import V185TrunkScan23Chunk0664

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3931753 : List Nat := [1, 2, 1, 1, 1, 4, 5, 1, 2, 1, 4]
def baseStart_3931753 : Nat := 118140960795 + 3931753 * 2 ^ 59
def prefixEnd_3931753 : Nat := 4983230072969 + 3 ^ 40 * 3931753 * 2
def baseEnd_3931753 : Nat := 2018879103757060732005703

theorem tailTrace_3931753 : CollatzResearch.WordTrace tailWord_3931753 prefixEnd_3931753 2018879103757060732005703 := by
  unfold tailWord_3931753
  simp only [CollatzResearch.WordTrace]
  refine ⟨143402812924937845797463913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95601875283291897198309275 143402812924937845797463913)
  ·
    refine ⟨107552109693703384348097935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143402812924937845797463913 107552109693703384348097935)
    ·
      refine ⟨161328164540555076522146903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107552109693703384348097935 161328164540555076522146903)
      ·
        refine ⟨241992246810832614783220355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161328164540555076522146903 241992246810832614783220355)
        ·
          refine ⟨362988370216248922174830533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241992246810832614783220355 362988370216248922174830533)
          ·
            refine ⟨68060319415546672907780725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 362988370216248922174830533 68060319415546672907780725)
            ·
              refine ⟨6380654945207500585104443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 68060319415546672907780725 6380654945207500585104443)
              ·
                refine ⟨9570982417811250877656665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6380654945207500585104443 9570982417811250877656665)
                ·
                  refine ⟨7178236813358438158242499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9570982417811250877656665 7178236813358438158242499)
                  ·
                    refine ⟨10767355220037657237363749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7178236813358438158242499 10767355220037657237363749)
                    ·
                      refine ⟨2018879103757060732005703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10767355220037657237363749 2018879103757060732005703)
                      ·
                        rfl

theorem cell23_3931753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 5, 1, 2, 1, 4].length) (baseStart_3931753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3931753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3931753 prefixEnd_3931753 := by exact prefixLift 3931753
  have htrace : WordTrace (prefixWord ++ tailWord_3931753) baseStart_3931753 baseEnd_3931753 := by
    simpa [prefixWord, tailWord_3931753, baseEnd_3931753] using wordTrace_append hprefix tailTrace_3931753
  have hstable : (prefixWord ++ tailWord_3931753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3931753).length < 2 ^ (prefixWord ++ tailWord_3931753).sum := by decide
  have hdescent : baseEnd_3931753 < baseStart_3931753 := by decide
  rcases family_descends (prefixWord ++ tailWord_3931753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3931776 : List Nat := [2, 1, 1, 2, 1, 4, 3, 1, 8]
def baseStart_3931776 : Nat := 118140960795 + 3931776 * 2 ^ 59
def prefixEnd_3931776 : Nat := 4983230072969 + 3 ^ 40 * 3931776 * 2
def baseEnd_3931776 : Nat := 224321212645790460224233

theorem tailTrace_3931776 : CollatzResearch.WordTrace tailWord_3931776 prefixEnd_3931776 224321212645790460224233 := by
  unfold tailWord_3931776
  simp only [CollatzResearch.WordTrace]
  refine ⟨71701825901927260362775591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95602434535903013817034121 71701825901927260362775591)
  ·
    refine ⟨107552738852890890544163387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71701825901927260362775591 107552738852890890544163387)
    ·
      refine ⟨161329108279336335816245081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107552738852890890544163387 161329108279336335816245081)
      ·
        refine ⟨120996831209502251862183811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161329108279336335816245081 120996831209502251862183811)
        ·
          refine ⟨181495246814253377793275717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120996831209502251862183811 181495246814253377793275717)
          ·
            refine ⟨34030358777672508336239197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 181495246814253377793275717 34030358777672508336239197)
            ·
              refine ⟨12761384541627190626089699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34030358777672508336239197 12761384541627190626089699)
              ·
                refine ⟨19142076812440785939134549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12761384541627190626089699 19142076812440785939134549)
                ·
                  refine ⟨224321212645790460224233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19142076812440785939134549 224321212645790460224233)
                  ·
                    rfl

theorem cell23_3931776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3, 1, 8].length) (baseStart_3931776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3931776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3931776 prefixEnd_3931776 := by exact prefixLift 3931776
  have htrace : WordTrace (prefixWord ++ tailWord_3931776) baseStart_3931776 baseEnd_3931776 := by
    simpa [prefixWord, tailWord_3931776, baseEnd_3931776] using wordTrace_append hprefix tailTrace_3931776
  have hstable : (prefixWord ++ tailWord_3931776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3931776).length < 2 ^ (prefixWord ++ tailWord_3931776).sum := by decide
  have hdescent : baseEnd_3931776 < baseStart_3931776 := by decide
  rcases family_descends (prefixWord ++ tailWord_3931776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3931823 : List Nat := [1, 1, 2, 1, 2, 4, 1, 5, 1, 5]
def baseStart_3931823 : Nat := 118140960795 + 3931823 * 2 ^ 59
def prefixEnd_3931823 : Nat := 4983230072969 + 3 ^ 40 * 3931823 * 2
def baseEnd_3931823 : Nat := 672971682467625152710127

theorem tailTrace_3931823 : CollatzResearch.WordTrace tailWord_3931823 prefixEnd_3931823 672971682467625152710127 := by
  unfold tailWord_3931823
  simp only [CollatzResearch.WordTrace]
  refine ⟨143405366034684247752512123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95603577356456165168341415 143405366034684247752512123)
  ·
    refine ⟨215108049052026371628768185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143405366034684247752512123 215108049052026371628768185)
    ·
      refine ⟨161331036789019778721576139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215108049052026371628768185 161331036789019778721576139)
      ·
        refine ⟨241996555183529668082364209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161331036789019778721576139 241996555183529668082364209)
        ·
          refine ⟨181497416387647251061773157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 241996555183529668082364209 181497416387647251061773157)
          ·
            refine ⟨34030765572683859574082467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 181497416387647251061773157 34030765572683859574082467)
            ·
              refine ⟨51046148359025789361123701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34030765572683859574082467 51046148359025789361123701)
              ·
                refine ⟨4785576408658667752605347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51046148359025789361123701 4785576408658667752605347)
                ·
                  refine ⟨7178364612988001628908021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4785576408658667752605347 7178364612988001628908021)
                  ·
                    refine ⟨672971682467625152710127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7178364612988001628908021 672971682467625152710127)
                    ·
                      rfl

theorem cell23_3931823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 5, 1, 5].length) (baseStart_3931823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3931823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3931823 prefixEnd_3931823 := by exact prefixLift 3931823
  have htrace : WordTrace (prefixWord ++ tailWord_3931823) baseStart_3931823 baseEnd_3931823 := by
    simpa [prefixWord, tailWord_3931823, baseEnd_3931823] using wordTrace_append hprefix tailTrace_3931823
  have hstable : (prefixWord ++ tailWord_3931823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3931823).length < 2 ^ (prefixWord ++ tailWord_3931823).sum := by decide
  have hdescent : baseEnd_3931823 < baseStart_3931823 := by decide
  rcases family_descends (prefixWord ++ tailWord_3931823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3931877 : List Nat := [1, 3, 1, 4, 1, 1, 5, 1, 1, 1, 4]
def baseStart_3931877 : Nat := 118140960795 + 3931877 * 2 ^ 59
def prefixEnd_3931877 : Nat := 4983230072969 + 3 ^ 40 * 3931877 * 2
def baseEnd_3931877 : Nat := 2018942775358218246855133

theorem tailTrace_3931877 : CollatzResearch.WordTrace tailWord_3931877 prefixEnd_3931877 2018942775358218246855133 := by
  unfold tailWord_3931877
  simp only [CollatzResearch.WordTrace]
  refine ⟨143407335576488614974977885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95604890384325743316651923 143407335576488614974977885)
  ·
    refine ⟨53777750841183230615616707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143407335576488614974977885 53777750841183230615616707)
    ·
      refine ⟨80666626261774845923425061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53777750841183230615616707 80666626261774845923425061)
      ·
        refine ⟨15124992424082783610642199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80666626261774845923425061 15124992424082783610642199)
        ·
          refine ⟨22687488636124175415963299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15124992424082783610642199 22687488636124175415963299)
          ·
            refine ⟨34031232954186263123944949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22687488636124175415963299 34031232954186263123944949)
            ·
              refine ⟨3190428089454962167869839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34031232954186263123944949 3190428089454962167869839)
              ·
                refine ⟨4785642134182443251804759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3190428089454962167869839 4785642134182443251804759)
                ·
                  refine ⟨7178463201273664877707139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4785642134182443251804759 7178463201273664877707139)
                  ·
                    refine ⟨10767694801910497316560709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7178463201273664877707139 10767694801910497316560709)
                    ·
                      refine ⟨2018942775358218246855133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10767694801910497316560709 2018942775358218246855133)
                      ·
                        rfl

theorem cell23_3931877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 5, 1, 1, 1, 4].length) (baseStart_3931877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3931877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3931877 prefixEnd_3931877 := by exact prefixLift 3931877
  have htrace : WordTrace (prefixWord ++ tailWord_3931877) baseStart_3931877 baseEnd_3931877 := by
    simpa [prefixWord, tailWord_3931877, baseEnd_3931877] using wordTrace_append hprefix tailTrace_3931877
  have hstable : (prefixWord ++ tailWord_3931877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3931877).length < 2 ^ (prefixWord ++ tailWord_3931877).sum := by decide
  have hdescent : baseEnd_3931877 < baseStart_3931877 := by decide
  rcases family_descends (prefixWord ++ tailWord_3931877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3931880 : List Nat := [2, 1, 4, 1, 3, 1, 3, 1, 1, 1, 5]
def baseStart_3931880 : Nat := 118140960795 + 3931880 * 2 ^ 59
def prefixEnd_3931880 : Nat := 4983230072969 + 3 ^ 40 * 3931880 * 2
def baseEnd_3931880 : Nat := 2018944315800181735117619

theorem tailTrace_3931880 : CollatzResearch.WordTrace tailWord_3931880 prefixEnd_3931880 2018944315800181735117619 := by
  unfold tailWord_3931880
  simp only [CollatzResearch.WordTrace]
  refine ⟨71703722497738873243668547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95604963330318497658224729 71703722497738873243668547)
  ·
    refine ⟨107555583746608309865502821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71703722497738873243668547 107555583746608309865502821)
    ·
      refine ⟨20166671952489058099781779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 107555583746608309865502821 20166671952489058099781779)
      ·
        refine ⟨30250007928733587149672669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20166671952489058099781779 30250007928733587149672669)
        ·
          refine ⟨11343752973275095181127251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30250007928733587149672669 11343752973275095181127251)
          ·
            refine ⟨17015629459912642771690877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11343752973275095181127251 17015629459912642771690877)
            ·
              refine ⟨6380861047467241039384079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17015629459912642771690877 6380861047467241039384079)
              ·
                refine ⟨9571291571200861559076119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6380861047467241039384079 9571291571200861559076119)
                ·
                  refine ⟨14356937356801292338614179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9571291571200861559076119 14356937356801292338614179)
                  ·
                    refine ⟨21535406035201938507921269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14356937356801292338614179 21535406035201938507921269)
                    ·
                      refine ⟨2018944315800181735117619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21535406035201938507921269 2018944315800181735117619)
                      ·
                        rfl

theorem cell23_3931880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 3, 1, 1, 1, 5].length) (baseStart_3931880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3931880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3931880 prefixEnd_3931880 := by exact prefixLift 3931880
  have htrace : WordTrace (prefixWord ++ tailWord_3931880) baseStart_3931880 baseEnd_3931880 := by
    simpa [prefixWord, tailWord_3931880, baseEnd_3931880] using wordTrace_append hprefix tailTrace_3931880
  have hstable : (prefixWord ++ tailWord_3931880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3931880).length < 2 ^ (prefixWord ++ tailWord_3931880).sum := by decide
  have hdescent : baseEnd_3931880 < baseStart_3931880 := by decide
  rcases family_descends (prefixWord ++ tailWord_3931880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3931944 : List Nat := [2, 1, 5, 1, 1, 2, 3, 2, 2, 1, 3]
def baseStart_3931944 : Nat := 118140960795 + 3931944 * 2 ^ 59
def prefixEnd_3931944 : Nat := 4983230072969 + 3 ^ 40 * 3931944 * 2
def baseEnd_3931944 : Nat := 2018977178562069484717325

theorem tailTrace_3931944 : CollatzResearch.WordTrace tailWord_3931944 prefixEnd_3931944 2018977178562069484717325 := by
  unfold tailWord_3931944
  simp only [CollatzResearch.WordTrace]
  refine ⟨71704889633622942708833443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95606519511497256945111257 71704889633622942708833443)
  ·
    refine ⟨107557334450434414063250165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71704889633622942708833443 107557334450434414063250165)
    ·
      refine ⟨10083500104728226318429703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 107557334450434414063250165 10083500104728226318429703)
      ·
        refine ⟨15125250157092339477644555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10083500104728226318429703 15125250157092339477644555)
        ·
          refine ⟨22687875235638509216466833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15125250157092339477644555 22687875235638509216466833)
          ·
            refine ⟨17015906426728881912350125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22687875235638509216466833 17015906426728881912350125)
            ·
              refine ⟨6380964910023330717131297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17015906426728881912350125 6380964910023330717131297)
              ·
                refine ⟨4785723682517498037848473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6380964910023330717131297 4785723682517498037848473)
                ·
                  refine ⟨3589292761888123528386355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4785723682517498037848473 3589292761888123528386355)
                  ·
                    refine ⟨5383939142832185292579533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3589292761888123528386355 5383939142832185292579533)
                    ·
                      refine ⟨2018977178562069484717325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5383939142832185292579533 2018977178562069484717325)
                      ·
                        rfl

theorem cell23_3931944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 3, 2, 2, 1, 3].length) (baseStart_3931944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3931944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3931944 prefixEnd_3931944 := by exact prefixLift 3931944
  have htrace : WordTrace (prefixWord ++ tailWord_3931944) baseStart_3931944 baseEnd_3931944 := by
    simpa [prefixWord, tailWord_3931944, baseEnd_3931944] using wordTrace_append hprefix tailTrace_3931944
  have hstable : (prefixWord ++ tailWord_3931944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3931944).length < 2 ^ (prefixWord ++ tailWord_3931944).sum := by decide
  have hdescent : baseEnd_3931944 < baseStart_3931944 := by decide
  rcases family_descends (prefixWord ++ tailWord_3931944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3931961 : List Nat := [1, 2, 1, 7, 2, 1, 1, 1, 1, 3, 3]
def baseStart_3931961 : Nat := 118140960795 + 3931961 * 2 ^ 59
def prefixEnd_3931961 : Nat := 4983230072969 + 3 ^ 40 * 3931961 * 2
def baseEnd_3931961 : Nat := 2018985907733195918204747

theorem tailTrace_3931961 : CollatzResearch.WordTrace tailWord_3931961 prefixEnd_3931961 2018985907733195918204747 := by
  unfold tailWord_3931961
  simp only [CollatzResearch.WordTrace]
  refine ⟨143410399308184297321035737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95606932872122864880690491 143410399308184297321035737)
  ·
    refine ⟨107557799481138222990776803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143410399308184297321035737 107557799481138222990776803)
    ·
      refine ⟨161336699221707334486165205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107557799481138222990776803 161336699221707334486165205)
      ·
        refine ⟨3781328888008765652019497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 161336699221707334486165205 3781328888008765652019497)
        ·
          refine ⟨2835996666006574239014623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3781328888008765652019497 2835996666006574239014623)
          ·
            refine ⟨4253994999009861358521935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2835996666006574239014623 4253994999009861358521935)
            ·
              refine ⟨6380992498514792037782903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4253994999009861358521935 6380992498514792037782903)
              ·
                refine ⟨9571488747772188056674355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6380992498514792037782903 9571488747772188056674355)
                ·
                  refine ⟨14357233121658282085011533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9571488747772188056674355 14357233121658282085011533)
                  ·
                    refine ⟨5383962420621855781879325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14357233121658282085011533 5383962420621855781879325)
                    ·
                      refine ⟨2018985907733195918204747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5383962420621855781879325 2018985907733195918204747)
                      ·
                        rfl

theorem cell23_3931961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 1, 1, 1, 3, 3].length) (baseStart_3931961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3931961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3931961 prefixEnd_3931961 := by exact prefixLift 3931961
  have htrace : WordTrace (prefixWord ++ tailWord_3931961) baseStart_3931961 baseEnd_3931961 := by
    simpa [prefixWord, tailWord_3931961, baseEnd_3931961] using wordTrace_append hprefix tailTrace_3931961
  have hstable : (prefixWord ++ tailWord_3931961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3931961).length < 2 ^ (prefixWord ++ tailWord_3931961).sum := by decide
  have hdescent : baseEnd_3931961 < baseStart_3931961 := by decide
  rcases family_descends (prefixWord ++ tailWord_3931961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3931973 : List Nat := [1, 3, 1, 1, 1, 2, 3, 4, 7]
def baseStart_3931973 : Nat := 118140960795 + 3931973 * 2 ^ 59
def prefixEnd_3931973 : Nat := 4983230072969 + 3 ^ 40 * 3931973 * 2
def baseEnd_3931973 : Nat := 224332452166783319028299

theorem tailTrace_3931973 : CollatzResearch.WordTrace tailWord_3931973 prefixEnd_3931973 224332452166783319028299 := by
  unfold tailWord_3931973
  simp only [CollatzResearch.WordTrace]
  refine ⟨143410836984140823370472573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95607224656093882246981715 143410836984140823370472573)
  ·
    refine ⟨53779063869052808763927215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143410836984140823370472573 53779063869052808763927215)
    ·
      refine ⟨80668595803579213145890823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53779063869052808763927215 80668595803579213145890823)
      ·
        refine ⟨121002893705368819718836235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80668595803579213145890823 121002893705368819718836235)
        ·
          refine ⟨181504340558053229578254353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121002893705368819718836235 181504340558053229578254353)
          ·
            refine ⟨136128255418539922183690765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 181504340558053229578254353 136128255418539922183690765)
            ·
              refine ⟨51048095781952470818884037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 136128255418539922183690765 51048095781952470818884037)
              ·
                refine ⟨9571517959116088278540757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51048095781952470818884037 9571517959116088278540757)
                ·
                  refine ⟨224332452166783319028299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9571517959116088278540757 224332452166783319028299)
                  ·
                    rfl

theorem cell23_3931973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 4, 7].length) (baseStart_3931973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3931973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3931973 prefixEnd_3931973 := by exact prefixLift 3931973
  have htrace : WordTrace (prefixWord ++ tailWord_3931973) baseStart_3931973 baseEnd_3931973 := by
    simpa [prefixWord, tailWord_3931973, baseEnd_3931973] using wordTrace_append hprefix tailTrace_3931973
  have hstable : (prefixWord ++ tailWord_3931973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3931973).length < 2 ^ (prefixWord ++ tailWord_3931973).sum := by decide
  have hdescent : baseEnd_3931973 < baseStart_3931973 := by decide
  rcases family_descends (prefixWord ++ tailWord_3931973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3932090 : List Nat := [3, 1, 1, 1, 2, 1, 2, 1, 1, 7, 3]
def baseStart_3932090 : Nat := 118140960795 + 3932090 * 2 ^ 59
def prefixEnd_3932090 : Nat := 4983230072969 + 3 ^ 40 * 3932090 * 2
def baseEnd_3932090 : Nat := 2019052146737625913491653

theorem tailTrace_3932090 : CollatzResearch.WordTrace tailWord_3932090 prefixEnd_3932090 2019052146737625913491653 := by
  unfold tailWord_3932090
  simp only [CollatzResearch.WordTrace]
  refine ⟨35853776081179238088120431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95610069549811301568321149 35853776081179238088120431)
  ·
    refine ⟨53780664121768857132180647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35853776081179238088120431 53780664121768857132180647)
    ·
      refine ⟨80670996182653285698270971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53780664121768857132180647 80670996182653285698270971)
      ·
        refine ⟨121006494273979928547406457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80670996182653285698270971 121006494273979928547406457)
        ·
          refine ⟨90754870705484946410554843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121006494273979928547406457 90754870705484946410554843)
          ·
            refine ⟨136132306058227419615832265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90754870705484946410554843 136132306058227419615832265)
            ·
              refine ⟨102099229543670564711874199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136132306058227419615832265 102099229543670564711874199)
              ·
                refine ⟨153148844315505847067811299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102099229543670564711874199 153148844315505847067811299)
                ·
                  refine ⟨229723266473258770601716949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 153148844315505847067811299 229723266473258770601716949)
                  ·
                    refine ⟨5384139057967002435977741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 229723266473258770601716949 5384139057967002435977741)
                    ·
                      refine ⟨2019052146737625913491653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5384139057967002435977741 2019052146737625913491653)
                      ·
                        rfl

theorem cell23_3932090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 1, 1, 7, 3].length) (baseStart_3932090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3932090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3932090 prefixEnd_3932090 := by exact prefixLift 3932090
  have htrace : WordTrace (prefixWord ++ tailWord_3932090) baseStart_3932090 baseEnd_3932090 := by
    simpa [prefixWord, tailWord_3932090, baseEnd_3932090] using wordTrace_append hprefix tailTrace_3932090
  have hstable : (prefixWord ++ tailWord_3932090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3932090).length < 2 ^ (prefixWord ++ tailWord_3932090).sum := by decide
  have hdescent : baseEnd_3932090 < baseStart_3932090 := by decide
  rcases family_descends (prefixWord ++ tailWord_3932090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3932094 : List Nat := [4, 2, 1, 1, 1, 3, 3, 1, 2, 2, 3]
def baseStart_3932094 : Nat := 118140960795 + 3932094 * 2 ^ 59
def prefixEnd_3932094 : Nat := 4983230072969 + 3 ^ 40 * 3932094 * 2
def baseEnd_3932094 : Nat := 2019054200660243897841635

theorem tailTrace_3932094 : CollatzResearch.WordTrace tailWord_3932094 prefixEnd_3932094 2019054200660243897841635 := by
  unfold tailWord_3932094
  simp only [CollatzResearch.WordTrace]
  refine ⟨17926906277087807629453417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95610166811134974023751557 17926906277087807629453417)
  ·
    refine ⟨13445179707815855722090063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17926906277087807629453417 13445179707815855722090063)
    ·
      refine ⟨20167769561723783583135095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13445179707815855722090063 20167769561723783583135095)
      ·
        refine ⟨30251654342585675374702643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20167769561723783583135095 30251654342585675374702643)
        ·
          refine ⟨45377481513878513062053965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30251654342585675374702643 45377481513878513062053965)
          ·
            refine ⟨17016555567704442398270237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45377481513878513062053965 17016555567704442398270237)
            ·
              refine ⟨6381208337889165899351339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17016555567704442398270237 6381208337889165899351339)
              ·
                refine ⟨9571812506833748849027009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6381208337889165899351339 9571812506833748849027009)
                ·
                  refine ⟨7178859380125311636770257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9571812506833748849027009 7178859380125311636770257)
                  ·
                    refine ⟨5384144535093983727577693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7178859380125311636770257 5384144535093983727577693)
                    ·
                      refine ⟨2019054200660243897841635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5384144535093983727577693 2019054200660243897841635)
                      ·
                        rfl

theorem cell23_3932094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 3, 1, 2, 2, 3].length) (baseStart_3932094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3932094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3932094 prefixEnd_3932094 := by exact prefixLift 3932094
  have htrace : WordTrace (prefixWord ++ tailWord_3932094) baseStart_3932094 baseEnd_3932094 := by
    simpa [prefixWord, tailWord_3932094, baseEnd_3932094] using wordTrace_append hprefix tailTrace_3932094
  have hstable : (prefixWord ++ tailWord_3932094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3932094).length < 2 ^ (prefixWord ++ tailWord_3932094).sum := by decide
  have hdescent : baseEnd_3932094 < baseStart_3932094 := by decide
  rcases family_descends (prefixWord ++ tailWord_3932094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3932107 : List Nat := [1, 1, 1, 1, 3, 4, 1, 2, 5, 1, 3]
def baseStart_3932107 : Nat := 118140960795 + 3932107 * 2 ^ 59
def prefixEnd_3932107 : Nat := 4983230072969 + 3 ^ 40 * 3932107 * 2
def baseEnd_3932107 : Nat := 2019060875908752346979075

theorem tailTrace_3932107 : CollatzResearch.WordTrace tailWord_3932107 prefixEnd_3932107 2019060875908752346979075 := by
  unfold tailWord_3932107
  simp only [CollatzResearch.WordTrace]
  refine ⟨143415724365655364255850575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95610482910436909503900383 143415724365655364255850575)
  ·
    refine ⟨215123586548483046383775863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143415724365655364255850575 215123586548483046383775863)
    ·
      refine ⟨322685379822724569575663795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215123586548483046383775863 322685379822724569575663795)
      ·
        refine ⟨484028069734086854363495693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 322685379822724569575663795 484028069734086854363495693)
        ·
          refine ⟨181510526150282570386310885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 484028069734086854363495693 181510526150282570386310885)
          ·
            refine ⟨34033223653177981947433291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 181510526150282570386310885 34033223653177981947433291)
            ·
              refine ⟨51049835479766972921149937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34033223653177981947433291 51049835479766972921149937)
              ·
                refine ⟨38287376609825229690862453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51049835479766972921149937 38287376609825229690862453)
                ·
                  refine ⟨3589441557171115283518355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38287376609825229690862453 3589441557171115283518355)
                  ·
                    refine ⟨5384162335756672925277533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3589441557171115283518355 5384162335756672925277533)
                    ·
                      refine ⟨2019060875908752346979075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5384162335756672925277533 2019060875908752346979075)
                      ·
                        rfl

theorem cell23_3932107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 2, 5, 1, 3].length) (baseStart_3932107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3932107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3932107 prefixEnd_3932107 := by exact prefixLift 3932107
  have htrace : WordTrace (prefixWord ++ tailWord_3932107) baseStart_3932107 baseEnd_3932107 := by
    simpa [prefixWord, tailWord_3932107, baseEnd_3932107] using wordTrace_append hprefix tailTrace_3932107
  have hstable : (prefixWord ++ tailWord_3932107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3932107).length < 2 ^ (prefixWord ++ tailWord_3932107).sum := by decide
  have hdescent : baseEnd_3932107 < baseStart_3932107 := by decide
  rcases family_descends (prefixWord ++ tailWord_3932107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3932157 : List Nat := [1, 4, 1, 1, 1, 2, 3, 2, 4, 4]
def baseStart_3932157 : Nat := 118140960795 + 3932157 * 2 ^ 59
def prefixEnd_3932157 : Nat := 4983230072969 + 3 ^ 40 * 3932157 * 2
def baseEnd_3932157 : Nat := 673028849980492383784615

theorem tailTrace_3932157 : CollatzResearch.WordTrace tailWord_3932157 prefixEnd_3932157 673028849980492383784615 := by
  unfold tailWord_3932157
  simp only [CollatzResearch.WordTrace]
  refine ⟨143417548015474222795170725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95611698676982815196780483 143417548015474222795170725)
  ·
    refine ⟨26890790252901416774094511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 143417548015474222795170725 26890790252901416774094511)
    ·
      refine ⟨40336185379352125161141767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26890790252901416774094511 40336185379352125161141767)
      ·
        refine ⟨60504278069028187741712651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40336185379352125161141767 60504278069028187741712651)
        ·
          refine ⟨90756417103542281612568977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60504278069028187741712651 90756417103542281612568977)
          ·
            refine ⟨68067312827656711209426733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90756417103542281612568977 68067312827656711209426733)
            ·
              refine ⟨25525242310371266703535025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68067312827656711209426733 25525242310371266703535025)
              ·
                refine ⟨19143931732778450027651269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25525242310371266703535025 19143931732778450027651269)
                ·
                  refine ⟨3589487199895959380184613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19143931732778450027651269 3589487199895959380184613)
                  ·
                    refine ⟨673028849980492383784615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3589487199895959380184613 673028849980492383784615)
                    ·
                      rfl

theorem cell23_3932157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 2, 4, 4].length) (baseStart_3932157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3932157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3932157 prefixEnd_3932157 := by exact prefixLift 3932157
  have htrace : WordTrace (prefixWord ++ tailWord_3932157) baseStart_3932157 baseEnd_3932157 := by
    simpa [prefixWord, tailWord_3932157, baseEnd_3932157] using wordTrace_append hprefix tailTrace_3932157
  have hstable : (prefixWord ++ tailWord_3932157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3932157).length < 2 ^ (prefixWord ++ tailWord_3932157).sum := by decide
  have hdescent : baseEnd_3932157 < baseStart_3932157 := by decide
  rcases family_descends (prefixWord ++ tailWord_3932157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3932167 : List Nat := [1, 1, 4, 3, 1, 2, 1, 3, 1, 1, 5]
def baseStart_3932167 : Nat := 118140960795 + 3932167 * 2 ^ 59
def prefixEnd_3932167 : Nat := 4983230072969 + 3 ^ 40 * 3932167 * 2
def baseEnd_3932167 : Nat := 2019091684748022112228799

theorem tailTrace_3932167 : CollatzResearch.WordTrace tailWord_3932167 prefixEnd_3932167 2019091684748022112228799 := by
  unfold tailWord_3932167
  simp only [CollatzResearch.WordTrace]
  refine ⟨143417912745437994503034755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95611941830291996335356503 143417912745437994503034755)
  ·
    refine ⟨215126869118156991754552133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143417912745437994503034755 215126869118156991754552133)
    ·
      refine ⟨40336287959654435953978525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 215126869118156991754552133 40336287959654435953978525)
      ·
        refine ⟨15126107984870413482741947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40336287959654435953978525 15126107984870413482741947)
        ·
          refine ⟨22689161977305620224112921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15126107984870413482741947 22689161977305620224112921)
          ·
            refine ⟨17016871482979215168084691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22689161977305620224112921 17016871482979215168084691)
            ·
              refine ⟨25525307224468822752127037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17016871482979215168084691 25525307224468822752127037)
              ·
                refine ⟨9571990209175808532047639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25525307224468822752127037 9571990209175808532047639)
                ·
                  refine ⟨14357985313763712798071459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9571990209175808532047639 14357985313763712798071459)
                  ·
                    refine ⟨21536977970645569197107189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14357985313763712798071459 21536977970645569197107189)
                    ·
                      refine ⟨2019091684748022112228799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21536977970645569197107189 2019091684748022112228799)
                      ·
                        rfl

theorem cell23_3932167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 3, 1, 1, 5].length) (baseStart_3932167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3932167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3932167 prefixEnd_3932167 := by exact prefixLift 3932167
  have htrace : WordTrace (prefixWord ++ tailWord_3932167) baseStart_3932167 baseEnd_3932167 := by
    simpa [prefixWord, tailWord_3932167, baseEnd_3932167] using wordTrace_append hprefix tailTrace_3932167
  have hstable : (prefixWord ++ tailWord_3932167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3932167).length < 2 ^ (prefixWord ++ tailWord_3932167).sum := by decide
  have hdescent : baseEnd_3932167 < baseStart_3932167 := by decide
  rcases family_descends (prefixWord ++ tailWord_3932167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3932174 : List Nat := [4, 1, 1, 2, 2, 1, 2, 4, 2, 4]
def baseStart_3932174 : Nat := 118140960795 + 3932174 * 2 ^ 59
def prefixEnd_3932174 : Nat := 4983230072969 + 3 ^ 40 * 3932174 * 2
def baseEnd_3932174 : Nat := 673031759704201194947089

theorem tailTrace_3932174 : CollatzResearch.WordTrace tailWord_3932174 prefixEnd_3932174 673031759704201194947089 := by
  unfold tailWord_3932174
  simp only [CollatzResearch.WordTrace]
  refine ⟨17927271007051579337317447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95612112037608423132359717 17927271007051579337317447)
  ·
    refine ⟨26890906510577369005976171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17927271007051579337317447 26890906510577369005976171)
    ·
      refine ⟨40336359765866053508964257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26890906510577369005976171 40336359765866053508964257)
      ·
        refine ⟨30252269824399540131723193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40336359765866053508964257 30252269824399540131723193)
        ·
          refine ⟨22689202368299655098792395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30252269824399540131723193 22689202368299655098792395)
          ·
            refine ⟨34033803552449482648188593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22689202368299655098792395 34033803552449482648188593)
            ·
              refine ⟨25525352664337111986141445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34033803552449482648188593 25525352664337111986141445)
              ·
                refine ⟨4786003624563208497401521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25525352664337111986141445 4786003624563208497401521)
                ·
                  refine ⟨3589502718422406373051141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4786003624563208497401521 3589502718422406373051141)
                  ·
                    refine ⟨673031759704201194947089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3589502718422406373051141 673031759704201194947089)
                    ·
                      rfl

theorem cell23_3932174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 4, 2, 4].length) (baseStart_3932174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3932174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3932174 prefixEnd_3932174 := by exact prefixLift 3932174
  have htrace : WordTrace (prefixWord ++ tailWord_3932174) baseStart_3932174 baseEnd_3932174 := by
    simpa [prefixWord, tailWord_3932174, baseEnd_3932174] using wordTrace_append hprefix tailTrace_3932174
  have hstable : (prefixWord ++ tailWord_3932174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3932174).length < 2 ^ (prefixWord ++ tailWord_3932174).sum := by decide
  have hdescent : baseEnd_3932174 < baseStart_3932174 := by decide
  rcases family_descends (prefixWord ++ tailWord_3932174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3932231 : List Nat := [1, 1, 4, 1, 3, 1, 4, 2, 2, 1, 3]
def baseStart_3932231 : Nat := 118140960795 + 3932231 * 2 ^ 59
def prefixEnd_3932231 : Nat := 4983230072969 + 3 ^ 40 * 3932231 * 2
def baseEnd_3932231 : Nat := 2019124547509909861828505

theorem tailTrace_3932231 : CollatzResearch.WordTrace tailWord_3932231 prefixEnd_3932231 2019124547509909861828505 := by
  unfold tailWord_3932231
  simp only [CollatzResearch.WordTrace]
  refine ⟨143420247017206133433364547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95613498011470755622243031 143420247017206133433364547)
  ·
    refine ⟨215130370525809200150046821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143420247017206133433364547 215130370525809200150046821)
    ·
      refine ⟨40336944473589225028133779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 215130370525809200150046821 40336944473589225028133779)
      ·
        refine ⟨60505416710383837542200669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40336944473589225028133779 60505416710383837542200669)
        ·
          refine ⟨22689531266393939078325251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60505416710383837542200669 22689531266393939078325251)
          ·
            refine ⟨34034296899590908617487877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22689531266393939078325251 34034296899590908617487877)
            ·
              refine ⟨6381430668673295365778977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34034296899590908617487877 6381430668673295365778977)
              ·
                refine ⟨4786073001504971524334233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6381430668673295365778977 4786073001504971524334233)
                ·
                  refine ⟨3589554751128728643250675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4786073001504971524334233 3589554751128728643250675)
                  ·
                    refine ⟨5384332126693092964876013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3589554751128728643250675 5384332126693092964876013)
                    ·
                      refine ⟨2019124547509909861828505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5384332126693092964876013 2019124547509909861828505)
                      ·
                        rfl

theorem cell23_3932231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 4, 2, 2, 1, 3].length) (baseStart_3932231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3932231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3932231 prefixEnd_3932231 := by exact prefixLift 3932231
  have htrace : WordTrace (prefixWord ++ tailWord_3932231) baseStart_3932231 baseEnd_3932231 := by
    simpa [prefixWord, tailWord_3932231, baseEnd_3932231] using wordTrace_append hprefix tailTrace_3932231
  have hstable : (prefixWord ++ tailWord_3932231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3932231).length < 2 ^ (prefixWord ++ tailWord_3932231).sum := by decide
  have hdescent : baseEnd_3932231 < baseStart_3932231 := by decide
  rcases family_descends (prefixWord ++ tailWord_3932231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3932257 : List Nat := [1, 2, 3, 1, 1, 2, 1, 1, 4, 4, 3]
def baseStart_3932257 : Nat := 118140960795 + 3932257 * 2 ^ 59
def prefixEnd_3932257 : Nat := 4983230072969 + 3 ^ 40 * 3932257 * 2
def baseEnd_3932257 : Nat := 2019137898006926760103385

theorem tailTrace_3932257 : CollatzResearch.WordTrace tailWord_3932257 prefixEnd_3932257 2019137898006926760103385 := by
  unfold tailWord_3932257
  simp only [CollatzResearch.WordTrace]
  refine ⟨143421195315111939873811025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95614130210074626582540683 143421195315111939873811025)
  ·
    refine ⟨107565896486333954905358269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143421195315111939873811025 107565896486333954905358269)
    ·
      refine ⟨40337211182375233089509351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107565896486333954905358269 40337211182375233089509351)
      ·
        refine ⟨60505816773562849634264027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40337211182375233089509351 60505816773562849634264027)
        ·
          refine ⟨90758725160344274451396041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60505816773562849634264027 90758725160344274451396041)
          ·
            refine ⟨68069043870258205838547031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90758725160344274451396041 68069043870258205838547031)
            ·
              refine ⟨102103565805387308757820547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68069043870258205838547031 102103565805387308757820547)
              ·
                refine ⟨153155348708080963136730821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102103565805387308757820547 153155348708080963136730821)
                ·
                  refine ⟨28716627882765180588137029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 153155348708080963136730821 28716627882765180588137029)
                  ·
                    refine ⟨5384367728018471360275693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28716627882765180588137029 5384367728018471360275693)
                    ·
                      refine ⟨2019137898006926760103385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5384367728018471360275693 2019137898006926760103385)
                      ·
                        rfl

theorem cell23_3932257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 1, 4, 4, 3].length) (baseStart_3932257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3932257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3932257 prefixEnd_3932257 := by exact prefixLift 3932257
  have htrace : WordTrace (prefixWord ++ tailWord_3932257) baseStart_3932257 baseEnd_3932257 := by
    simpa [prefixWord, tailWord_3932257, baseEnd_3932257] using wordTrace_append hprefix tailTrace_3932257
  have hstable : (prefixWord ++ tailWord_3932257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3932257).length < 2 ^ (prefixWord ++ tailWord_3932257).sum := by decide
  have hdescent : baseEnd_3932257 < baseStart_3932257 := by decide
  rcases family_descends (prefixWord ++ tailWord_3932257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3932344 : List Nat := [2, 1, 2, 1, 2, 1, 5, 2, 2, 1, 4]
def baseStart_3932344 : Nat := 118140960795 + 3932344 * 2 ^ 59
def prefixEnd_3932344 : Nat := 4983230072969 + 3 ^ 40 * 3932344 * 2
def baseEnd_3932344 : Nat := 2019182570823867919715485

theorem tailTrace_3932344 : CollatzResearch.WordTrace tailWord_3932344 prefixEnd_3932344 2019182570823867919715485 := by
  unfold tailWord_3932344
  simp only [CollatzResearch.WordTrace]
  refine ⟨71712184232898376866114043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95616245643864502488152057 71712184232898376866114043)
  ·
    refine ⟨107568276349347565299171065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71712184232898376866114043 107568276349347565299171065)
    ·
      refine ⟨80676207262010673974378299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107568276349347565299171065 80676207262010673974378299)
      ·
        refine ⟨121014310893016010961567449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80676207262010673974378299 121014310893016010961567449)
        ·
          refine ⟨90760733169762008221175587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121014310893016010961567449 90760733169762008221175587)
          ·
            refine ⟨136141099754643012331763381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90760733169762008221175587 136141099754643012331763381)
            ·
              refine ⟨12763228101997782406102817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 136141099754643012331763381 12763228101997782406102817)
              ·
                refine ⟨9572421076498336804577113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12763228101997782406102817 9572421076498336804577113)
                ·
                  refine ⟨7179315807373752603432835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9572421076498336804577113 7179315807373752603432835)
                  ·
                    refine ⟨10768973711060628905149253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7179315807373752603432835 10768973711060628905149253)
                    ·
                      refine ⟨2019182570823867919715485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10768973711060628905149253 2019182570823867919715485)
                      ·
                        rfl

theorem cell23_3932344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5, 2, 2, 1, 4].length) (baseStart_3932344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3932344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3932344 prefixEnd_3932344 := by exact prefixLift 3932344
  have htrace : WordTrace (prefixWord ++ tailWord_3932344) baseStart_3932344 baseEnd_3932344 := by
    simpa [prefixWord, tailWord_3932344, baseEnd_3932344] using wordTrace_append hprefix tailTrace_3932344
  have hstable : (prefixWord ++ tailWord_3932344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3932344).length < 2 ^ (prefixWord ++ tailWord_3932344).sum := by decide
  have hdescent : baseEnd_3932344 < baseStart_3932344 := by decide
  rcases family_descends (prefixWord ++ tailWord_3932344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3932357 : List Nat := [1, 3, 1, 1, 1, 1, 4, 2, 2, 1, 6]
def baseStart_3932357 : Nat := 118140960795 + 3932357 * 2 ^ 59
def prefixEnd_3932357 : Nat := 4983230072969 + 3 ^ 40 * 3932357 * 2
def baseEnd_3932357 : Nat := 2019189246072376368852925

theorem tailTrace_3932357 : CollatzResearch.WordTrace tailWord_3932357 prefixEnd_3932357 2019189246072376368852925 := by
  unfold tailWord_3932357
  simp only [CollatzResearch.WordTrace]
  refine ⟨143424842614749656952451325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95616561743166437968300883 143424842614749656952451325)
  ·
    refine ⟨53784315980531121357169247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143424842614749656952451325 53784315980531121357169247)
    ·
      refine ⟨80676473970796682035753871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53784315980531121357169247 80676473970796682035753871)
      ·
        refine ⟨121014710956195023053630807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80676473970796682035753871 121014710956195023053630807)
        ·
          refine ⟨181522066434292534580446211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121014710956195023053630807 181522066434292534580446211)
          ·
            refine ⟨272283099651438801870669317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181522066434292534580446211 272283099651438801870669317)
            ·
              refine ⟨51053081184644775350750497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 272283099651438801870669317 51053081184644775350750497)
              ·
                refine ⟨38289810888483581513062873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51053081184644775350750497 38289810888483581513062873)
                ·
                  refine ⟨28717358166362686134797155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38289810888483581513062873 28717358166362686134797155)
                  ·
                    refine ⟨43076037249544029202195733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28717358166362686134797155 43076037249544029202195733)
                    ·
                      refine ⟨2019189246072376368852925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 43076037249544029202195733 2019189246072376368852925)
                      ·
                        rfl

theorem cell23_3932357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 2, 2, 1, 6].length) (baseStart_3932357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3932357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3932357 prefixEnd_3932357 := by exact prefixLift 3932357
  have htrace : WordTrace (prefixWord ++ tailWord_3932357) baseStart_3932357 baseEnd_3932357 := by
    simpa [prefixWord, tailWord_3932357, baseEnd_3932357] using wordTrace_append hprefix tailTrace_3932357
  have hstable : (prefixWord ++ tailWord_3932357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3932357).length < 2 ^ (prefixWord ++ tailWord_3932357).sum := by decide
  have hdescent : baseEnd_3932357 < baseStart_3932357 := by decide
  rcases family_descends (prefixWord ++ tailWord_3932357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3932407 : List Nat := [1, 1, 3, 1, 1, 1, 2, 1, 4, 1, 7]
def baseStart_3932407 : Nat := 118140960795 + 3932407 * 2 ^ 59
def prefixEnd_3932407 : Nat := 4983230072969 + 3 ^ 40 * 3932407 * 2
def baseEnd_3932407 : Nat := 2019214920105101173227695

theorem tailTrace_3932407 : CollatzResearch.WordTrace tailWord_3932407 prefixEnd_3932407 2019214920105101173227695 := by
  unfold tailWord_3932407
  simp only [CollatzResearch.WordTrace]
  refine ⟨143426666264568515491771475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95617777509712343661180983 143426666264568515491771475)
  ·
    refine ⟨215139999396852773237657213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143426666264568515491771475 215139999396852773237657213)
    ·
      refine ⟨80677499773819789964121455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 215139999396852773237657213 80677499773819789964121455)
      ·
        refine ⟨121016249660729684946182183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80677499773819789964121455 121016249660729684946182183)
        ·
          refine ⟨181524374491094527419273275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121016249660729684946182183 181524374491094527419273275)
          ·
            refine ⟨272286561736641791128909913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181524374491094527419273275 272286561736641791128909913)
            ·
              refine ⟨204214921302481343346682435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 272286561736641791128909913 204214921302481343346682435)
              ·
                refine ⟨306322381953722015020023653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 204214921302481343346682435 306322381953722015020023653)
                ·
                  refine ⟨57435446616322877816254435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 306322381953722015020023653 57435446616322877816254435)
                  ·
                    refine ⟨86153169924484316724381653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57435446616322877816254435 86153169924484316724381653)
                    ·
                      refine ⟨2019214920105101173227695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 86153169924484316724381653 2019214920105101173227695)
                      ·
                        rfl

theorem cell23_3932407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 4, 1, 7].length) (baseStart_3932407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3932407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3932407 prefixEnd_3932407 := by exact prefixLift 3932407
  have htrace : WordTrace (prefixWord ++ tailWord_3932407) baseStart_3932407 baseEnd_3932407 := by
    simpa [prefixWord, tailWord_3932407, baseEnd_3932407] using wordTrace_append hprefix tailTrace_3932407
  have hstable : (prefixWord ++ tailWord_3932407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3932407).length < 2 ^ (prefixWord ++ tailWord_3932407).sum := by decide
  have hdescent : baseEnd_3932407 < baseStart_3932407 := by decide
  rcases family_descends (prefixWord ++ tailWord_3932407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3932448 : List Nat := [2, 1, 1, 5, 2, 1, 4, 1, 1, 5]
def baseStart_3932448 : Nat := 118140960795 + 3932448 * 2 ^ 59
def prefixEnd_3932448 : Nat := 4983230072969 + 3 ^ 40 * 3932448 * 2
def baseEnd_3932448 : Nat := 673078657603978504271669

theorem tailTrace_3932448 : CollatzResearch.WordTrace tailWord_3932448 prefixEnd_3932448 673078657603978504271669 := by
  unfold tailWord_3932448
  simp only [CollatzResearch.WordTrace]
  refine ⟨71714080828709989747006999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95618774438279986329342665 71714080828709989747006999)
  ·
    refine ⟨107571121243064984620510499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71714080828709989747006999 107571121243064984620510499)
    ·
      refine ⟨161356681864597476930765749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107571121243064984620510499 161356681864597476930765749)
      ·
        refine ⟨15127188924806013462259289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 161356681864597476930765749 15127188924806013462259289)
        ·
          refine ⟨11345391693604510096694467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15127188924806013462259289 11345391693604510096694467)
          ·
            refine ⟨17018087540406765145041701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11345391693604510096694467 17018087540406765145041701)
            ·
              refine ⟨3190891413826268464695319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17018087540406765145041701 3190891413826268464695319)
              ·
                refine ⟨4786337120739402697042979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3190891413826268464695319 4786337120739402697042979)
                ·
                  refine ⟨7179505681109104045564469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4786337120739402697042979 7179505681109104045564469)
                  ·
                    refine ⟨673078657603978504271669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7179505681109104045564469 673078657603978504271669)
                    ·
                      rfl

theorem cell23_3932448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 4, 1, 1, 5].length) (baseStart_3932448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3932448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3932448 prefixEnd_3932448 := by exact prefixLift 3932448
  have htrace : WordTrace (prefixWord ++ tailWord_3932448) baseStart_3932448 baseEnd_3932448 := by
    simpa [prefixWord, tailWord_3932448, baseEnd_3932448] using wordTrace_append hprefix tailTrace_3932448
  have hstable : (prefixWord ++ tailWord_3932448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3932448).length < 2 ^ (prefixWord ++ tailWord_3932448).sum := by decide
  have hdescent : baseEnd_3932448 < baseStart_3932448 := by decide
  rcases family_descends (prefixWord ++ tailWord_3932448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3932451 : List Nat := [1, 1, 1, 4, 2, 2, 3, 3, 1, 1, 4]
def baseStart_3932451 : Nat := 118140960795 + 3932451 * 2 ^ 59
def prefixEnd_3932451 : Nat := 4983230072969 + 3 ^ 40 * 3932451 * 2
def baseEnd_3932451 : Nat := 2019237513253899001077493

theorem tailTrace_3932451 : CollatzResearch.WordTrace tailWord_3932451 prefixEnd_3932451 2019237513253899001077493 := by
  unfold tailWord_3932451
  simp only [CollatzResearch.WordTrace]
  refine ⟨143428271076409111006373207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95618847384272740670915471 143428271076409111006373207)
  ·
    refine ⟨215142406614613666509559811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143428271076409111006373207 215142406614613666509559811)
    ·
      refine ⟨322713609921920499764339717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215142406614613666509559811 322713609921920499764339717)
      ·
        refine ⟨60508801860360093705813697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 322713609921920499764339717 60508801860360093705813697)
        ·
          refine ⟨45381601395270070279360273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60508801860360093705813697 45381601395270070279360273)
          ·
            refine ⟨34036201046452552709520205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45381601395270070279360273 34036201046452552709520205)
            ·
              refine ⟨12763575392419707266070077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34036201046452552709520205 12763575392419707266070077)
              ·
                refine ⟨4786340772157390224776279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12763575392419707266070077 4786340772157390224776279)
                ·
                  refine ⟨7179511158236085337164419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4786340772157390224776279 7179511158236085337164419)
                  ·
                    refine ⟨10769266737354128005746629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7179511158236085337164419 10769266737354128005746629)
                    ·
                      refine ⟨2019237513253899001077493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10769266737354128005746629 2019237513253899001077493)
                      ·
                        rfl

theorem cell23_3932451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3, 3, 1, 1, 4].length) (baseStart_3932451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3932451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3932451 prefixEnd_3932451 := by exact prefixLift 3932451
  have htrace : WordTrace (prefixWord ++ tailWord_3932451) baseStart_3932451 baseEnd_3932451 := by
    simpa [prefixWord, tailWord_3932451, baseEnd_3932451] using wordTrace_append hprefix tailTrace_3932451
  have hstable : (prefixWord ++ tailWord_3932451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3932451).length < 2 ^ (prefixWord ++ tailWord_3932451).sum := by decide
  have hdescent : baseEnd_3932451 < baseStart_3932451 := by decide
  rcases family_descends (prefixWord ++ tailWord_3932451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3932462 : List Nat := [4, 1, 3, 3, 1, 1, 2, 1, 3, 1, 3]
def baseStart_3932462 : Nat := 118140960795 + 3932462 * 2 ^ 59
def prefixEnd_3932462 : Nat := 4983230072969 + 3 ^ 40 * 3932462 * 2
def baseEnd_3932462 : Nat := 2019243161541098458039943

theorem tailTrace_3932462 : CollatzResearch.WordTrace tailWord_3932462 prefixEnd_3932462 2019243161541098458039943 := by
  unfold tailWord_3932462
  simp only [CollatzResearch.WordTrace]
  refine ⟨17928584034921157485627955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95619114852912839923349093 17928584034921157485627955)
  ·
    refine ⟨26892876052381736228441933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17928584034921157485627955 26892876052381736228441933)
    ·
      refine ⟨10084828519643151085665725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26892876052381736228441933 10084828519643151085665725)
      ·
        refine ⟨3781810694866181657124647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10084828519643151085665725 3781810694866181657124647)
        ·
          refine ⟨5672716042299272485686971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3781810694866181657124647 5672716042299272485686971)
          ·
            refine ⟨8509074063448908728530457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5672716042299272485686971 8509074063448908728530457)
            ·
              refine ⟨6381805547586681546397843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8509074063448908728530457 6381805547586681546397843)
              ·
                refine ⟨9572708321380022319596765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6381805547586681546397843 9572708321380022319596765)
                ·
                  refine ⟨3589765620517508369848787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9572708321380022319596765 3589765620517508369848787)
                  ·
                    refine ⟨5384648430776262554773181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3589765620517508369848787 5384648430776262554773181)
                    ·
                      refine ⟨2019243161541098458039943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5384648430776262554773181 2019243161541098458039943)
                      ·
                        rfl

theorem cell23_3932462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 2, 1, 3, 1, 3].length) (baseStart_3932462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3932462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3932462 prefixEnd_3932462 := by exact prefixLift 3932462
  have htrace : WordTrace (prefixWord ++ tailWord_3932462) baseStart_3932462 baseEnd_3932462 := by
    simpa [prefixWord, tailWord_3932462, baseEnd_3932462] using wordTrace_append hprefix tailTrace_3932462
  have hstable : (prefixWord ++ tailWord_3932462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3932462).length < 2 ^ (prefixWord ++ tailWord_3932462).sum := by decide
  have hdescent : baseEnd_3932462 < baseStart_3932462 := by decide
  rcases family_descends (prefixWord ++ tailWord_3932462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3932478 : List Nat := [4, 2, 1, 2, 1, 4, 1, 1, 1, 6]
def baseStart_3932478 : Nat := 118140960795 + 3932478 * 2 ^ 59
def prefixEnd_3932478 : Nat := 4983230072969 + 3 ^ 40 * 3932478 * 2
def baseEnd_3932478 : Nat := 673083792410523465146623

theorem tailTrace_3932478 : CollatzResearch.WordTrace tailWord_3932478 prefixEnd_3932478 673083792410523465146623 := by
  unfold tailWord_3932478
  simp only [CollatzResearch.WordTrace]
  refine ⟨17928656980913911827200761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95619503898207529745070725 17928656980913911827200761)
  ·
    refine ⟨13446492735685433870400571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17928656980913911827200761 13446492735685433870400571)
    ·
      refine ⟨20169739103528150805600857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13446492735685433870400571 20169739103528150805600857)
      ·
        refine ⟨15127304327646113104200643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20169739103528150805600857 15127304327646113104200643)
        ·
          refine ⟨22690956491469169656300965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15127304327646113104200643 22690956491469169656300965)
          ·
            refine ⟨4254554342150469310556431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22690956491469169656300965 4254554342150469310556431)
            ·
              refine ⟨6381831513225703965834647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4254554342150469310556431 6381831513225703965834647)
              ·
                refine ⟨9572747269838555948751971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6381831513225703965834647 9572747269838555948751971)
                ·
                  refine ⟨14359120904757833923127957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9572747269838555948751971 14359120904757833923127957)
                  ·
                    refine ⟨673083792410523465146623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14359120904757833923127957 673083792410523465146623)
                    ·
                      rfl

theorem cell23_3932478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 1, 1, 1, 6].length) (baseStart_3932478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3932478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3932478 prefixEnd_3932478 := by exact prefixLift 3932478
  have htrace : WordTrace (prefixWord ++ tailWord_3932478) baseStart_3932478 baseEnd_3932478 := by
    simpa [prefixWord, tailWord_3932478, baseEnd_3932478] using wordTrace_append hprefix tailTrace_3932478
  have hstable : (prefixWord ++ tailWord_3932478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3932478).length < 2 ^ (prefixWord ++ tailWord_3932478).sum := by decide
  have hdescent : baseEnd_3932478 < baseStart_3932478 := by decide
  rcases family_descends (prefixWord ++ tailWord_3932478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3932508 : List Nat := [2, 2, 4, 3, 1, 2, 9]
def baseStart_3932508 : Nat := 118140960795 + 3932508 * 2 ^ 59
def prefixEnd_3932508 : Nat := 4983230072969 + 3 ^ 40 * 3932508 * 2
def baseEnd_3932508 : Nat := 24929219526558089852651

theorem tailTrace_3932508 : CollatzResearch.WordTrace tailWord_3932508 prefixEnd_3932508 24929219526558089852651 := by
  unfold tailWord_3932508
  simp only [CollatzResearch.WordTrace]
  refine ⟨71715175018601304870599089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95620233358135073160798785 71715175018601304870599089)
  ·
    refine ⟨53786381263950978652949317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71715175018601304870599089 53786381263950978652949317)
    ·
      refine ⟨10084946486990808497427997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53786381263950978652949317 10084946486990808497427997)
      ·
        refine ⟨3781854932621553186535499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10084946486990808497427997 3781854932621553186535499)
        ·
          refine ⟨5672782398932329779803249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3781854932621553186535499 5672782398932329779803249)
          ·
            refine ⟨4254586799199247334852437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5672782398932329779803249 4254586799199247334852437)
            ·
              refine ⟨24929219526558089852651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4254586799199247334852437 24929219526558089852651)
              ·
                rfl

theorem cell23_3932508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 9].length) (baseStart_3932508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3932508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3932508 prefixEnd_3932508 := by exact prefixLift 3932508
  have htrace : WordTrace (prefixWord ++ tailWord_3932508) baseStart_3932508 baseEnd_3932508 := by
    simpa [prefixWord, tailWord_3932508, baseEnd_3932508] using wordTrace_append hprefix tailTrace_3932508
  have hstable : (prefixWord ++ tailWord_3932508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3932508).length < 2 ^ (prefixWord ++ tailWord_3932508).sum := by decide
  have hdescent : baseEnd_3932508 < baseStart_3932508 := by decide
  rcases family_descends (prefixWord ++ tailWord_3932508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3932519 : List Nat := [1, 1, 5, 1, 3, 2, 3, 2, 1, 2, 2]
def baseStart_3932519 : Nat := 118140960795 + 3932519 * 2 ^ 59
def prefixEnd_3932519 : Nat := 4983230072969 + 3 ^ 40 * 3932519 * 2
def baseEnd_3932519 : Nat := 2019272429938404735027181

theorem tailTrace_3932519 : CollatzResearch.WordTrace tailWord_3932519 prefixEnd_3932519 2019272429938404735027181 := by
  unfold tailWord_3932519
  simp only [CollatzResearch.WordTrace]
  refine ⟨143430751240162758619848611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95620500826775172413232407 143430751240162758619848611)
  ·
    refine ⟨215146126860244137929772917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143430751240162758619848611 215146126860244137929772917)
    ·
      refine ⟨20169949393147887930916211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 215146126860244137929772917 20169949393147887930916211)
      ·
        refine ⟨30254924089721831896374317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20169949393147887930916211 30254924089721831896374317)
        ·
          refine ⟨11345596533645686961140369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30254924089721831896374317 11345596533645686961140369)
          ·
            refine ⟨8509197400234265220855277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11345596533645686961140369 8509197400234265220855277)
            ·
              refine ⟨3190949025087849457820729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8509197400234265220855277 3190949025087849457820729)
              ·
                refine ⟨2393211768815887093365547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3190949025087849457820729 2393211768815887093365547)
                ·
                  refine ⟨3589817653223830640048321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2393211768815887093365547 3589817653223830640048321)
                  ·
                    refine ⟨2692363239917872980036241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3589817653223830640048321 2692363239917872980036241)
                    ·
                      refine ⟨2019272429938404735027181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2692363239917872980036241 2019272429938404735027181)
                      ·
                        rfl

theorem cell23_3932519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 3, 2, 1, 2, 2].length) (baseStart_3932519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3932519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3932519 prefixEnd_3932519 := by exact prefixLift 3932519
  have htrace : WordTrace (prefixWord ++ tailWord_3932519) baseStart_3932519 baseEnd_3932519 := by
    simpa [prefixWord, tailWord_3932519, baseEnd_3932519] using wordTrace_append hprefix tailTrace_3932519
  have hstable : (prefixWord ++ tailWord_3932519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3932519).length < 2 ^ (prefixWord ++ tailWord_3932519).sum := by decide
  have hdescent : baseEnd_3932519 < baseStart_3932519 := by decide
  rcases family_descends (prefixWord ++ tailWord_3932519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3932545 : List Nat := [1, 2, 4, 3, 1, 2, 1, 1, 3, 3, 2]
def baseStart_3932545 : Nat := 118140960795 + 3932545 * 2 ^ 59
def prefixEnd_3932545 : Nat := 4983230072969 + 3 ^ 40 * 3932545 * 2
def baseEnd_3932545 : Nat := 2019285780435421633302061

theorem tailTrace_3932545 : CollatzResearch.WordTrace tailWord_3932545 prefixEnd_3932545 2019285780435421633302061 := by
  unfold tailWord_3932545
  simp only [CollatzResearch.WordTrace]
  refine ⟨143431699538068565060295089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95621133025379043373530059 143431699538068565060295089)
  ·
    refine ⟨107573774653551423795221317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143431699538068565060295089 107573774653551423795221317)
    ·
      refine ⟨20170082747540891961603997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 107573774653551423795221317 20170082747540891961603997)
      ·
        refine ⟨7563781030327834485601499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20170082747540891961603997 7563781030327834485601499)
        ·
          refine ⟨11345671545491751728402249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7563781030327834485601499 11345671545491751728402249)
          ·
            refine ⟨8509253659118813796301687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11345671545491751728402249 8509253659118813796301687)
            ·
              refine ⟨12763880488678220694452531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8509253659118813796301687 12763880488678220694452531)
              ·
                refine ⟨19145820733017331041678797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12763880488678220694452531 19145820733017331041678797)
                ·
                  refine ⟨7179682774881499140629549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19145820733017331041678797 7179682774881499140629549)
                  ·
                    refine ⟨2692381040580562177736081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7179682774881499140629549 2692381040580562177736081)
                    ·
                      refine ⟨2019285780435421633302061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2692381040580562177736081 2019285780435421633302061)
                      ·
                        rfl

theorem cell23_3932545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 1, 1, 3, 3, 2].length) (baseStart_3932545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3932545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3932545 prefixEnd_3932545 := by exact prefixLift 3932545
  have htrace : WordTrace (prefixWord ++ tailWord_3932545) baseStart_3932545 baseEnd_3932545 := by
    simpa [prefixWord, tailWord_3932545, baseEnd_3932545] using wordTrace_append hprefix tailTrace_3932545
  have hstable : (prefixWord ++ tailWord_3932545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3932545).length < 2 ^ (prefixWord ++ tailWord_3932545).sum := by decide
  have hdescent : baseEnd_3932545 < baseStart_3932545 := by decide
  rcases family_descends (prefixWord ++ tailWord_3932545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3932626 : List Nat := [3, 2, 2, 4, 1, 2, 1, 2, 2, 2, 2]
def baseStart_3932626 : Nat := 118140960795 + 3932626 * 2 ^ 59
def prefixEnd_3932626 : Nat := 4983230072969 + 3 ^ 40 * 3932626 * 2
def baseEnd_3932626 : Nat := 2019327372368435816389189

theorem tailTrace_3932626 : CollatzResearch.WordTrace tailWord_3932626 prefixEnd_3932626 2019327372368435816389189 := by
  unfold tailWord_3932626
  simp only [CollatzResearch.WordTrace]
  refine ⟨35858663462693778973498433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95623102567183410595995821 35858663462693778973498433)
  ·
    refine ⟨26893997597020334230123825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35858663462693778973498433 26893997597020334230123825)
    ·
      refine ⟨20170498197765250672592869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26893997597020334230123825 20170498197765250672592869)
      ·
        refine ⟨3781968412080984501111163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20170498197765250672592869 3781968412080984501111163)
        ·
          refine ⟨5672952618121476751666745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3781968412080984501111163 5672952618121476751666745)
          ·
            refine ⟨4254714463591107563750059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5672952618121476751666745 4254714463591107563750059)
            ·
              refine ⟨6382071695386661345625089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4254714463591107563750059 6382071695386661345625089)
              ·
                refine ⟨4786553771539996009218817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6382071695386661345625089 4786553771539996009218817)
                ·
                  refine ⟨3589915328654997006914113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4786553771539996009218817 3589915328654997006914113)
                  ·
                    refine ⟨2692436496491247755185585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3589915328654997006914113 2692436496491247755185585)
                    ·
                      refine ⟨2019327372368435816389189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2692436496491247755185585 2019327372368435816389189)
                      ·
                        rfl

theorem cell23_3932626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 1, 2, 2, 2, 2].length) (baseStart_3932626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3932626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3932626 prefixEnd_3932626 := by exact prefixLift 3932626
  have htrace : WordTrace (prefixWord ++ tailWord_3932626) baseStart_3932626 baseEnd_3932626 := by
    simpa [prefixWord, tailWord_3932626, baseEnd_3932626] using wordTrace_append hprefix tailTrace_3932626
  have hstable : (prefixWord ++ tailWord_3932626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3932626).length < 2 ^ (prefixWord ++ tailWord_3932626).sum := by decide
  have hdescent : baseEnd_3932626 < baseStart_3932626 := by decide
  rcases family_descends (prefixWord ++ tailWord_3932626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3932651 : List Nat := [1, 1, 1, 1, 2, 3, 3, 1, 3, 4, 3]
def baseStart_3932651 : Nat := 118140960795 + 3932651 * 2 ^ 59
def prefixEnd_3932651 : Nat := 4983230072969 + 3 ^ 40 * 3932651 * 2
def baseEnd_3932651 : Nat := 2019340209384798218576573

theorem tailTrace_3932651 : CollatzResearch.WordTrace tailWord_3932651 prefixEnd_3932651 2019340209384798218576573 := by
  unfold tailWord_3932651
  simp only [CollatzResearch.WordTrace]
  refine ⟨143435565675684545163653807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95623710450456363442435871 143435565675684545163653807)
  ·
    refine ⟨215153348513526817745480711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143435565675684545163653807 215153348513526817745480711)
    ·
      refine ⟨322730022770290226618221067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215153348513526817745480711 322730022770290226618221067)
      ·
        refine ⟨484095034155435339927331601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 322730022770290226618221067 484095034155435339927331601)
        ·
          refine ⟨363071275616576504945498701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 484095034155435339927331601 363071275616576504945498701)
          ·
            refine ⟨136151728356216189354562013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 363071275616576504945498701 136151728356216189354562013)
            ·
              refine ⟨51056898133581071007960755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 136151728356216189354562013 51056898133581071007960755)
              ·
                refine ⟨76585347200371606511941133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51056898133581071007960755 76585347200371606511941133)
                ·
                  refine ⟨28719505200139352441977925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76585347200371606511941133 28719505200139352441977925)
                  ·
                    refine ⟨5384907225026128582870861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28719505200139352441977925 5384907225026128582870861)
                    ·
                      refine ⟨2019340209384798218576573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5384907225026128582870861 2019340209384798218576573)
                      ·
                        rfl

theorem cell23_3932651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 1, 3, 4, 3].length) (baseStart_3932651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3932651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3932651 prefixEnd_3932651 := by exact prefixLift 3932651
  have htrace : WordTrace (prefixWord ++ tailWord_3932651) baseStart_3932651 baseEnd_3932651 := by
    simpa [prefixWord, tailWord_3932651, baseEnd_3932651] using wordTrace_append hprefix tailTrace_3932651
  have hstable : (prefixWord ++ tailWord_3932651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3932651).length < 2 ^ (prefixWord ++ tailWord_3932651).sum := by decide
  have hdescent : baseEnd_3932651 < baseStart_3932651 := by decide
  rcases family_descends (prefixWord ++ tailWord_3932651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3932668 : List Nat := [2, 2, 2, 1, 2, 1, 1, 5, 2, 2, 3]
def baseStart_3932668 : Nat := 118140960795 + 3932668 * 2 ^ 59
def prefixEnd_3932668 : Nat := 4983230072969 + 3 ^ 40 * 3932668 * 2
def baseEnd_3932668 : Nat := 2019348938555924652063995

theorem tailTrace_3932668 : CollatzResearch.WordTrace tailWord_3932668 prefixEnd_3932668 2019348938555924652063995 := by
  unfold tailWord_3932668
  simp only [CollatzResearch.WordTrace]
  refine ⟨71718092858311478533511329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95624123811081971378015105 71718092858311478533511329)
  ·
    refine ⟨53788569643733608900133497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71718092858311478533511329 53788569643733608900133497)
    ·
      refine ⟨40341427232800206675100123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53788569643733608900133497 40341427232800206675100123)
      ·
        refine ⟨60512140849200310012650185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40341427232800206675100123 60512140849200310012650185)
        ·
          refine ⟨45384105636900232509487639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60512140849200310012650185 45384105636900232509487639)
          ·
            refine ⟨68076158455350348764231459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45384105636900232509487639 68076158455350348764231459)
            ·
              refine ⟨102114237683025523146347189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68076158455350348764231459 102114237683025523146347189)
              ·
                refine ⟨9573209782783642794970049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 102114237683025523146347189 9573209782783642794970049)
                ·
                  refine ⟨7179907337087732096227537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9573209782783642794970049 7179907337087732096227537)
                  ·
                    refine ⟨5384930502815799072170653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7179907337087732096227537 5384930502815799072170653)
                    ·
                      refine ⟨2019348938555924652063995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5384930502815799072170653 2019348938555924652063995)
                      ·
                        rfl

theorem cell23_3932668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 5, 2, 2, 3].length) (baseStart_3932668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3932668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3932668 prefixEnd_3932668 := by exact prefixLift 3932668
  have htrace : WordTrace (prefixWord ++ tailWord_3932668) baseStart_3932668 baseEnd_3932668 := by
    simpa [prefixWord, tailWord_3932668, baseEnd_3932668] using wordTrace_append hprefix tailTrace_3932668
  have hstable : (prefixWord ++ tailWord_3932668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3932668).length < 2 ^ (prefixWord ++ tailWord_3932668).sum := by decide
  have hdescent : baseEnd_3932668 < baseStart_3932668 := by decide
  rcases family_descends (prefixWord ++ tailWord_3932668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3932692 : List Nat := [2, 4, 3, 1, 1, 1, 3, 1, 3, 4]
def baseStart_3932692 : Nat := 118140960795 + 3932692 * 2 ^ 59
def prefixEnd_3932692 : Nat := 4983230072969 + 3 ^ 40 * 3932692 * 2
def baseEnd_3932692 : Nat := 673120420697210852721295

theorem tailTrace_3932692 : CollatzResearch.WordTrace tailWord_3932692 prefixEnd_3932692 673120420697210852721295 := by
  unfold tailWord_3932692
  simp only [CollatzResearch.WordTrace]
  refine ⟨71718530534268004582948165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95624707379024006110597553 71718530534268004582948165)
  ·
    refine ⟨13447224475175250859302781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71718530534268004582948165 13447224475175250859302781)
    ·
      refine ⟨5042709178190719072238543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13447224475175250859302781 5042709178190719072238543)
      ·
        refine ⟨7564063767286078608357815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5042709178190719072238543 7564063767286078608357815)
        ·
          refine ⟨11346095650929117912536723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7564063767286078608357815 11346095650929117912536723)
          ·
            refine ⟨17019143476393676868805085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11346095650929117912536723 17019143476393676868805085)
            ·
              refine ⟨6382178803647628825801907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17019143476393676868805085 6382178803647628825801907)
              ·
                refine ⟨9573268205471443238702861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6382178803647628825801907 9573268205471443238702861)
                ·
                  refine ⟨3589975577051791214513573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9573268205471443238702861 3589975577051791214513573)
                  ·
                    refine ⟨673120420697210852721295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3589975577051791214513573 673120420697210852721295)
                    ·
                      rfl

theorem cell23_3932692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 3, 1, 3, 4].length) (baseStart_3932692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3932692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3932692 prefixEnd_3932692 := by exact prefixLift 3932692
  have htrace : WordTrace (prefixWord ++ tailWord_3932692) baseStart_3932692 baseEnd_3932692 := by
    simpa [prefixWord, tailWord_3932692, baseEnd_3932692] using wordTrace_append hprefix tailTrace_3932692
  have hstable : (prefixWord ++ tailWord_3932692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3932692).length < 2 ^ (prefixWord ++ tailWord_3932692).sum := by decide
  have hdescent : baseEnd_3932692 < baseStart_3932692 := by decide
  rcases family_descends (prefixWord ++ tailWord_3932692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3932735 : List Nat := [1, 1, 2, 2, 3, 2, 5, 1, 1, 5]
def baseStart_3932735 : Nat := 118140960795 + 3932735 * 2 ^ 59
def prefixEnd_3932735 : Nat := 4983230072969 + 3 ^ 40 * 3932735 * 2
def baseEnd_3932735 : Nat := 673127780586591963308729

theorem tailTrace_3932735 : CollatzResearch.WordTrace tailWord_3932735 prefixEnd_3932735 673127780586591963308729 := by
  unfold tailWord_3932735
  simp only [CollatzResearch.WordTrace]
  refine ⟨143438629407380227509711659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95625752938253485006474439 143438629407380227509711659)
  ·
    refine ⟨215157944111070341264567489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143438629407380227509711659 215157944111070341264567489)
    ·
      refine ⟨161368458083302755948425617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215157944111070341264567489 161368458083302755948425617)
      ·
        refine ⟨121026343562477066961319213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161368458083302755948425617 121026343562477066961319213)
        ·
          refine ⟨45384878835928900110494705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121026343562477066961319213 45384878835928900110494705)
          ·
            refine ⟨34038659126946675082871029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45384878835928900110494705 34038659126946675082871029)
            ·
              refine ⟨3191124293151250789019159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34038659126946675082871029 3191124293151250789019159)
              ·
                refine ⟨4786686439726876183528739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3191124293151250789019159 4786686439726876183528739)
                ·
                  refine ⟨7180029659590314275293109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4786686439726876183528739 7180029659590314275293109)
                  ·
                    refine ⟨673127780586591963308729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7180029659590314275293109 673127780586591963308729)
                    ·
                      rfl

theorem cell23_3932735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 5, 1, 1, 5].length) (baseStart_3932735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3932735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3932735 prefixEnd_3932735 := by exact prefixLift 3932735
  have htrace : WordTrace (prefixWord ++ tailWord_3932735) baseStart_3932735 baseEnd_3932735 := by
    simpa [prefixWord, tailWord_3932735, baseEnd_3932735] using wordTrace_append hprefix tailTrace_3932735
  have hstable : (prefixWord ++ tailWord_3932735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3932735).length < 2 ^ (prefixWord ++ tailWord_3932735).sum := by decide
  have hdescent : baseEnd_3932735 < baseStart_3932735 := by decide
  rcases family_descends (prefixWord ++ tailWord_3932735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3932751 : List Nat := [1, 1, 2, 1, 1, 2, 4, 1, 3, 1, 6]
def baseStart_3932751 : Nat := 118140960795 + 3932751 * 2 ^ 59
def prefixEnd_3932751 : Nat := 4983230072969 + 3 ^ 40 * 3932751 * 2
def baseEnd_3932751 : Nat := 2019391557450247827326113

theorem tailTrace_3932751 : CollatzResearch.WordTrace tailWord_3932751 prefixEnd_3932751 2019391557450247827326113 := by
  unfold tailWord_3932751
  simp only [CollatzResearch.WordTrace]
  refine ⟨143439212975322262242294107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95626141983548174828196071 143439212975322262242294107)
  ·
    refine ⟨215158819462983393363441161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143439212975322262242294107 215158819462983393363441161)
    ·
      refine ⟨161369114597237545022580871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215158819462983393363441161 161369114597237545022580871)
      ·
        refine ⟨242053671895856317533871307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161369114597237545022580871 242053671895856317533871307)
        ·
          refine ⟨363080507843784476300806961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242053671895856317533871307 363080507843784476300806961)
          ·
            refine ⟨272310380882838357225605221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 363080507843784476300806961 272310380882838357225605221)
            ·
              refine ⟨51058196415532191979800979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 272310380882838357225605221 51058196415532191979800979)
              ·
                refine ⟨76587294623298287969701469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51058196415532191979800979 76587294623298287969701469)
                ·
                  refine ⟨28720235483736857988638051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76587294623298287969701469 28720235483736857988638051)
                  ·
                    refine ⟨43080353225605286982957077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28720235483736857988638051 43080353225605286982957077)
                    ·
                      refine ⟨2019391557450247827326113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 43080353225605286982957077 2019391557450247827326113)
                      ·
                        rfl

theorem cell23_3932751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 1, 3, 1, 6].length) (baseStart_3932751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3932751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3932751 prefixEnd_3932751 := by exact prefixLift 3932751
  have htrace : WordTrace (prefixWord ++ tailWord_3932751) baseStart_3932751 baseEnd_3932751 := by
    simpa [prefixWord, tailWord_3932751, baseEnd_3932751] using wordTrace_append hprefix tailTrace_3932751
  have hstable : (prefixWord ++ tailWord_3932751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3932751).length < 2 ^ (prefixWord ++ tailWord_3932751).sum := by decide
  have hdescent : baseEnd_3932751 < baseStart_3932751 := by decide
  rcases family_descends (prefixWord ++ tailWord_3932751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3932768 : List Nat := [2, 1, 1, 3, 2, 1, 3, 3, 1, 2, 4]
def baseStart_3932768 : Nat := 118140960795 + 3932768 * 2 ^ 59
def prefixEnd_3932768 : Nat := 4983230072969 + 3 ^ 40 * 3932768 * 2
def baseEnd_3932768 : Nat := 2019400286621374260813535

theorem tailTrace_3932768 : CollatzResearch.WordTrace tailWord_3932768 prefixEnd_3932768 2019400286621374260813535 := by
  unfold tailWord_3932768
  simp only [CollatzResearch.WordTrace]
  refine ⟨71719916508130337072831479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95626555344173782763775305 71719916508130337072831479)
  ·
    refine ⟨107579874762195505609247219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71719916508130337072831479 107579874762195505609247219)
    ·
      refine ⟨161369812143293258413870829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107579874762195505609247219 161369812143293258413870829)
      ·
        refine ⟨60513679553734971905201561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 161369812143293258413870829 60513679553734971905201561)
        ·
          refine ⟨45385259665301228928901171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60513679553734971905201561 45385259665301228928901171)
          ·
            refine ⟨68077889497951843393351757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45385259665301228928901171 68077889497951843393351757)
            ·
              refine ⟨25529208561731941272506909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68077889497951843393351757 25529208561731941272506909)
              ·
                refine ⟨9573453210649477977190091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25529208561731941272506909 9573453210649477977190091)
                ·
                  refine ⟨14360179815974216965785137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9573453210649477977190091 14360179815974216965785137)
                  ·
                    refine ⟨10770134861980662724338853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14360179815974216965785137 10770134861980662724338853)
                    ·
                      refine ⟨2019400286621374260813535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10770134861980662724338853 2019400286621374260813535)
                      ·
                        rfl

theorem cell23_3932768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 3, 1, 2, 4].length) (baseStart_3932768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3932768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3932768 prefixEnd_3932768 := by exact prefixLift 3932768
  have htrace : WordTrace (prefixWord ++ tailWord_3932768) baseStart_3932768 baseEnd_3932768 := by
    simpa [prefixWord, tailWord_3932768, baseEnd_3932768] using wordTrace_append hprefix tailTrace_3932768
  have hstable : (prefixWord ++ tailWord_3932768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3932768).length < 2 ^ (prefixWord ++ tailWord_3932768).sum := by decide
  have hdescent : baseEnd_3932768 < baseStart_3932768 := by decide
  rcases family_descends (prefixWord ++ tailWord_3932768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3932772 : List Nat := [2, 3, 1, 1, 2, 2, 3, 2, 3, 2, 2]
def baseStart_3932772 : Nat := 118140960795 + 3932772 * 2 ^ 59
def prefixEnd_3932772 : Nat := 4983230072969 + 3 ^ 40 * 3932772 * 2
def baseEnd_3932772 : Nat := 2019402340543992245163517

theorem tailTrace_3932772 : CollatzResearch.WordTrace tailWord_3932772 prefixEnd_3932772 2019402340543992245163517 := by
  unfold tailWord_3932772
  simp only [CollatzResearch.WordTrace]
  refine ⟨71719989454123091414404285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95626652605497455219205713 71719989454123091414404285)
  ·
    refine ⟨26894996045296159280401607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71719989454123091414404285 26894996045296159280401607)
    ·
      refine ⟨40342494067944238920602411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26894996045296159280401607 40342494067944238920602411)
      ·
        refine ⟨60513741101916358380903617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40342494067944238920602411 60513741101916358380903617)
        ·
          refine ⟨45385305826437268785677713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60513741101916358380903617 45385305826437268785677713)
          ·
            refine ⟨34038979369827951589258285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45385305826437268785677713 34038979369827951589258285)
            ·
              refine ⟨12764617263685481845971857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34038979369827951589258285 12764617263685481845971857)
              ·
                refine ⟨9573462947764111384478893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12764617263685481845971857 9573462947764111384478893)
                ·
                  refine ⟨3590048605411541769179585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9573462947764111384478893 3590048605411541769179585)
                  ·
                    refine ⟨2692536454058656326884689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3590048605411541769179585 2692536454058656326884689)
                    ·
                      refine ⟨2019402340543992245163517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2692536454058656326884689 2019402340543992245163517)
                      ·
                        rfl

theorem cell23_3932772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3, 2, 3, 2, 2].length) (baseStart_3932772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3932772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3932772 prefixEnd_3932772 := by exact prefixLift 3932772
  have htrace : WordTrace (prefixWord ++ tailWord_3932772) baseStart_3932772 baseEnd_3932772 := by
    simpa [prefixWord, tailWord_3932772, baseEnd_3932772] using wordTrace_append hprefix tailTrace_3932772
  have hstable : (prefixWord ++ tailWord_3932772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3932772).length < 2 ^ (prefixWord ++ tailWord_3932772).sum := by decide
  have hdescent : baseEnd_3932772 < baseStart_3932772 := by decide
  rcases family_descends (prefixWord ++ tailWord_3932772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3932775 : List Nat := [1, 1, 5, 1, 1, 1, 1, 6, 1, 2, 3]
def baseStart_3932775 : Nat := 118140960795 + 3932775 * 2 ^ 59
def prefixEnd_3932775 : Nat := 4983230072969 + 3 ^ 40 * 3932775 * 2
def baseEnd_3932775 : Nat := 2019403880985955733426003

theorem tailTrace_3932775 : CollatzResearch.WordTrace tailWord_3932775 prefixEnd_3932775 2019403880985955733426003 := by
  unfold tailWord_3932775
  simp only [CollatzResearch.WordTrace]
  refine ⟨143440088327235314341167779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95626725551490209560778519 143440088327235314341167779)
  ·
    refine ⟨215160132490852971511751669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143440088327235314341167779 215160132490852971511751669)
    ·
      refine ⟨20171262421017466079226719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 215160132490852971511751669 20171262421017466079226719)
      ·
        refine ⟨30256893631526199118840079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20171262421017466079226719 30256893631526199118840079)
        ·
          refine ⟨45385340447289298678260119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30256893631526199118840079 45385340447289298678260119)
          ·
            refine ⟨68078010670933948017390179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45385340447289298678260119 68078010670933948017390179)
            ·
              refine ⟨102117016006400922026085269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68078010670933948017390179 102117016006400922026085269)
              ·
                refine ⟨4786735125300043219972747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 102117016006400922026085269 4786735125300043219972747)
                ·
                  refine ⟨7180102687950064829959121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4786735125300043219972747 7180102687950064829959121)
                  ·
                    refine ⟨5385077015962548622469341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7180102687950064829959121 5385077015962548622469341)
                    ·
                      refine ⟨2019403880985955733426003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5385077015962548622469341 2019403880985955733426003)
                      ·
                        rfl

theorem cell23_3932775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 6, 1, 2, 3].length) (baseStart_3932775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3932775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3932775 prefixEnd_3932775 := by exact prefixLift 3932775
  have htrace : WordTrace (prefixWord ++ tailWord_3932775) baseStart_3932775 baseEnd_3932775 := by
    simpa [prefixWord, tailWord_3932775, baseEnd_3932775] using wordTrace_append hprefix tailTrace_3932775
  have hstable : (prefixWord ++ tailWord_3932775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3932775).length < 2 ^ (prefixWord ++ tailWord_3932775).sum := by decide
  have hdescent : baseEnd_3932775 < baseStart_3932775 := by decide
  rcases family_descends (prefixWord ++ tailWord_3932775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3932776 : List Nat := [2, 1, 4, 3, 3, 1, 1, 1, 2, 3, 2]
def baseStart_3932776 : Nat := 118140960795 + 3932776 * 2 ^ 59
def prefixEnd_3932776 : Nat := 4983230072969 + 3 ^ 40 * 3932776 * 2
def baseEnd_3932776 : Nat := 2019404394466610229513499

theorem tailTrace_3932776 : CollatzResearch.WordTrace tailWord_3932776 prefixEnd_3932776 2019404394466610229513499 := by
  unfold tailWord_3932776
  simp only [CollatzResearch.WordTrace]
  refine ⟨71720062400115845755977091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95626749866821127674636121 71720062400115845755977091)
  ·
    refine ⟨107580093600173768633965637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71720062400115845755977091 107580093600173768633965637)
    ·
      refine ⟨20171267550032581618868557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 107580093600173768633965637 20171267550032581618868557)
      ·
        refine ⟨7564225331262218107075709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20171267550032581618868557 7564225331262218107075709)
        ·
          refine ⟨2836584499223331790153391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7564225331262218107075709 2836584499223331790153391)
          ·
            refine ⟨4254876748834997685230087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2836584499223331790153391 4254876748834997685230087)
            ·
              refine ⟨6382315123252496527845131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4254876748834997685230087 6382315123252496527845131)
              ·
                refine ⟨9573472684878744791767697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6382315123252496527845131 9573472684878744791767697)
                ·
                  refine ⟨7180104513659058593825773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9573472684878744791767697 7180104513659058593825773)
                  ·
                    refine ⟨2692539192622146972684665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7180104513659058593825773 2692539192622146972684665)
                    ·
                      refine ⟨2019404394466610229513499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2692539192622146972684665 2019404394466610229513499)
                      ·
                        rfl

theorem cell23_3932776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 1, 1, 2, 3, 2].length) (baseStart_3932776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3932776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3932776 prefixEnd_3932776 := by exact prefixLift 3932776
  have htrace : WordTrace (prefixWord ++ tailWord_3932776) baseStart_3932776 baseEnd_3932776 := by
    simpa [prefixWord, tailWord_3932776, baseEnd_3932776] using wordTrace_append hprefix tailTrace_3932776
  have hstable : (prefixWord ++ tailWord_3932776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3932776).length < 2 ^ (prefixWord ++ tailWord_3932776).sum := by decide
  have hdescent : baseEnd_3932776 < baseStart_3932776 := by decide
  rcases family_descends (prefixWord ++ tailWord_3932776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3932848 : List Nat := [2, 1, 1, 1, 2, 1, 3, 2, 1, 6, 3]
def baseStart_3932848 : Nat := 118140960795 + 3932848 * 2 ^ 59
def prefixEnd_3932848 : Nat := 4983230072969 + 3 ^ 40 * 3932848 * 2
def baseEnd_3932848 : Nat := 2019441365073733947813167

theorem tailTrace_3932848 : CollatzResearch.WordTrace tailWord_3932848 prefixEnd_3932848 2019441365073733947813167 := by
  unfold tailWord_3932848
  simp only [CollatzResearch.WordTrace]
  refine ⟨71721375427985423904287599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95628500570647231872383465 71721375427985423904287599)
  ·
    refine ⟨107582063141978135856431399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71721375427985423904287599 107582063141978135856431399)
    ·
      refine ⟨161373094712967203784647099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107582063141978135856431399 161373094712967203784647099)
      ·
        refine ⟨242059642069450805676970649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161373094712967203784647099 242059642069450805676970649)
        ·
          refine ⟨181544731552088104257727987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 242059642069450805676970649 181544731552088104257727987)
          ·
            refine ⟨272317097328132156386591981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181544731552088104257727987 272317097328132156386591981)
            ·
              refine ⟨102118911498049558644971993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 272317097328132156386591981 102118911498049558644971993)
              ·
                refine ⟨76589183623537168983728995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102118911498049558644971993 76589183623537168983728995)
                ·
                  refine ⟨114883775435305753475593493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76589183623537168983728995 114883775435305753475593493)
                  ·
                    refine ⟨5385176973529957194168445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 114883775435305753475593493 5385176973529957194168445)
                    ·
                      refine ⟨2019441365073733947813167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5385176973529957194168445 2019441365073733947813167)
                      ·
                        rfl

theorem cell23_3932848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 2, 1, 6, 3].length) (baseStart_3932848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3932848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3932848 prefixEnd_3932848 := by exact prefixLift 3932848
  have htrace : WordTrace (prefixWord ++ tailWord_3932848) baseStart_3932848 baseEnd_3932848 := by
    simpa [prefixWord, tailWord_3932848, baseEnd_3932848] using wordTrace_append hprefix tailTrace_3932848
  have hstable : (prefixWord ++ tailWord_3932848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3932848).length < 2 ^ (prefixWord ++ tailWord_3932848).sum := by decide
  have hdescent : baseEnd_3932848 < baseStart_3932848 := by decide
  rcases family_descends (prefixWord ++ tailWord_3932848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3932945 : List Nat := [1, 2, 2, 1, 1, 3, 3, 1, 5, 4]
def baseStart_3932945 : Nat := 118140960795 + 3932945 * 2 ^ 59
def prefixEnd_3932945 : Nat := 4983230072969 + 3 ^ 40 * 3932945 * 2
def baseEnd_3932945 : Nat := 673163724232406689433407

theorem tailTrace_3932945 : CollatzResearch.WordTrace tailWord_3932945 prefixEnd_3932945 673163724232406689433407 := by
  unfold tailWord_3932945
  simp only [CollatzResearch.WordTrace]
  refine ⟨143446288736619433374856289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95630859157746288916570859 143446288736619433374856289)
  ·
    refine ⟨107584716552464575031142217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143446288736619433374856289 107584716552464575031142217)
    ·
      refine ⟨80688537414348431273356663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107584716552464575031142217 80688537414348431273356663)
      ·
        refine ⟨121032806121522646910034995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80688537414348431273356663 121032806121522646910034995)
        ·
          refine ⟨181549209182283970365052493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121032806121522646910034995 181549209182283970365052493)
          ·
            refine ⟨68080953443356488886894685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 181549209182283970365052493 68080953443356488886894685)
            ·
              refine ⟨25530357541258683332585507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68080953443356488886894685 25530357541258683332585507)
              ·
                refine ⟨38295536311888024998878261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25530357541258683332585507 38295536311888024998878261)
                ·
                  refine ⟨3590206529239502343644837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38295536311888024998878261 3590206529239502343644837)
                  ·
                    refine ⟨673163724232406689433407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3590206529239502343644837 673163724232406689433407)
                    ·
                      rfl

theorem cell23_3932945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 1, 5, 4].length) (baseStart_3932945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3932945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3932945 prefixEnd_3932945 := by exact prefixLift 3932945
  have htrace : WordTrace (prefixWord ++ tailWord_3932945) baseStart_3932945 baseEnd_3932945 := by
    simpa [prefixWord, tailWord_3932945, baseEnd_3932945] using wordTrace_append hprefix tailTrace_3932945
  have hstable : (prefixWord ++ tailWord_3932945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3932945).length < 2 ^ (prefixWord ++ tailWord_3932945).sum := by decide
  have hdescent : baseEnd_3932945 < baseStart_3932945 := by decide
  rcases family_descends (prefixWord ++ tailWord_3932945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3932979 : List Nat := [1, 1, 1, 2, 6, 1, 2, 4, 1, 4]
def baseStart_3932979 : Nat := 118140960795 + 3932979 * 2 ^ 59
def prefixEnd_3932979 : Nat := 4983230072969 + 3 ^ 40 * 3932979 * 2
def baseEnd_3932979 : Nat := 673169543679824311758355

theorem tailTrace_3932979 : CollatzResearch.WordTrace tailWord_3932979 prefixEnd_3932979 673169543679824311758355 := by
  unfold tailWord_3932979
  simp only [CollatzResearch.WordTrace]
  refine ⟨143447528818496257181593991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95631685878997504787729327 143447528818496257181593991)
  ·
    refine ⟨215171293227744385772390987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143447528818496257181593991 215171293227744385772390987)
    ·
      refine ⟨322756939841616578658586481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215171293227744385772390987 322756939841616578658586481)
      ·
        refine ⟨242067704881212433993939861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 322756939841616578658586481 242067704881212433993939861)
        ·
          refine ⟨11346923666306832843465931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 242067704881212433993939861 11346923666306832843465931)
          ·
            refine ⟨17020385499460249265198897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11346923666306832843465931 17020385499460249265198897)
            ·
              refine ⟨12765289124595186948899173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17020385499460249265198897 12765289124595186948899173)
              ·
                refine ⟨2393491710861597552918595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12765289124595186948899173 2393491710861597552918595)
                ·
                  refine ⟨3590237566292396329377893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2393491710861597552918595 3590237566292396329377893)
                  ·
                    refine ⟨673169543679824311758355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3590237566292396329377893 673169543679824311758355)
                    ·
                      rfl

theorem cell23_3932979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 2, 4, 1, 4].length) (baseStart_3932979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3932979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3932979 prefixEnd_3932979 := by exact prefixLift 3932979
  have htrace : WordTrace (prefixWord ++ tailWord_3932979) baseStart_3932979 baseEnd_3932979 := by
    simpa [prefixWord, tailWord_3932979, baseEnd_3932979] using wordTrace_append hprefix tailTrace_3932979
  have hstable : (prefixWord ++ tailWord_3932979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3932979).length < 2 ^ (prefixWord ++ tailWord_3932979).sum := by decide
  have hdescent : baseEnd_3932979 < baseStart_3932979 := by decide
  rcases family_descends (prefixWord ++ tailWord_3932979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3933002 : List Nat := [3, 1, 2, 1, 1, 1, 2, 3, 5, 1, 3]
def baseStart_3933002 : Nat := 118140960795 + 3933002 * 2 ^ 59
def prefixEnd_3933002 : Nat := 4983230072969 + 3 ^ 40 * 3933002 * 2
def baseEnd_3933002 : Nat := 2019520441094526345287459

theorem tailTrace_3933002 : CollatzResearch.WordTrace tailWord_3933002 prefixEnd_3933002 2019520441094526345287459 := by
  unfold tailWord_3933002
  simp only [CollatzResearch.WordTrace]
  refine ⟨35862091924353233027420315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95632245131608621406454173 35862091924353233027420315)
  ·
    refine ⟨53793137886529849541130473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35862091924353233027420315 53793137886529849541130473)
    ·
      refine ⟨40344853414897387155847855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53793137886529849541130473 40344853414897387155847855)
      ·
        refine ⟨60517280122346080733771783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40344853414897387155847855 60517280122346080733771783)
        ·
          refine ⟨90775920183519121100657675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60517280122346080733771783 90775920183519121100657675)
          ·
            refine ⟨136163880275278681650986513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90775920183519121100657675 136163880275278681650986513)
            ·
              refine ⟨102122910206459011238239885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136163880275278681650986513 102122910206459011238239885)
              ·
                refine ⟨38296091327422129214339957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 102122910206459011238239885 38296091327422129214339957)
                ·
                  refine ⟨3590258561945824613844371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38296091327422129214339957 3590258561945824613844371)
                  ·
                    refine ⟨5385387842918736920766557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3590258561945824613844371 5385387842918736920766557)
                    ·
                      refine ⟨2019520441094526345287459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5385387842918736920766557 2019520441094526345287459)
                      ·
                        rfl

theorem cell23_3933002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 3, 5, 1, 3].length) (baseStart_3933002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3933002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3933002 prefixEnd_3933002 := by exact prefixLift 3933002
  have htrace : WordTrace (prefixWord ++ tailWord_3933002) baseStart_3933002 baseEnd_3933002 := by
    simpa [prefixWord, tailWord_3933002, baseEnd_3933002] using wordTrace_append hprefix tailTrace_3933002
  have hstable : (prefixWord ++ tailWord_3933002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3933002).length < 2 ^ (prefixWord ++ tailWord_3933002).sum := by decide
  have hdescent : baseEnd_3933002 < baseStart_3933002 := by decide
  rcases family_descends (prefixWord ++ tailWord_3933002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3933055 : List Nat := [1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 6]
def baseStart_3933055 : Nat := 118140960795 + 3933055 * 2 ^ 59
def prefixEnd_3933055 : Nat := 4983230072969 + 3 ^ 40 * 3933055 * 2
def baseEnd_3933055 : Nat := 2019547655569214637924715

theorem tailTrace_3933055 : CollatzResearch.WordTrace tailWord_3933055 prefixEnd_3933055 2019547655569214637924715 := by
  unfold tailWord_3933055
  simp only [CollatzResearch.WordTrace]
  refine ⟨143450300766220922161360619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95633533844147281440907079 143450300766220922161360619)
  ·
    refine ⟨215175451149331383242040929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143450300766220922161360619 215175451149331383242040929)
    ·
      refine ⟨161381588361998537431530697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215175451149331383242040929 161381588361998537431530697)
      ·
        refine ⟨121036191271498903073648023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161381588361998537431530697 121036191271498903073648023)
        ·
          refine ⟨181554286907248354610472035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121036191271498903073648023 181554286907248354610472035)
          ·
            refine ⟨272331430360872531915708053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181554286907248354610472035 272331430360872531915708053)
            ·
              refine ⟨12765535798165899933548815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 272331430360872531915708053 12765535798165899933548815)
              ·
                refine ⟨19148303697248849900323223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12765535798165899933548815 19148303697248849900323223)
                ·
                  refine ⟨28722455545873274850484835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19148303697248849900323223 28722455545873274850484835)
                  ·
                    refine ⟨43083683318809912275727253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28722455545873274850484835 43083683318809912275727253)
                    ·
                      refine ⟨2019547655569214637924715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 43083683318809912275727253 2019547655569214637924715)
                      ·
                        rfl

theorem cell23_3933055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 6].length) (baseStart_3933055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3933055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3933055 prefixEnd_3933055 := by exact prefixLift 3933055
  have htrace : WordTrace (prefixWord ++ tailWord_3933055) baseStart_3933055 baseEnd_3933055 := by
    simpa [prefixWord, tailWord_3933055, baseEnd_3933055] using wordTrace_append hprefix tailTrace_3933055
  have hstable : (prefixWord ++ tailWord_3933055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3933055).length < 2 ^ (prefixWord ++ tailWord_3933055).sum := by decide
  have hdescent : baseEnd_3933055 < baseStart_3933055 := by decide
  rcases family_descends (prefixWord ++ tailWord_3933055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3933059 : List Nat := [1, 1, 1, 3, 4, 1, 2, 1, 5, 2, 2]
def baseStart_3933059 : Nat := 118140960795 + 3933059 * 2 ^ 59
def prefixEnd_3933059 : Nat := 4983230072969 + 3 ^ 40 * 3933059 * 2
def baseEnd_3933059 : Nat := 2019549709491832622274697

theorem tailTrace_3933059 : CollatzResearch.WordTrace tailWord_3933059 prefixEnd_3933059 2019549709491832622274697 := by
  unfold tailWord_3933059
  simp only [CollatzResearch.WordTrace]
  refine ⟨143450446658206430844506231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95633631105470953896337487 143450446658206430844506231)
  ·
    refine ⟨215175669987309646266759347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143450446658206430844506231 215175669987309646266759347)
    ·
      refine ⟨322763504980964469400139021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215175669987309646266759347 322763504980964469400139021)
      ·
        refine ⟨121036314367861676025052133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 322763504980964469400139021 121036314367861676025052133)
        ·
          refine ⟨22694308943974064254697275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 121036314367861676025052133 22694308943974064254697275)
          ·
            refine ⟨34041463415961096382045913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22694308943974064254697275 34041463415961096382045913)
            ·
              refine ⟨25531097561970822286534435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34041463415961096382045913 25531097561970822286534435)
              ·
                refine ⟨38296646342956233429801653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25531097561970822286534435 38296646342956233429801653)
                ·
                  refine ⟨3590310594652146884043905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38296646342956233429801653 3590310594652146884043905)
                  ·
                    refine ⟨2692732945989110163032929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3590310594652146884043905 2692732945989110163032929)
                    ·
                      refine ⟨2019549709491832622274697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2692732945989110163032929 2019549709491832622274697)
                      ·
                        rfl

theorem cell23_3933059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 1, 5, 2, 2].length) (baseStart_3933059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3933059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3933059 prefixEnd_3933059 := by exact prefixLift 3933059
  have htrace : WordTrace (prefixWord ++ tailWord_3933059) baseStart_3933059 baseEnd_3933059 := by
    simpa [prefixWord, tailWord_3933059, baseEnd_3933059] using wordTrace_append hprefix tailTrace_3933059
  have hstable : (prefixWord ++ tailWord_3933059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3933059).length < 2 ^ (prefixWord ++ tailWord_3933059).sum := by decide
  have hdescent : baseEnd_3933059 < baseStart_3933059 := by decide
  rcases family_descends (prefixWord ++ tailWord_3933059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3933065 : List Nat := [1, 2, 1, 1, 5, 2, 2, 9]
def baseStart_3933065 : Nat := 118140960795 + 3933065 * 2 ^ 59
def prefixEnd_3933065 : Nat := 4983230072969 + 3 ^ 40 * 3933065 * 2
def baseEnd_3933065 : Nat := 74798251495398503659247

theorem tailTrace_3933065 : CollatzResearch.WordTrace tailWord_3933065 prefixEnd_3933065 74798251495398503659247 := by
  unfold tailWord_3933065
  simp only [CollatzResearch.WordTrace]
  refine ⟨143450665496184693869224649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95633776997456462579483099 143450665496184693869224649)
  ·
    refine ⟨107587999122138520401918487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143450665496184693869224649 107587999122138520401918487)
    ·
      refine ⟨161381998683207780602877731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107587999122138520401918487 161381998683207780602877731)
      ·
        refine ⟨242072998024811670904316597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161381998683207780602877731 242072998024811670904316597)
        ·
          refine ⟨22694343564826094147279681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 242072998024811670904316597 22694343564826094147279681)
          ·
            refine ⟨17020757673619570610459761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22694343564826094147279681 17020757673619570610459761)
            ·
              refine ⟨12765568255214677957844821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17020757673619570610459761 12765568255214677957844821)
              ·
                refine ⟨74798251495398503659247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 12765568255214677957844821 74798251495398503659247)
                ·
                  rfl

theorem cell23_3933065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 2, 9].length) (baseStart_3933065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3933065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3933065 prefixEnd_3933065 := by exact prefixLift 3933065
  have htrace : WordTrace (prefixWord ++ tailWord_3933065) baseStart_3933065 baseEnd_3933065 := by
    simpa [prefixWord, tailWord_3933065, baseEnd_3933065] using wordTrace_append hprefix tailTrace_3933065
  have hstable : (prefixWord ++ tailWord_3933065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3933065).length < 2 ^ (prefixWord ++ tailWord_3933065).sum := by decide
  have hdescent : baseEnd_3933065 < baseStart_3933065 := by decide
  rcases family_descends (prefixWord ++ tailWord_3933065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3933076 : List Nat := [2, 4, 2, 1, 1, 1, 5, 1, 1, 1, 4]
def baseStart_3933076 : Nat := 118140960795 + 3933076 * 2 ^ 59
def prefixEnd_3933076 : Nat := 4983230072969 + 3 ^ 40 * 3933076 * 2
def baseEnd_3933076 : Nat := 2019558438662959055762119

theorem tailTrace_3933076 : CollatzResearch.WordTrace tailWord_3933076 prefixEnd_3933076 2019558438662959055762119 := by
  unfold tailWord_3933076
  simp only [CollatzResearch.WordTrace]
  refine ⟨71725533349572421373937541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95634044466096561831916721 71725533349572421373937541)
  ·
    refine ⟨13448537503044829007613289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71725533349572421373937541 13448537503044829007613289)
    ·
      refine ⟨10086403127283621755709967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13448537503044829007613289 10086403127283621755709967)
      ·
        refine ⟨15129604690925432633564951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10086403127283621755709967 15129604690925432633564951)
        ·
          refine ⟨22694407036388148950347427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15129604690925432633564951 22694407036388148950347427)
          ·
            refine ⟨34041610554582223425521141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22694407036388148950347427 34041610554582223425521141)
            ·
              refine ⟨3191400989492083446142607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34041610554582223425521141 3191400989492083446142607)
              ·
                refine ⟨4787101484238125169213911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3191400989492083446142607 4787101484238125169213911)
                ·
                  refine ⟨7180652226357187753820867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4787101484238125169213911 7180652226357187753820867)
                  ·
                    refine ⟨10770978339535781630731301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7180652226357187753820867 10770978339535781630731301)
                    ·
                      refine ⟨2019558438662959055762119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10770978339535781630731301 2019558438662959055762119)
                      ·
                        rfl

theorem cell23_3933076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 5, 1, 1, 1, 4].length) (baseStart_3933076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3933076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3933076 prefixEnd_3933076 := by exact prefixLift 3933076
  have htrace : WordTrace (prefixWord ++ tailWord_3933076) baseStart_3933076 baseEnd_3933076 := by
    simpa [prefixWord, tailWord_3933076, baseEnd_3933076] using wordTrace_append hprefix tailTrace_3933076
  have hstable : (prefixWord ++ tailWord_3933076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3933076).length < 2 ^ (prefixWord ++ tailWord_3933076).sum := by decide
  have hdescent : baseEnd_3933076 < baseStart_3933076 := by decide
  rcases family_descends (prefixWord ++ tailWord_3933076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3933082 : List Nat := [3, 1, 1, 4, 4, 10]
def baseStart_3933082 : Nat := 118140960795 + 3933082 * 2 ^ 59
def prefixEnd_3933082 : Nat := 4983230072969 + 3 ^ 40 * 3933082 * 2
def baseEnd_3933082 : Nat := 8310952755336979556737

theorem tailTrace_3933082 : CollatzResearch.WordTrace tailWord_3933082 prefixEnd_3933082 8310952755336979556737 := by
  unfold tailWord_3933082
  simp only [CollatzResearch.WordTrace]
  refine ⟨35862821384280776443148375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95634190358082070515062333 35862821384280776443148375)
  ·
    refine ⟨53794232076421164664722563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35862821384280776443148375 53794232076421164664722563)
    ·
      refine ⟨80691348114631746997083845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53794232076421164664722563 80691348114631746997083845)
      ·
        refine ⟨15129627771493452561953221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80691348114631746997083845 15129627771493452561953221)
        ·
          refine ⟨2836805207155022355366229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15129627771493452561953221 2836805207155022355366229)
          ·
            refine ⟨8310952755336979556737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2836805207155022355366229 8310952755336979556737)
            ·
              rfl

theorem cell23_3933082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 10].length) (baseStart_3933082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3933082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3933082 prefixEnd_3933082 := by exact prefixLift 3933082
  have htrace : WordTrace (prefixWord ++ tailWord_3933082) baseStart_3933082 baseEnd_3933082 := by
    simpa [prefixWord, tailWord_3933082, baseEnd_3933082] using wordTrace_append hprefix tailTrace_3933082
  have hstable : (prefixWord ++ tailWord_3933082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3933082).length < 2 ^ (prefixWord ++ tailWord_3933082).sum := by decide
  have hdescent : baseEnd_3933082 < baseStart_3933082 := by decide
  rcases family_descends (prefixWord ++ tailWord_3933082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3933092 : List Nat := [2, 3, 1, 2, 1, 2, 1, 2, 3, 3, 3]
def baseStart_3933092 : Nat := 118140960795 + 3933092 * 2 ^ 59
def prefixEnd_3933092 : Nat := 4983230072969 + 3 ^ 40 * 3933092 * 2
def baseEnd_3933092 : Nat := 2019566654353430993162045

theorem tailTrace_3933092 : CollatzResearch.WordTrace tailWord_3933092 prefixEnd_3933092 2019566654353430993162045 := by
  unfold tailWord_3933092
  simp only [CollatzResearch.WordTrace]
  refine ⟨71725825133543438740228765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95634433511391251653638353 71725825133543438740228765)
  ·
    refine ⟨26897184425078789527585787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71725825133543438740228765 26897184425078789527585787)
    ·
      refine ⟨40345776637618184291378681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26897184425078789527585787 40345776637618184291378681)
      ·
        refine ⟨30259332478213638218534011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40345776637618184291378681 30259332478213638218534011)
        ·
          refine ⟨45388998717320457327801017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30259332478213638218534011 45388998717320457327801017)
          ·
            refine ⟨34041749037990342995850763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45388998717320457327801017 34041749037990342995850763)
            ·
              refine ⟨51062623556985514493776145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34041749037990342995850763 51062623556985514493776145)
              ·
                refine ⟨38296967667739135870332109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51062623556985514493776145 38296967667739135870332109)
                ·
                  refine ⟨14361362875402175951374541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38296967667739135870332109 14361362875402175951374541)
                  ·
                    refine ⟨5385511078275815981765453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14361362875402175951374541 5385511078275815981765453)
                    ·
                      refine ⟨2019566654353430993162045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5385511078275815981765453 2019566654353430993162045)
                      ·
                        rfl

theorem cell23_3933092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 2, 3, 3, 3].length) (baseStart_3933092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3933092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3933092 prefixEnd_3933092 := by exact prefixLift 3933092
  have htrace : WordTrace (prefixWord ++ tailWord_3933092) baseStart_3933092 baseEnd_3933092 := by
    simpa [prefixWord, tailWord_3933092, baseEnd_3933092] using wordTrace_append hprefix tailTrace_3933092
  have hstable : (prefixWord ++ tailWord_3933092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3933092).length < 2 ^ (prefixWord ++ tailWord_3933092).sum := by decide
  have hdescent : baseEnd_3933092 < baseStart_3933092 := by decide
  rcases family_descends (prefixWord ++ tailWord_3933092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3933109 : List Nat := [1, 3, 3, 2, 1, 1, 4, 1, 1, 3, 3]
def baseStart_3933109 : Nat := 118140960795 + 3933109 * 2 ^ 59
def prefixEnd_3933109 : Nat := 4983230072969 + 3 ^ 40 * 3933109 * 2
def baseEnd_3933109 : Nat := 2019575383524557426649467

theorem tailTrace_3933109 : CollatzResearch.WordTrace tailWord_3933109 prefixEnd_3933109 2019575383524557426649467 := by
  unfold tailWord_3933109
  simp only [CollatzResearch.WordTrace]
  refine ⟨143452270308025289383826381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95634846872016859589217587 143452270308025289383826381)
  ·
    refine ⟨53794601365509483518934893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143452270308025289383826381 53794601365509483518934893)
    ·
      refine ⟨20172975512066056319600585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53794601365509483518934893 20172975512066056319600585)
      ·
        refine ⟨15129731634049542239700439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20172975512066056319600585 15129731634049542239700439)
        ·
          refine ⟨22694597451074313359550659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15129731634049542239700439 22694597451074313359550659)
          ·
            refine ⟨34041896176611470039325989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22694597451074313359550659 34041896176611470039325989)
            ·
              refine ⟨6382855533114650632373623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34041896176611470039325989 6382855533114650632373623)
              ·
                refine ⟨9574283299671975948560435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6382855533114650632373623 9574283299671975948560435)
                ·
                  refine ⟨14361424949507963922840653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9574283299671975948560435 14361424949507963922840653)
                  ·
                    refine ⟨5385534356065486471065245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14361424949507963922840653 5385534356065486471065245)
                    ·
                      refine ⟨2019575383524557426649467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5385534356065486471065245 2019575383524557426649467)
                      ·
                        rfl

theorem cell23_3933109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 4, 1, 1, 3, 3].length) (baseStart_3933109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3933109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3933109 prefixEnd_3933109 := by exact prefixLift 3933109
  have htrace : WordTrace (prefixWord ++ tailWord_3933109) baseStart_3933109 baseEnd_3933109 := by
    simpa [prefixWord, tailWord_3933109, baseEnd_3933109] using wordTrace_append hprefix tailTrace_3933109
  have hstable : (prefixWord ++ tailWord_3933109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3933109).length < 2 ^ (prefixWord ++ tailWord_3933109).sum := by decide
  have hdescent : baseEnd_3933109 < baseStart_3933109 := by decide
  rcases family_descends (prefixWord ++ tailWord_3933109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3933115 : List Nat := [1, 1, 1, 1, 1, 2, 2, 2, 3, 5, 4]
def baseStart_3933115 : Nat := 118140960795 + 3933115 * 2 ^ 59
def prefixEnd_3933115 : Nat := 4983230072969 + 3 ^ 40 * 3933115 * 2
def baseEnd_3933115 : Nat := 2019578464408484403174439

theorem tailTrace_3933115 : CollatzResearch.WordTrace tailWord_3933115 prefixEnd_3933115 2019578464408484403174439 := by
  unfold tailWord_3933115
  simp only [CollatzResearch.WordTrace]
  refine ⟨143452489146003552408544799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95634992764002368272363199 143452489146003552408544799)
  ·
    refine ⟨215178733719005328612817199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143452489146003552408544799 215178733719005328612817199)
    ·
      refine ⟨322768100578507992919225799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215178733719005328612817199 322768100578507992919225799)
      ·
        refine ⟨484152150867761989378838699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 322768100578507992919225799 484152150867761989378838699)
        ·
          refine ⟨726228226301642984068258049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 484152150867761989378838699 726228226301642984068258049)
          ·
            refine ⟨544671169726232238051193537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 726228226301642984068258049 544671169726232238051193537)
            ·
              refine ⟨408503377294674178538395153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 544671169726232238051193537 408503377294674178538395153)
              ·
                refine ⟨306377532971005633903796365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 408503377294674178538395153 306377532971005633903796365)
                ·
                  refine ⟨114891574864127112713923637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 306377532971005633903796365 114891574864127112713923637)
                  ·
                    refine ⟨10771085143511916816930341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 114891574864127112713923637 10771085143511916816930341)
                    ·
                      refine ⟨2019578464408484403174439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10771085143511916816930341 2019578464408484403174439)
                      ·
                        rfl

theorem cell23_3933115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 5, 4].length) (baseStart_3933115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3933115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3933115 prefixEnd_3933115 := by exact prefixLift 3933115
  have htrace : WordTrace (prefixWord ++ tailWord_3933115) baseStart_3933115 baseEnd_3933115 := by
    simpa [prefixWord, tailWord_3933115, baseEnd_3933115] using wordTrace_append hprefix tailTrace_3933115
  have hstable : (prefixWord ++ tailWord_3933115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3933115).length < 2 ^ (prefixWord ++ tailWord_3933115).sum := by decide
  have hdescent : baseEnd_3933115 < baseStart_3933115 := by decide
  rcases family_descends (prefixWord ++ tailWord_3933115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3933170 : List Nat := [3, 2, 1, 5, 1, 1, 2, 2, 1, 3, 2]
def baseStart_3933170 : Nat := 118140960795 + 3933170 * 2 ^ 59
def prefixEnd_3933170 : Nat := 4983230072969 + 3 ^ 40 * 3933170 * 2
def baseEnd_3933170 : Nat := 2019606705844481687986687

theorem tailTrace_3933170 : CollatzResearch.WordTrace tailWord_3933170 prefixEnd_3933170 2019606705844481687986687 := by
  unfold tailWord_3933170
  simp only [CollatzResearch.WordTrace]
  refine ⟨35863623790201074200449241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95636330107202864534531309 35863623790201074200449241)
  ·
    refine ⟨26897717842650805650336931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35863623790201074200449241 26897717842650805650336931)
    ·
      refine ⟨40346576763976208475505397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26897717842650805650336931 40346576763976208475505397)
      ·
        refine ⟨3782491571622769544578631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 40346576763976208475505397 3782491571622769544578631)
        ·
          refine ⟨5673737357434154316867947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3782491571622769544578631 5673737357434154316867947)
          ·
            refine ⟨8510606036151231475301921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5673737357434154316867947 8510606036151231475301921)
            ·
              refine ⟨6382954527113423606476441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8510606036151231475301921 6382954527113423606476441)
              ·
                refine ⟨4787215895335067704857331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6382954527113423606476441 4787215895335067704857331)
                ·
                  refine ⟨7180823843002601557285997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4787215895335067704857331 7180823843002601557285997)
                  ·
                    refine ⟨2692808941125975583982249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7180823843002601557285997 2692808941125975583982249)
                    ·
                      refine ⟨2019606705844481687986687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2692808941125975583982249 2019606705844481687986687)
                      ·
                        rfl

theorem cell23_3933170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 2, 2, 1, 3, 2].length) (baseStart_3933170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3933170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3933170 prefixEnd_3933170 := by exact prefixLift 3933170
  have htrace : WordTrace (prefixWord ++ tailWord_3933170) baseStart_3933170 baseEnd_3933170 := by
    simpa [prefixWord, tailWord_3933170, baseEnd_3933170] using wordTrace_append hprefix tailTrace_3933170
  have hstable : (prefixWord ++ tailWord_3933170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3933170).length < 2 ^ (prefixWord ++ tailWord_3933170).sum := by decide
  have hdescent : baseEnd_3933170 < baseStart_3933170 := by decide
  rcases family_descends (prefixWord ++ tailWord_3933170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3933236 : List Nat := [2, 5, 1, 2, 1, 1, 1, 3, 2, 5]
def baseStart_3933236 : Nat := 118140960795 + 3933236 * 2 ^ 59
def prefixEnd_3933236 : Nat := 4983230072969 + 3 ^ 40 * 3933236 * 2
def baseEnd_3933236 : Nat := 673213531855892809920461

theorem tailTrace_3933236 : CollatzResearch.WordTrace tailWord_3933236 prefixEnd_3933236 673213531855892809920461 := by
  unfold tailWord_3933236
  simp only [CollatzResearch.WordTrace]
  refine ⟨71728451189282595036849781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95637934919043460049133041 71728451189282595036849781)
  ·
    refine ⟨6724542298995243284704667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 71728451189282595036849781 6724542298995243284704667)
    ·
      refine ⟨10086813448492864927057001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6724542298995243284704667 10086813448492864927057001)
      ·
        refine ⟨7565110086369648695292751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10086813448492864927057001 7565110086369648695292751)
        ·
          refine ⟨11347665129554473042939127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7565110086369648695292751 11347665129554473042939127)
          ·
            refine ⟨17021497694331709564408691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11347665129554473042939127 17021497694331709564408691)
            ·
              refine ⟨25532246541497564346613037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17021497694331709564408691 25532246541497564346613037)
              ·
                refine ⟨9574592453061586629979889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25532246541497564346613037 9574592453061586629979889)
                ·
                  refine ⟨7180944339796189972484917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9574592453061586629979889 7180944339796189972484917)
                  ·
                    refine ⟨673213531855892809920461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7180944339796189972484917 673213531855892809920461)
                    ·
                      rfl

theorem cell23_3933236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 3, 2, 5].length) (baseStart_3933236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3933236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3933236 prefixEnd_3933236 := by exact prefixLift 3933236
  have htrace : WordTrace (prefixWord ++ tailWord_3933236) baseStart_3933236 baseEnd_3933236 := by
    simpa [prefixWord, tailWord_3933236, baseEnd_3933236] using wordTrace_append hprefix tailTrace_3933236
  have hstable : (prefixWord ++ tailWord_3933236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3933236).length < 2 ^ (prefixWord ++ tailWord_3933236).sum := by decide
  have hdescent : baseEnd_3933236 < baseStart_3933236 := by decide
  rcases family_descends (prefixWord ++ tailWord_3933236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3933239 : List Nat := [1, 1, 3, 1, 2, 2, 1, 2, 4, 4, 2]
def baseStart_3933239 : Nat := 118140960795 + 3933239 * 2 ^ 59
def prefixEnd_3933239 : Nat := 4983230072969 + 3 ^ 40 * 3933239 * 2
def baseEnd_3933239 : Nat := 2019642136009641918023869

theorem tailTrace_3933239 : CollatzResearch.WordTrace tailWord_3933239 prefixEnd_3933239 2019642136009641918023869 := by
  unfold tailWord_3933239
  simp only [CollatzResearch.WordTrace]
  refine ⟨143457011797554321586058771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95638007865036214390705847 143457011797554321586058771)
  ·
    refine ⟨215185517696331482379088157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143457011797554321586058771 215185517696331482379088157)
    ·
      refine ⟨80694569136124305892158059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 215185517696331482379088157 80694569136124305892158059)
      ·
        refine ⟨121041853704186458838237089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80694569136124305892158059 121041853704186458838237089)
        ·
          refine ⟨90781390278139844128677817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121041853704186458838237089 90781390278139844128677817)
          ·
            refine ⟨68086042708604883096508363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90781390278139844128677817 68086042708604883096508363)
            ·
              refine ⟨102129064062907324644762545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68086042708604883096508363 102129064062907324644762545)
              ·
                refine ⟨76596798047180493483571909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102129064062907324644762545 76596798047180493483571909)
                ·
                  refine ⟨14361899633846342528169733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 76596798047180493483571909 14361899633846342528169733)
                  ·
                    refine ⟨2692856181346189224031825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14361899633846342528169733 2692856181346189224031825)
                    ·
                      refine ⟨2019642136009641918023869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2692856181346189224031825 2019642136009641918023869)
                      ·
                        rfl

theorem cell23_3933239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 2, 4, 4, 2].length) (baseStart_3933239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3933239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3933239 prefixEnd_3933239 := by exact prefixLift 3933239
  have htrace : WordTrace (prefixWord ++ tailWord_3933239) baseStart_3933239 baseEnd_3933239 := by
    simpa [prefixWord, tailWord_3933239, baseEnd_3933239] using wordTrace_append hprefix tailTrace_3933239
  have hstable : (prefixWord ++ tailWord_3933239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3933239).length < 2 ^ (prefixWord ++ tailWord_3933239).sum := by decide
  have hdescent : baseEnd_3933239 < baseStart_3933239 := by decide
  rcases family_descends (prefixWord ++ tailWord_3933239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3933293 : List Nat := [1, 5, 1, 1, 2, 4, 1, 1, 2, 2, 3]
def baseStart_3933293 : Nat := 118140960795 + 3933293 * 2 ^ 59
def prefixEnd_3933293 : Nat := 4983230072969 + 3 ^ 40 * 3933293 * 2
def baseEnd_3933293 : Nat := 2019669863964984706748621

theorem tailTrace_3933293 : CollatzResearch.WordTrace tailWord_3933293 prefixEnd_3933293 2019669863964984706748621 := by
  unfold tailWord_3933293
  simp only [CollatzResearch.WordTrace]
  refine ⟨143458981339358688808524533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95639320892905792539016355 143458981339358688808524533)
  ·
    refine ⟨13449279500564877075799175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 143458981339358688808524533 13449279500564877075799175)
    ·
      refine ⟨20173919250847315613698763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13449279500564877075799175 20173919250847315613698763)
      ·
        refine ⟨30260878876270973420548145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20173919250847315613698763 30260878876270973420548145)
        ·
          refine ⟨22695659157203230065411109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30260878876270973420548145 22695659157203230065411109)
          ·
            refine ⟨4255436091975605637264583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22695659157203230065411109 4255436091975605637264583)
            ·
              refine ⟨6383154137963408455896875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4255436091975605637264583 6383154137963408455896875)
              ·
                refine ⟨9574731206945112683845313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6383154137963408455896875 9574731206945112683845313)
                ·
                  refine ⟨7181048405208834512883985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9574731206945112683845313 7181048405208834512883985)
                  ·
                    refine ⟨5385786303906625884662989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7181048405208834512883985 5385786303906625884662989)
                    ·
                      refine ⟨2019669863964984706748621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5385786303906625884662989 2019669863964984706748621)
                      ·
                        rfl

theorem cell23_3933293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 1, 1, 2, 2, 3].length) (baseStart_3933293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3933293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3933293 prefixEnd_3933293 := by exact prefixLift 3933293
  have htrace : WordTrace (prefixWord ++ tailWord_3933293) baseStart_3933293 baseEnd_3933293 := by
    simpa [prefixWord, tailWord_3933293, baseEnd_3933293] using wordTrace_append hprefix tailTrace_3933293
  have hstable : (prefixWord ++ tailWord_3933293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3933293).length < 2 ^ (prefixWord ++ tailWord_3933293).sum := by decide
  have hdescent : baseEnd_3933293 < baseStart_3933293 := by decide
  rcases family_descends (prefixWord ++ tailWord_3933293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3933343 : List Nat := [1, 1, 2, 6, 2, 1, 2, 2, 1, 5]
def baseStart_3933343 : Nat := 118140960795 + 3933343 * 2 ^ 59
def prefixEnd_3933343 : Nat := 4983230072969 + 3 ^ 40 * 3933343 * 2
def baseEnd_3933343 : Nat := 673231845999236503707797

theorem tailTrace_3933343 : CollatzResearch.WordTrace tailWord_3933343 prefixEnd_3933343 673231845999236503707797 := by
  unfold tailWord_3933343
  simp only [CollatzResearch.WordTrace]
  refine ⟨143460804989177547347844683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95640536659451698231896455 143460804989177547347844683)
  ·
    refine ⟨215191207483766321021767025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143460804989177547347844683 215191207483766321021767025)
    ·
      refine ⟨161393405612824740766325269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215191207483766321021767025 161393405612824740766325269)
      ·
        refine ⟨7565315888101159723421497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 161393405612824740766325269 7565315888101159723421497)
        ·
          refine ⟨5673986916075869792566123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7565315888101159723421497 5673986916075869792566123)
          ·
            refine ⟨8510980374113804688849185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5673986916075869792566123 8510980374113804688849185)
            ·
              refine ⟨6383235280585353516636889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8510980374113804688849185 6383235280585353516636889)
              ·
                refine ⟨4787426460439015137477667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6383235280585353516636889 4787426460439015137477667)
                ·
                  refine ⟨7181139690658522706216501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4787426460439015137477667 7181139690658522706216501)
                  ·
                    refine ⟨673231845999236503707797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7181139690658522706216501 673231845999236503707797)
                    ·
                      rfl

theorem cell23_3933343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 2, 2, 1, 5].length) (baseStart_3933343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3933343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3933343 prefixEnd_3933343 := by exact prefixLift 3933343
  have htrace : WordTrace (prefixWord ++ tailWord_3933343) baseStart_3933343 baseEnd_3933343 := by
    simpa [prefixWord, tailWord_3933343, baseEnd_3933343] using wordTrace_append hprefix tailTrace_3933343
  have hstable : (prefixWord ++ tailWord_3933343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3933343).length < 2 ^ (prefixWord ++ tailWord_3933343).sum := by decide
  have hdescent : baseEnd_3933343 < baseStart_3933343 := by decide
  rcases family_descends (prefixWord ++ tailWord_3933343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3933359 : List Nat := [1, 1, 2, 1, 2, 3, 2, 4, 1, 2, 4]
def baseStart_3933359 : Nat := 118140960795 + 3933359 * 2 ^ 59
def prefixEnd_3933359 : Nat := 4983230072969 + 3 ^ 40 * 3933359 * 2
def baseEnd_3933359 : Nat := 2019703753688181448523317

theorem tailTrace_3933359 : CollatzResearch.WordTrace tailWord_3933359 prefixEnd_3933359 2019703753688181448523317 := by
  unfold tailWord_3933359
  simp only [CollatzResearch.WordTrace]
  refine ⟨143461388557119582080427131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95640925704746388053618087 143461388557119582080427131)
  ·
    refine ⟨215192082835679373120640697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143461388557119582080427131 215192082835679373120640697)
    ·
      refine ⟨161394062126759529840480523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215192082835679373120640697 161394062126759529840480523)
      ·
        refine ⟨242091093190139294760720785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161394062126759529840480523 242091093190139294760720785)
        ·
          refine ⟨181568319892604471070540589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 242091093190139294760720785 181568319892604471070540589)
          ·
            refine ⟨68088119959726676651452721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 181568319892604471070540589 68088119959726676651452721)
            ·
              refine ⟨51066089969795007488589541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68088119959726676651452721 51066089969795007488589541)
              ·
                refine ⟨9574891869336563904110539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51066089969795007488589541 9574891869336563904110539)
                ·
                  refine ⟨14362337804004845856165809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9574891869336563904110539 14362337804004845856165809)
                  ·
                    refine ⟨10771753353003634392124357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14362337804004845856165809 10771753353003634392124357)
                    ·
                      refine ⟨2019703753688181448523317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10771753353003634392124357 2019703753688181448523317)
                      ·
                        rfl

theorem cell23_3933359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 4, 1, 2, 4].length) (baseStart_3933359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3933359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3933359 prefixEnd_3933359 := by exact prefixLift 3933359
  have htrace : WordTrace (prefixWord ++ tailWord_3933359) baseStart_3933359 baseEnd_3933359 := by
    simpa [prefixWord, tailWord_3933359, baseEnd_3933359] using wordTrace_append hprefix tailTrace_3933359
  have hstable : (prefixWord ++ tailWord_3933359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3933359).length < 2 ^ (prefixWord ++ tailWord_3933359).sum := by decide
  have hdescent : baseEnd_3933359 < baseStart_3933359 := by decide
  rcases family_descends (prefixWord ++ tailWord_3933359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3933369 : List Nat := [1, 2, 1, 4, 1, 5, 9]
def baseStart_3933369 : Nat := 118140960795 + 3933369 * 2 ^ 59
def prefixEnd_3933369 : Nat := 4983230072969 + 3 ^ 40 * 3933369 * 2
def baseEnd_3933369 : Nat := 24934677635737363078991

theorem tailTrace_3933369 : CollatzResearch.WordTrace tailWord_3933369 prefixEnd_3933369 24934677635737363078991 := by
  unfold tailWord_3933369
  simp only [CollatzResearch.WordTrace]
  refine ⟨143461753287083353788291161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95641168858055569192194107 143461753287083353788291161)
  ·
    refine ⟨107596314965312515341218371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143461753287083353788291161 107596314965312515341218371)
    ·
      refine ⟨161394472447968773011827557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107596314965312515341218371 161394472447968773011827557)
      ·
        refine ⟨30261463583994144939717667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 161394472447968773011827557 30261463583994144939717667)
        ·
          refine ⟨45392195375991217409576501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30261463583994144939717667 45392195375991217409576501)
          ·
            refine ⟨4255518316499176632147797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 45392195375991217409576501 4255518316499176632147797)
            ·
              refine ⟨24934677635737363078991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4255518316499176632147797 24934677635737363078991)
              ·
                rfl

theorem cell23_3933369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 9].length) (baseStart_3933369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3933369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3933369 prefixEnd_3933369 := by exact prefixLift 3933369
  have htrace : WordTrace (prefixWord ++ tailWord_3933369) baseStart_3933369 baseEnd_3933369 := by
    simpa [prefixWord, tailWord_3933369, baseEnd_3933369] using wordTrace_append hprefix tailTrace_3933369
  have hstable : (prefixWord ++ tailWord_3933369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3933369).length < 2 ^ (prefixWord ++ tailWord_3933369).sum := by decide
  have hdescent : baseEnd_3933369 < baseStart_3933369 := by decide
  rcases family_descends (prefixWord ++ tailWord_3933369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3933379 : List Nat := [1, 1, 1, 3, 1, 1, 1, 3, 5, 3, 3]
def baseStart_3933379 : Nat := 118140960795 + 3933379 * 2 ^ 59
def prefixEnd_3933379 : Nat := 4983230072969 + 3 ^ 40 * 3933379 * 2
def baseEnd_3933379 : Nat := 2019714023301271370273225

theorem tailTrace_3933379 : CollatzResearch.WordTrace tailWord_3933379 prefixEnd_3933379 2019714023301271370273225 := by
  unfold tailWord_3933379
  simp only [CollatzResearch.WordTrace]
  refine ⟨143462118017047125496155191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95641412011364750330770127 143462118017047125496155191)
  ·
    refine ⟨215193177025570688244232787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143462118017047125496155191 215193177025570688244232787)
    ·
      refine ⟨322789765538356032366349181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215193177025570688244232787 322789765538356032366349181)
      ·
        refine ⟨121046162076883512137380943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 322789765538356032366349181 121046162076883512137380943)
        ·
          refine ⟨181569243115325268206071415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121046162076883512137380943 181569243115325268206071415)
          ·
            refine ⟨272353864672987902309107123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181569243115325268206071415 272353864672987902309107123)
            ·
              refine ⟨408530797009481853463660685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 272353864672987902309107123 408530797009481853463660685)
              ·
                refine ⟨153199048878555695048872757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 408530797009481853463660685 153199048878555695048872757)
                ·
                  refine ⟨14362410832364596410831821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 153199048878555695048872757 14362410832364596410831821)
                  ·
                    refine ⟨5385904062136723654061933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14362410832364596410831821 5385904062136723654061933)
                    ·
                      refine ⟨2019714023301271370273225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5385904062136723654061933 2019714023301271370273225)
                      ·
                        rfl

theorem cell23_3933379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 3, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 3, 5, 3, 3].length) (baseStart_3933379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3933379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3933379 prefixEnd_3933379 := by exact prefixLift 3933379
  have htrace : WordTrace (prefixWord ++ tailWord_3933379) baseStart_3933379 baseEnd_3933379 := by
    simpa [prefixWord, tailWord_3933379, baseEnd_3933379] using wordTrace_append hprefix tailTrace_3933379
  have hstable : (prefixWord ++ tailWord_3933379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3933379).length < 2 ^ (prefixWord ++ tailWord_3933379).sum := by decide
  have hdescent : baseEnd_3933379 < baseStart_3933379 := by decide
  rcases family_descends (prefixWord ++ tailWord_3933379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3933400 : List Nat := [2, 1, 2, 2, 5, 2, 1, 2, 1, 2, 3]
def baseStart_3933400 : Nat := 118140960795 + 3933400 * 2 ^ 59
def prefixEnd_3933400 : Nat := 4983230072969 + 3 ^ 40 * 3933400 * 2
def baseEnd_3933400 : Nat := 2019724806395015788110629

theorem tailTrace_3933400 : CollatzResearch.WordTrace tailWord_3933400 prefixEnd_3933400 2019724806395015788110629 := by
  unfold tailWord_3933400
  simp only [CollatzResearch.WordTrace]
  refine ⟨71731441974985523041334827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95641922633314030721779769 71731441974985523041334827)
  ·
    refine ⟨107597162962478284562002241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71731441974985523041334827 107597162962478284562002241)
    ·
      refine ⟨80697872221858713421501681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107597162962478284562002241 80697872221858713421501681)
      ·
        refine ⟨60523404166394035066126261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80697872221858713421501681 60523404166394035066126261)
        ·
          refine ⟨5674069140599440787449337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 60523404166394035066126261 5674069140599440787449337)
          ·
            refine ⟨4255551855449580590587003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5674069140599440787449337 4255551855449580590587003)
            ·
              refine ⟨6383327783174370885880505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4255551855449580590587003 6383327783174370885880505)
              ·
                refine ⟨4787495837380778164410379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6383327783174370885880505 4787495837380778164410379)
                ·
                  refine ⟨7181243756071167246615569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4787495837380778164410379 7181243756071167246615569)
                  ·
                    refine ⟨5385932817053375434961677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7181243756071167246615569 5385932817053375434961677)
                    ·
                      refine ⟨2019724806395015788110629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5385932817053375434961677 2019724806395015788110629)
                      ·
                        rfl

theorem cell23_3933400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 1, 2, 1, 2, 3].length) (baseStart_3933400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3933400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3933400 prefixEnd_3933400 := by exact prefixLift 3933400
  have htrace : WordTrace (prefixWord ++ tailWord_3933400) baseStart_3933400 baseEnd_3933400 := by
    simpa [prefixWord, tailWord_3933400, baseEnd_3933400] using wordTrace_append hprefix tailTrace_3933400
  have hstable : (prefixWord ++ tailWord_3933400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3933400).length < 2 ^ (prefixWord ++ tailWord_3933400).sum := by decide
  have hdescent : baseEnd_3933400 < baseStart_3933400 := by decide
  rcases family_descends (prefixWord ++ tailWord_3933400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3933413 : List Nat := [1, 3, 1, 4, 3, 1, 1, 2, 1, 3, 3]
def baseStart_3933413 : Nat := 118140960795 + 3933413 * 2 ^ 59
def prefixEnd_3933413 : Nat := 4983230072969 + 3 ^ 40 * 3933413 * 2
def baseEnd_3933413 : Nat := 2019731481643524237248069

theorem tailTrace_3933413 : CollatzResearch.WordTrace tailWord_3933413 prefixEnd_3933413 2019731481643524237248069 := by
  unfold tailWord_3933413
  simp only [CollatzResearch.WordTrace]
  refine ⟨143463358098923949302892893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95642238732615966201928595 143463358098923949302892893)
  ·
    refine ⟨53798759287096480988584835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143463358098923949302892893 53798759287096480988584835)
    ·
      refine ⟨80698138930644721482877253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53798759287096480988584835 80698138930644721482877253)
      ·
        refine ⟨15130901049495885278039485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80698138930644721482877253 15130901049495885278039485)
        ·
          refine ⟨5674087893560956979264807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15130901049495885278039485 5674087893560956979264807)
          ·
            refine ⟨8511131840341435468897211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5674087893560956979264807 8511131840341435468897211)
            ·
              refine ⟨12766697760512153203345817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8511131840341435468897211 12766697760512153203345817)
              ·
                refine ⟨9575023320384114902509363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12766697760512153203345817 9575023320384114902509363)
                ·
                  refine ⟨14362534980576172353764045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9575023320384114902509363 14362534980576172353764045)
                  ·
                    refine ⟨5385950617716064632661517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14362534980576172353764045 5385950617716064632661517)
                    ·
                      refine ⟨2019731481643524237248069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5385950617716064632661517 2019731481643524237248069)
                      ·
                        rfl

theorem cell23_3933413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 1, 2, 1, 3, 3].length) (baseStart_3933413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3933413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3933413 prefixEnd_3933413 := by exact prefixLift 3933413
  have htrace : WordTrace (prefixWord ++ tailWord_3933413) baseStart_3933413 baseEnd_3933413 := by
    simpa [prefixWord, tailWord_3933413, baseEnd_3933413] using wordTrace_append hprefix tailTrace_3933413
  have hstable : (prefixWord ++ tailWord_3933413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3933413).length < 2 ^ (prefixWord ++ tailWord_3933413).sum := by decide
  have hdescent : baseEnd_3933413 < baseStart_3933413 := by decide
  rcases family_descends (prefixWord ++ tailWord_3933413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3933474 : List Nat := [3, 3, 1, 1, 4, 2, 2, 1, 1, 3, 2]
def baseStart_3933474 : Nat := 118140960795 + 3933474 * 2 ^ 59
def prefixEnd_3933474 : Nat := 4983230072969 + 3 ^ 40 * 3933474 * 2
def baseEnd_3933474 : Nat := 2019762803963448498585289

theorem tailTrace_3933474 : CollatzResearch.WordTrace tailWord_3933474 prefixEnd_3933474 2019762803963448498585289 := by
  unfold tailWord_3933474
  simp only [CollatzResearch.WordTrace]
  refine ⟨35866395737925739180215869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95643721967801971147242317 35866395737925739180215869)
  ·
    refine ⟨13449898401722152192580951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35866395737925739180215869 13449898401722152192580951)
    ·
      refine ⟨20174847602583228288871427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13449898401722152192580951 20174847602583228288871427)
      ·
        refine ⟨30262271403874842433307141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20174847602583228288871427 30262271403874842433307141)
        ·
          refine ⟨5674175888226532956245089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30262271403874842433307141 5674175888226532956245089)
          ·
            refine ⟨4255631916169899717183817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5674175888226532956245089 4255631916169899717183817)
            ·
              refine ⟨3191723937127424787887863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4255631916169899717183817 3191723937127424787887863)
              ·
                refine ⟨4787585905691137181831795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3191723937127424787887863 4787585905691137181831795)
                ·
                  refine ⟨7181378858536705772747693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4787585905691137181831795 7181378858536705772747693)
                  ·
                    refine ⟨2693017071951264664780385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7181378858536705772747693 2693017071951264664780385)
                    ·
                      refine ⟨2019762803963448498585289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2693017071951264664780385 2019762803963448498585289)
                      ·
                        rfl

theorem cell23_3933474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 2, 1, 1, 3, 2].length) (baseStart_3933474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3933474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3933474 prefixEnd_3933474 := by exact prefixLift 3933474
  have htrace : WordTrace (prefixWord ++ tailWord_3933474) baseStart_3933474 baseEnd_3933474 := by
    simpa [prefixWord, tailWord_3933474, baseEnd_3933474] using wordTrace_append hprefix tailTrace_3933474
  have hstable : (prefixWord ++ tailWord_3933474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3933474).length < 2 ^ (prefixWord ++ tailWord_3933474).sum := by decide
  have hdescent : baseEnd_3933474 < baseStart_3933474 := by decide
  rcases family_descends (prefixWord ++ tailWord_3933474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3933493 : List Nat := [1, 3, 3, 1, 2, 2, 2, 4, 5]
def baseStart_3933493 : Nat := 118140960795 + 3933493 * 2 ^ 59
def prefixEnd_3933493 : Nat := 4983230072969 + 3 ^ 40 * 3933493 * 2
def baseEnd_3933493 : Nat := 224419173343987102694189

theorem tailTrace_3933493 : CollatzResearch.WordTrace tailWord_3933493 prefixEnd_3933493 224419173343987102694189 := by
  unfold tailWord_3933493
  simp only [CollatzResearch.WordTrace]
  refine ⟨143466275938634122965805133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95644183959089415310536755 143466275938634122965805133)
  ·
    refine ⟨53799853476987796112176925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143466275938634122965805133 53799853476987796112176925)
    ·
      refine ⟨20174945053870423542066347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53799853476987796112176925 20174945053870423542066347)
      ·
        refine ⟨30262417580805635313099521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20174945053870423542066347 30262417580805635313099521)
        ·
          refine ⟨22696813185604226484824641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30262417580805635313099521 22696813185604226484824641)
          ·
            refine ⟨17022609889203169863618481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22696813185604226484824641 17022609889203169863618481)
            ·
              refine ⟨12766957416902377397713861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17022609889203169863618481 12766957416902377397713861)
              ·
                refine ⟨2393804515669195762071349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12766957416902377397713861 2393804515669195762071349)
                ·
                  refine ⟨224419173343987102694189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2393804515669195762071349 224419173343987102694189)
                  ·
                    rfl

theorem cell23_3933493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 2, 4, 5].length) (baseStart_3933493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3933493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3933493 prefixEnd_3933493 := by exact prefixLift 3933493
  have htrace : WordTrace (prefixWord ++ tailWord_3933493) baseStart_3933493 baseEnd_3933493 := by
    simpa [prefixWord, tailWord_3933493, baseEnd_3933493] using wordTrace_append hprefix tailTrace_3933493
  have hstable : (prefixWord ++ tailWord_3933493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3933493).length < 2 ^ (prefixWord ++ tailWord_3933493).sum := by decide
  have hdescent : baseEnd_3933493 < baseStart_3933493 := by decide
  rcases family_descends (prefixWord ++ tailWord_3933493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3933499 : List Nat := [1, 1, 1, 1, 1, 2, 1, 1, 7, 2, 5]
def baseStart_3933499 : Nat := 118140960795 + 3933499 * 2 ^ 59
def prefixEnd_3933499 : Nat := 4983230072969 + 3 ^ 40 * 3933499 * 2
def baseEnd_3933499 : Nat := 2019775640979810900772673

theorem tailTrace_3933499 : CollatzResearch.WordTrace tailWord_3933499 prefixEnd_3933499 2019775640979810900772673 := by
  unfold tailWord_3933499
  simp only [CollatzResearch.WordTrace]
  refine ⟨143466494776612385990523551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95644329851074923993682367 143466494776612385990523551)
  ·
    refine ⟨215199742164918578985785327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143466494776612385990523551 215199742164918578985785327)
    ·
      refine ⟨322799613247377868478677991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215199742164918578985785327 322799613247377868478677991)
      ·
        refine ⟨484199419871066802718016987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 322799613247377868478677991 484199419871066802718016987)
        ·
          refine ⟨726299129806600204077025481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 484199419871066802718016987 726299129806600204077025481)
          ·
            refine ⟨544724347354950153057769111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 726299129806600204077025481 544724347354950153057769111)
            ·
              refine ⟨817086521032425229586653667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 544724347354950153057769111 817086521032425229586653667)
              ·
                refine ⟨1225629781548637844379980501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 817086521032425229586653667 1225629781548637844379980501)
                ·
                  refine ⟨28725698005046199477655793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1225629781548637844379980501 28725698005046199477655793)
                  ·
                    refine ⟨21544273503784649608241845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28725698005046199477655793 21544273503784649608241845)
                    ·
                      refine ⟨2019775640979810900772673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21544273503784649608241845 2019775640979810900772673)
                      ·
                        rfl

theorem cell23_3933499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 7, 2, 5].length) (baseStart_3933499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3933499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3933499 prefixEnd_3933499 := by exact prefixLift 3933499
  have htrace : WordTrace (prefixWord ++ tailWord_3933499) baseStart_3933499 baseEnd_3933499 := by
    simpa [prefixWord, tailWord_3933499, baseEnd_3933499] using wordTrace_append hprefix tailTrace_3933499
  have hstable : (prefixWord ++ tailWord_3933499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3933499).length < 2 ^ (prefixWord ++ tailWord_3933499).sum := by decide
  have hdescent : baseEnd_3933499 < baseStart_3933499 := by decide
  rcases family_descends (prefixWord ++ tailWord_3933499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3933550 : List Nat := [4, 1, 2, 4, 1, 1, 1, 1, 1, 2, 5]
def baseStart_3933550 : Nat := 118140960795 + 3933550 * 2 ^ 59
def prefixEnd_3933550 : Nat := 4983230072969 + 3 ^ 40 * 3933550 * 2
def baseEnd_3933550 : Nat := 2019801828493190201234939

theorem tailTrace_3933550 : CollatzResearch.WordTrace tailWord_3933550 prefixEnd_3933550 2019801828493190201234939 := by
  unfold tailWord_3933550
  simp only [CollatzResearch.WordTrace]
  refine ⟨17933544362428452712578763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95645569932951747800420069 17933544362428452712578763)
  ·
    refine ⟨26900316543642679068868145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17933544362428452712578763 26900316543642679068868145)
    ·
      refine ⟨20175237407732009301651109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26900316543642679068868145 20175237407732009301651109)
      ·
        refine ⟨3782857013949751744059583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20175237407732009301651109 3782857013949751744059583)
        ·
          refine ⟨5674285520924627616089375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3782857013949751744059583 5674285520924627616089375)
          ·
            refine ⟨8511428281386941424134063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5674285520924627616089375 8511428281386941424134063)
            ·
              refine ⟨12767142422080412136201095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8511428281386941424134063 12767142422080412136201095)
              ·
                refine ⟨19150713633120618204301643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12767142422080412136201095 19150713633120618204301643)
                ·
                  refine ⟨28726070449680927306452465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19150713633120618204301643 28726070449680927306452465)
                  ·
                    refine ⟨21544552837260695479839349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28726070449680927306452465 21544552837260695479839349)
                    ·
                      refine ⟨2019801828493190201234939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21544552837260695479839349 2019801828493190201234939)
                      ·
                        rfl

theorem cell23_3933550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 1, 1, 1, 2, 5].length) (baseStart_3933550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3933550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3933550 prefixEnd_3933550 := by exact prefixLift 3933550
  have htrace : WordTrace (prefixWord ++ tailWord_3933550) baseStart_3933550 baseEnd_3933550 := by
    simpa [prefixWord, tailWord_3933550, baseEnd_3933550] using wordTrace_append hprefix tailTrace_3933550
  have hstable : (prefixWord ++ tailWord_3933550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3933550).length < 2 ^ (prefixWord ++ tailWord_3933550).sum := by decide
  have hdescent : baseEnd_3933550 < baseStart_3933550 := by decide
  rcases family_descends (prefixWord ++ tailWord_3933550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3933553 : List Nat := [1, 2, 2, 2, 1, 2, 5, 1, 3, 4]
def baseStart_3933553 : Nat := 118140960795 + 3933553 * 2 ^ 59
def prefixEnd_3933553 : Nat := 4983230072969 + 3 ^ 40 * 3933553 * 2
def baseEnd_3933553 : Nat := 673267789645051229832475

theorem tailTrace_3933553 : CollatzResearch.WordTrace tailWord_3933553 prefixEnd_3933553 673267789645051229832475 := by
  unfold tailWord_3933553
  simp only [CollatzResearch.WordTrace]
  refine ⟨143468464318416753212989313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95645642878944502141992875 143468464318416753212989313)
  ·
    refine ⟨107601348238812564909741985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143468464318416753212989313 107601348238812564909741985)
    ·
      refine ⟨80701011179109423682306489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107601348238812564909741985 80701011179109423682306489)
      ·
        refine ⟨60525758384332067761729867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80701011179109423682306489 60525758384332067761729867)
        ·
          refine ⟨90788637576498101642594801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60525758384332067761729867 90788637576498101642594801)
          ·
            refine ⟨68091478182373576231946101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90788637576498101642594801 68091478182373576231946101)
            ·
              refine ⟨6383576079597522771744947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 68091478182373576231946101 6383576079597522771744947)
              ·
                refine ⟨9575364119396284157617421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6383576079597522771744947 9575364119396284157617421)
                ·
                  refine ⟨3590761544773606559106533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9575364119396284157617421 3590761544773606559106533)
                  ·
                    refine ⟨673267789645051229832475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3590761544773606559106533 673267789645051229832475)
                    ·
                      rfl

theorem cell23_3933553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 5, 1, 3, 4].length) (baseStart_3933553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3933553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3933553 prefixEnd_3933553 := by exact prefixLift 3933553
  have htrace : WordTrace (prefixWord ++ tailWord_3933553) baseStart_3933553 baseEnd_3933553 := by
    simpa [prefixWord, tailWord_3933553, baseEnd_3933553] using wordTrace_append hprefix tailTrace_3933553
  have hstable : (prefixWord ++ tailWord_3933553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3933553).length < 2 ^ (prefixWord ++ tailWord_3933553).sum := by decide
  have hdescent : baseEnd_3933553 < baseStart_3933553 := by decide
  rcases family_descends (prefixWord ++ tailWord_3933553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3933644 : List Nat := [2, 2, 1, 4, 2, 2, 2, 3, 1, 1, 3]
def baseStart_3933644 : Nat := 118140960795 + 3933644 * 2 ^ 59
def prefixEnd_3933644 : Nat := 4983230072969 + 3 ^ 40 * 3933644 * 2
def baseEnd_3933644 : Nat := 2019850095674712833459507

theorem tailTrace_3933644 : CollatzResearch.WordTrace tailWord_3933644 prefixEnd_3933644 2019850095674712833459507 := by
  unfold tailWord_3933644
  simp only [CollatzResearch.WordTrace]
  refine ⟨71735891680543537877275993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95647855574058050503034657 71735891680543537877275993)
  ·
    refine ⟨53801918760407653407956995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71735891680543537877275993 53801918760407653407956995)
    ·
      refine ⟨80702878140611480111935493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53801918760407653407956995 80702878140611480111935493)
      ·
        refine ⟨15131789651364652520987905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80702878140611480111935493 15131789651364652520987905)
        ·
          refine ⟨11348842238523489390740929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15131789651364652520987905 11348842238523489390740929)
          ·
            refine ⟨8511631678892617043055697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11348842238523489390740929 8511631678892617043055697)
            ·
              refine ⟨6383723759169462782291773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8511631678892617043055697 6383723759169462782291773)
              ·
                refine ⟨2393896409688548543359415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6383723759169462782291773 2393896409688548543359415)
                ·
                  refine ⟨3590844614532822815039123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2393896409688548543359415 3590844614532822815039123)
                  ·
                    refine ⟨5386266921799234222558685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3590844614532822815039123 5386266921799234222558685)
                    ·
                      refine ⟨2019850095674712833459507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5386266921799234222558685 2019850095674712833459507)
                      ·
                        rfl

theorem cell23_3933644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 2, 3, 1, 1, 3].length) (baseStart_3933644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3933644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3933644 prefixEnd_3933644 := by exact prefixLift 3933644
  have htrace : WordTrace (prefixWord ++ tailWord_3933644) baseStart_3933644 baseEnd_3933644 := by
    simpa [prefixWord, tailWord_3933644, baseEnd_3933644] using wordTrace_append hprefix tailTrace_3933644
  have hstable : (prefixWord ++ tailWord_3933644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3933644).length < 2 ^ (prefixWord ++ tailWord_3933644).sum := by decide
  have hdescent : baseEnd_3933644 < baseStart_3933644 := by decide
  rcases family_descends (prefixWord ++ tailWord_3933644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3933653 : List Nat := [1, 3, 2, 3, 1, 1, 2, 3, 1, 1, 5]
def baseStart_3933653 : Nat := 118140960795 + 3933653 * 2 ^ 59
def prefixEnd_3933653 : Nat := 4983230072969 + 3 ^ 40 * 3933653 * 2
def baseEnd_3933653 : Nat := 2019854717000603298246965

theorem tailTrace_3933653 : CollatzResearch.WordTrace tailWord_3933653 prefixEnd_3933653 2019854717000603298246965 := by
  unfold tailWord_3933653
  simp only [CollatzResearch.WordTrace]
  refine ⟨143472111618054470291629613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95648074412036313527753075 143472111618054470291629613)
  ·
    refine ⟨53802041856770426359361105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143472111618054470291629613 53802041856770426359361105)
    ·
      refine ⟨40351531392577819769520829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53802041856770426359361105 40351531392577819769520829)
      ·
        refine ⟨15131824272216682413570311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40351531392577819769520829 15131824272216682413570311)
        ·
          refine ⟨22697736408325023620355467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15131824272216682413570311 22697736408325023620355467)
          ·
            refine ⟨34046604612487535430533201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22697736408325023620355467 34046604612487535430533201)
            ·
              refine ⟨25534953459365651572899901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34046604612487535430533201 25534953459365651572899901)
              ·
                refine ⟨9575607547262119339837463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25534953459365651572899901 9575607547262119339837463)
                ·
                  refine ⟨14363411320893179009756195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9575607547262119339837463 14363411320893179009756195)
                  ·
                    refine ⟨21545116981339768514634293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14363411320893179009756195 21545116981339768514634293)
                    ·
                      refine ⟨2019854717000603298246965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21545116981339768514634293 2019854717000603298246965)
                      ·
                        rfl

theorem cell23_3933653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 3, 1, 1, 5].length) (baseStart_3933653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3933653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3933653 prefixEnd_3933653 := by exact prefixLift 3933653
  have htrace : WordTrace (prefixWord ++ tailWord_3933653) baseStart_3933653 baseEnd_3933653 := by
    simpa [prefixWord, tailWord_3933653, baseEnd_3933653] using wordTrace_append hprefix tailTrace_3933653
  have hstable : (prefixWord ++ tailWord_3933653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3933653).length < 2 ^ (prefixWord ++ tailWord_3933653).sum := by decide
  have hdescent : baseEnd_3933653 < baseStart_3933653 := by decide
  rcases family_descends (prefixWord ++ tailWord_3933653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3933667 : List Nat := [1, 1, 1, 6, 2, 1, 1, 3, 3, 2, 2]
def baseStart_3933667 : Nat := 118140960795 + 3933667 * 2 ^ 59
def prefixEnd_3933667 : Nat := 4983230072969 + 3 ^ 40 * 3933667 * 2
def baseEnd_3933667 : Nat := 2019861905729766243471901

theorem tailTrace_3933667 : CollatzResearch.WordTrace tailWord_3933667 prefixEnd_3933667 2019861905729766243471901 := by
  unfold tailWord_3933667
  simp only [CollatzResearch.WordTrace]
  refine ⟨143472622240003750682639255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95648414826669167121759503 143472622240003750682639255)
  ·
    refine ⟨215208933360005626023958883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143472622240003750682639255 215208933360005626023958883)
    ·
      refine ⟨322813400040008439035938325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215208933360005626023958883 322813400040008439035938325)
      ·
        refine ⟨15131878126875395579809609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 322813400040008439035938325 15131878126875395579809609)
        ·
          refine ⟨11348908595156546684857207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15131878126875395579809609 11348908595156546684857207)
          ·
            refine ⟨17023362892734820027285811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11348908595156546684857207 17023362892734820027285811)
            ·
              refine ⟨25535044339102230040928717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17023362892734820027285811 25535044339102230040928717)
              ·
                refine ⟨9575641627163336265348269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25535044339102230040928717 9575641627163336265348269)
                ·
                  refine ⟨3590865610186251099505601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9575641627163336265348269 3590865610186251099505601)
                  ·
                    refine ⟨2693149207639688324629201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3590865610186251099505601 2693149207639688324629201)
                    ·
                      refine ⟨2019861905729766243471901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2693149207639688324629201 2019861905729766243471901)
                      ·
                        rfl

theorem cell23_3933667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 3, 3, 2, 2].length) (baseStart_3933667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3933667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3933667 prefixEnd_3933667 := by exact prefixLift 3933667
  have htrace : WordTrace (prefixWord ++ tailWord_3933667) baseStart_3933667 baseEnd_3933667 := by
    simpa [prefixWord, tailWord_3933667, baseEnd_3933667] using wordTrace_append hprefix tailTrace_3933667
  have hstable : (prefixWord ++ tailWord_3933667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3933667).length < 2 ^ (prefixWord ++ tailWord_3933667).sum := by decide
  have hdescent : baseEnd_3933667 < baseStart_3933667 := by decide
  rcases family_descends (prefixWord ++ tailWord_3933667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3933676 : List Nat := [2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 6]
def baseStart_3933676 : Nat := 118140960795 + 3933676 * 2 ^ 59
def prefixEnd_3933676 : Nat := 4983230072969 + 3 ^ 40 * 3933676 * 2
def baseEnd_3933676 : Nat := 2019866527055656708259359

theorem tailTrace_3933676 : CollatzResearch.WordTrace tailWord_3933676 prefixEnd_3933676 2019866527055656708259359 := by
  unfold tailWord_3933676
  simp only [CollatzResearch.WordTrace]
  refine ⟨71736475248485572609858441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95648633664647430146477921 71736475248485572609858441)
  ·
    refine ⟨53802356436364179457393831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71736475248485572609858441 53802356436364179457393831)
    ·
      refine ⟨80703534654546269186090747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53802356436364179457393831 80703534654546269186090747)
      ·
        refine ⟨121055301981819403779136121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80703534654546269186090747 121055301981819403779136121)
        ·
          refine ⟨90791476486364552834352091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121055301981819403779136121 90791476486364552834352091)
          ·
            refine ⟨136187214729546829251528137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90791476486364552834352091 136187214729546829251528137)
            ·
              refine ⟨102140411047160121938646103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136187214729546829251528137 102140411047160121938646103)
              ·
                refine ⟨153210616570740182907969155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102140411047160121938646103 153210616570740182907969155)
                ·
                  refine ⟨229815924856110274361953733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 153210616570740182907969155 229815924856110274361953733)
                  ·
                    refine ⟨43090485910520676442866325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 229815924856110274361953733 43090485910520676442866325)
                    ·
                      refine ⟨2019866527055656708259359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 43090485910520676442866325 2019866527055656708259359)
                      ·
                        rfl

theorem cell23_3933676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 6].length) (baseStart_3933676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3933676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3933676 prefixEnd_3933676 := by exact prefixLift 3933676
  have htrace : WordTrace (prefixWord ++ tailWord_3933676) baseStart_3933676 baseEnd_3933676 := by
    simpa [prefixWord, tailWord_3933676, baseEnd_3933676] using wordTrace_append hprefix tailTrace_3933676
  have hstable : (prefixWord ++ tailWord_3933676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3933676).length < 2 ^ (prefixWord ++ tailWord_3933676).sum := by decide
  have hdescent : baseEnd_3933676 < baseStart_3933676 := by decide
  rcases family_descends (prefixWord ++ tailWord_3933676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3933677 : List Nat := [1, 5, 1, 3, 2, 2, 1, 1, 1, 6]
def baseStart_3933677 : Nat := 118140960795 + 3933677 * 2 ^ 59
def prefixEnd_3933677 : Nat := 4983230072969 + 3 ^ 40 * 3933677 * 2
def baseEnd_3933677 : Nat := 673289013512103734782285

theorem tailTrace_3933677 : CollatzResearch.WordTrace tailWord_3933677 prefixEnd_3933677 673289013512103734782285 := by
  unfold tailWord_3933677
  simp only [CollatzResearch.WordTrace]
  refine ⟨143472986969967522390503285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95648657979978348260335523 143472986969967522390503285)
  ·
    refine ⟨13450592528434455224109683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 143472986969967522390503285 13450592528434455224109683)
    ·
      refine ⟨20175888792651682836164525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13450592528434455224109683 20175888792651682836164525)
      ·
        refine ⟨7565958297244381063561697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20175888792651682836164525 7565958297244381063561697)
        ·
          refine ⟨5674468722933285797671273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7565958297244381063561697 5674468722933285797671273)
          ·
            refine ⟨4255851542199964348253455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5674468722933285797671273 4255851542199964348253455)
            ·
              refine ⟨6383777313299946522380183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4255851542199964348253455 6383777313299946522380183)
              ·
                refine ⟨9575665969949919783570275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6383777313299946522380183 9575665969949919783570275)
                ·
                  refine ⟨14363498954924879675355413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9575665969949919783570275 14363498954924879675355413)
                  ·
                    refine ⟨673289013512103734782285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14363498954924879675355413 673289013512103734782285)
                    ·
                      rfl

theorem cell23_3933677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 1, 1, 1, 6].length) (baseStart_3933677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3933677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3933677 prefixEnd_3933677 := by exact prefixLift 3933677
  have htrace : WordTrace (prefixWord ++ tailWord_3933677) baseStart_3933677 baseEnd_3933677 := by
    simpa [prefixWord, tailWord_3933677, baseEnd_3933677] using wordTrace_append hprefix tailTrace_3933677
  have hstable : (prefixWord ++ tailWord_3933677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3933677).length < 2 ^ (prefixWord ++ tailWord_3933677).sum := by decide
  have hdescent : baseEnd_3933677 < baseStart_3933677 := by decide
  rcases family_descends (prefixWord ++ tailWord_3933677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3933680 : List Nat := [2, 1, 1, 1, 3, 6, 1, 1, 1, 2, 4]
def baseStart_3933680 : Nat := 118140960795 + 3933680 * 2 ^ 59
def prefixEnd_3933680 : Nat := 4983230072969 + 3 ^ 40 * 3933680 * 2
def baseEnd_3933680 : Nat := 2019868580978274692609341

theorem tailTrace_3933680 : CollatzResearch.WordTrace tailWord_3933680 prefixEnd_3933680 2019868580978274692609341 := by
  unfold tailWord_3933680
  simp only [CollatzResearch.WordTrace]
  refine ⟨71736548194478326951431247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95648730925971102601908329 71736548194478326951431247)
  ·
    refine ⟨107604822291717490427146871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71736548194478326951431247 107604822291717490427146871)
    ·
      refine ⟨161407233437576235640720307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107604822291717490427146871 161407233437576235640720307)
      ·
        refine ⟨242110850156364353461080461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161407233437576235640720307 242110850156364353461080461)
        ·
          refine ⟨90791568808636632547905173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 242110850156364353461080461 90791568808636632547905173)
          ·
            refine ⟨4255854787904842150683055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 90791568808636632547905173 4255854787904842150683055)
            ·
              refine ⟨6383782181857263226024583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4255854787904842150683055 6383782181857263226024583)
              ·
                refine ⟨9575673272785894839036875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6383782181857263226024583 9575673272785894839036875)
                ·
                  refine ⟨14363509909178842258555313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9575673272785894839036875 14363509909178842258555313)
                  ·
                    refine ⟨10772632431884131693916485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14363509909178842258555313 10772632431884131693916485)
                    ·
                      refine ⟨2019868580978274692609341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10772632431884131693916485 2019868580978274692609341)
                      ·
                        rfl

theorem cell23_3933680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 1, 1, 1, 2, 4].length) (baseStart_3933680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3933680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3933680 prefixEnd_3933680 := by exact prefixLift 3933680
  have htrace : WordTrace (prefixWord ++ tailWord_3933680) baseStart_3933680 baseEnd_3933680 := by
    simpa [prefixWord, tailWord_3933680, baseEnd_3933680] using wordTrace_append hprefix tailTrace_3933680
  have hstable : (prefixWord ++ tailWord_3933680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3933680).length < 2 ^ (prefixWord ++ tailWord_3933680).sum := by decide
  have hdescent : baseEnd_3933680 < baseStart_3933680 := by decide
  rcases family_descends (prefixWord ++ tailWord_3933680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3933683 : List Nat := [1, 1, 1, 2, 2, 2, 2, 5, 1, 3, 3]
def baseStart_3933683 : Nat := 118140960795 + 3933683 * 2 ^ 59
def prefixEnd_3933683 : Nat := 4983230072969 + 3 ^ 40 * 3933683 * 2
def baseEnd_3933683 : Nat := 2019870121420238180871827

theorem tailTrace_3933683 : CollatzResearch.WordTrace tailWord_3933683 prefixEnd_3933683 2019870121420238180871827 := by
  unfold tailWord_3933683
  simp only [CollatzResearch.WordTrace]
  refine ⟨143473205807945785415221703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95648803871963856943481135 143473205807945785415221703)
  ·
    refine ⟨215209808711918678122832555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143473205807945785415221703 215209808711918678122832555)
    ·
      refine ⟨322814713067878017184248833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215209808711918678122832555 322814713067878017184248833)
      ·
        refine ⟨242111034800908512888186625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 322814713067878017184248833 242111034800908512888186625)
        ·
          refine ⟨181583276100681384666139969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 242111034800908512888186625 181583276100681384666139969)
          ·
            refine ⟨136187457075511038499604977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 181583276100681384666139969 136187457075511038499604977)
            ·
              refine ⟨102140592806633278874703733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136187457075511038499604977 102140592806633278874703733)
              ·
                refine ⟨9575680575621869894503475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 102140592806633278874703733 9575680575621869894503475)
                ·
                  refine ⟨14363520863432804841755213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9575680575621869894503475 14363520863432804841755213)
                  ·
                    refine ⟨5386320323787301815658205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14363520863432804841755213 5386320323787301815658205)
                    ·
                      refine ⟨2019870121420238180871827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5386320323787301815658205 2019870121420238180871827)
                      ·
                        rfl

theorem cell23_3933683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 5, 1, 3, 3].length) (baseStart_3933683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3933683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3933683 prefixEnd_3933683 := by exact prefixLift 3933683
  have htrace : WordTrace (prefixWord ++ tailWord_3933683) baseStart_3933683 baseEnd_3933683 := by
    simpa [prefixWord, tailWord_3933683, baseEnd_3933683] using wordTrace_append hprefix tailTrace_3933683
  have hstable : (prefixWord ++ tailWord_3933683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3933683).length < 2 ^ (prefixWord ++ tailWord_3933683).sum := by decide
  have hdescent : baseEnd_3933683 < baseStart_3933683 := by decide
  rcases family_descends (prefixWord ++ tailWord_3933683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3933793 : List Nat := [1, 2, 3, 1, 1, 3, 2, 2, 1, 7]
def baseStart_3933793 : Nat := 118140960795 + 3933793 * 2 ^ 59
def prefixEnd_3933793 : Nat := 4983230072969 + 3 ^ 40 * 3933793 * 2
def baseEnd_3933793 : Nat := 673308868097410916832107

theorem tailTrace_3933793 : CollatzResearch.WordTrace tailWord_3933793 prefixEnd_3933793 673308868097410916832107 := by
  unfold tailWord_3933793
  simp only [CollatzResearch.WordTrace]
  refine ⟨143477217837547274201726033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95651478558364849467817355 143477217837547274201726033)
  ·
    refine ⟨107607913378160455651294525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143477217837547274201726033 107607913378160455651294525)
    ·
      refine ⟨40352967516810170869235447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107607913378160455651294525 40352967516810170869235447)
      ·
        refine ⟨60529451275215256303853171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40352967516810170869235447 60529451275215256303853171)
        ·
          refine ⟨90794176912822884455779757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60529451275215256303853171 90794176912822884455779757)
          ·
            refine ⟨34047816342308581670917409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90794176912822884455779757 34047816342308581670917409)
            ·
              refine ⟨25535862256731436253188057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34047816342308581670917409 25535862256731436253188057)
              ·
                refine ⟨19151896692548577189891043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25535862256731436253188057 19151896692548577189891043)
                ·
                  refine ⟨28727845038822865784836565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19151896692548577189891043 28727845038822865784836565)
                  ·
                    refine ⟨673308868097410916832107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28727845038822865784836565 673308868097410916832107)
                    ·
                      rfl

theorem cell23_3933793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 2, 1, 7].length) (baseStart_3933793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3933793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3933793 prefixEnd_3933793 := by exact prefixLift 3933793
  have htrace : WordTrace (prefixWord ++ tailWord_3933793) baseStart_3933793 baseEnd_3933793 := by
    simpa [prefixWord, tailWord_3933793, baseEnd_3933793] using wordTrace_append hprefix tailTrace_3933793
  have hstable : (prefixWord ++ tailWord_3933793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3933793).length < 2 ^ (prefixWord ++ tailWord_3933793).sum := by decide
  have hdescent : baseEnd_3933793 < baseStart_3933793 := by decide
  rcases family_descends (prefixWord ++ tailWord_3933793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3933810 : List Nat := [3, 2, 1, 2, 3, 2, 1, 1, 1, 7]
def baseStart_3933810 : Nat := 118140960795 + 3933810 * 2 ^ 59
def prefixEnd_3933810 : Nat := 4983230072969 + 3 ^ 40 * 3933810 * 2
def baseEnd_3933810 : Nat := 673311777821119727994581

theorem tailTrace_3933810 : CollatzResearch.WordTrace tailWord_3933810 prefixEnd_3933810 673311777821119727994581 := by
  unfold tailWord_3933810
  simp only [CollatzResearch.WordTrace]
  refine ⟨35869459469621421526273721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95651891918990457403396589 35869459469621421526273721)
  ·
    refine ⟨26902094602216066144705291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35869459469621421526273721 26902094602216066144705291)
    ·
      refine ⟨40353141903324099217057937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26902094602216066144705291 40353141903324099217057937)
      ·
        refine ⟨30264856427493074412793453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40353141903324099217057937 30264856427493074412793453)
        ·
          refine ⟨11349321160309902904797545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30264856427493074412793453 11349321160309902904797545)
          ·
            refine ⟨8511990870232427178598159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11349321160309902904797545 8511990870232427178598159)
            ·
              refine ⟨12767986305348640767897239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8511990870232427178598159 12767986305348640767897239)
              ·
                refine ⟨19151979458022961151845859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12767986305348640767897239 19151979458022961151845859)
                ·
                  refine ⟨28727969187034441727768789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19151979458022961151845859 28727969187034441727768789)
                  ·
                    refine ⟨673311777821119727994581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28727969187034441727768789 673311777821119727994581)
                    ·
                      rfl

theorem cell23_3933810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 1, 1, 1, 7].length) (baseStart_3933810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3933810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3933810 prefixEnd_3933810 := by exact prefixLift 3933810
  have htrace : WordTrace (prefixWord ++ tailWord_3933810) baseStart_3933810 baseEnd_3933810 := by
    simpa [prefixWord, tailWord_3933810, baseEnd_3933810] using wordTrace_append hprefix tailTrace_3933810
  have hstable : (prefixWord ++ tailWord_3933810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3933810).length < 2 ^ (prefixWord ++ tailWord_3933810).sum := by decide
  have hdescent : baseEnd_3933810 < baseStart_3933810 := by decide
  rcases family_descends (prefixWord ++ tailWord_3933810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3933814 : List Nat := [5, 1, 1, 2, 2, 2, 2, 3, 5]
def baseStart_3933814 : Nat := 118140960795 + 3933814 * 2 ^ 59
def prefixEnd_3933814 : Nat := 4983230072969 + 3 ^ 40 * 3933814 * 2
def baseEnd_3933814 : Nat := 224437487487330796481525

theorem tailTrace_3933814 : CollatzResearch.WordTrace tailWord_3933814 prefixEnd_3933814 224437487487330796481525 := by
  unfold tailWord_3933814
  simp only [CollatzResearch.WordTrace]
  refine ⟨8967373985654449674265031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 95651989180314129858826997 8967373985654449674265031)
  ·
    refine ⟨13451060978481674511397547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8967373985654449674265031 13451060978481674511397547)
    ·
      refine ⟨20176591467722511767096321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13451060978481674511397547 20176591467722511767096321)
      ·
        refine ⟨15132443600791883825322241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20176591467722511767096321 15132443600791883825322241)
        ·
          refine ⟨11349332700593912868991681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15132443600791883825322241 11349332700593912868991681)
          ·
            refine ⟨8511999525445434651743761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11349332700593912868991681 8511999525445434651743761)
            ·
              refine ⟨6383999644084075988807821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8511999525445434651743761 6383999644084075988807821)
              ·
                refine ⟨2393999866531528495802933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6383999644084075988807821 2393999866531528495802933)
                ·
                  refine ⟨224437487487330796481525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2393999866531528495802933 224437487487330796481525)
                  ·
                    rfl

theorem cell23_3933814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 2, 3, 5].length) (baseStart_3933814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3933814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3933814 prefixEnd_3933814 := by exact prefixLift 3933814
  have htrace : WordTrace (prefixWord ++ tailWord_3933814) baseStart_3933814 baseEnd_3933814 := by
    simpa [prefixWord, tailWord_3933814, baseEnd_3933814] using wordTrace_append hprefix tailTrace_3933814
  have hstable : (prefixWord ++ tailWord_3933814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3933814).length < 2 ^ (prefixWord ++ tailWord_3933814).sum := by decide
  have hdescent : baseEnd_3933814 < baseStart_3933814 := by decide
  rcases family_descends (prefixWord ++ tailWord_3933814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3933833 : List Nat := [1, 2, 1, 1, 4, 1, 2, 1, 2, 3, 5]
def baseStart_3933833 : Nat := 118140960795 + 3933833 * 2 ^ 59
def prefixEnd_3933833 : Nat := 4983230072969 + 3 ^ 40 * 3933833 * 2
def baseEnd_3933833 : Nat := 2019947143518412593996137

theorem tailTrace_3933833 : CollatzResearch.WordTrace tailWord_3933833 prefixEnd_3933833 2019947143518412593996137 := by
  unfold tailWord_3933833
  simp only [CollatzResearch.WordTrace]
  refine ⟨143478676757402361033182153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95652451171601574022121435 143478676757402361033182153)
  ·
    refine ⟨107609007568051770774886615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143478676757402361033182153 107609007568051770774886615)
    ·
      refine ⟨161413511352077656162329923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107609007568051770774886615 161413511352077656162329923)
      ·
        refine ⟨242120267028116484243494885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161413511352077656162329923 242120267028116484243494885)
        ·
          refine ⟨45397550067771840795655291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 242120267028116484243494885 45397550067771840795655291)
          ·
            refine ⟨68096325101657761193482937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45397550067771840795655291 68096325101657761193482937)
            ·
              refine ⟨51072243826243320895112203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68096325101657761193482937 51072243826243320895112203)
              ·
                refine ⟨76608365739364981342668305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51072243826243320895112203 76608365739364981342668305)
                ·
                  refine ⟨57456274304523736007001229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76608365739364981342668305 57456274304523736007001229)
                  ·
                    refine ⟨21546102864196401002625461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 57456274304523736007001229 21546102864196401002625461)
                    ·
                      refine ⟨2019947143518412593996137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21546102864196401002625461 2019947143518412593996137)
                      ·
                        rfl

theorem cell23_3933833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 1, 2, 3, 5].length) (baseStart_3933833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3933833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3933833 prefixEnd_3933833 := by exact prefixLift 3933833
  have htrace : WordTrace (prefixWord ++ tailWord_3933833) baseStart_3933833 baseEnd_3933833 := by
    simpa [prefixWord, tailWord_3933833, baseEnd_3933833] using wordTrace_append hprefix tailTrace_3933833
  have hstable : (prefixWord ++ tailWord_3933833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3933833).length < 2 ^ (prefixWord ++ tailWord_3933833).sum := by decide
  have hdescent : baseEnd_3933833 < baseStart_3933833 := by decide
  rcases family_descends (prefixWord ++ tailWord_3933833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3933843 : List Nat := [1, 1, 1, 2, 1, 2, 2, 1, 4, 4, 4]
def baseStart_3933843 : Nat := 118140960795 + 3933843 * 2 ^ 59
def prefixEnd_3933843 : Nat := 4983230072969 + 3 ^ 40 * 3933843 * 2
def baseEnd_3933843 : Nat := 2019952278324957554871091

theorem tailTrace_3933843 : CollatzResearch.WordTrace tailWord_3933843 prefixEnd_3933843 2019952278324957554871091 := by
  unfold tailWord_3933843
  simp only [CollatzResearch.WordTrace]
  refine ⟨143479041487366132741046183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95652694324910755160697455 143479041487366132741046183)
  ·
    refine ⟨215218562231049199111569275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143479041487366132741046183 215218562231049199111569275)
    ·
      refine ⟨322827843346573798667353913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215218562231049199111569275 322827843346573798667353913)
      ·
        refine ⟨242120882509930349000515435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 322827843346573798667353913 242120882509930349000515435)
        ·
          refine ⟨363181323764895523500773153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242120882509930349000515435 363181323764895523500773153)
          ·
            refine ⟨272385992823671642625579865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 363181323764895523500773153 272385992823671642625579865)
            ·
              refine ⟨204289494617753731969184899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 272385992823671642625579865 204289494617753731969184899)
              ·
                refine ⟨306434241926630597953777349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 204289494617753731969184899 306434241926630597953777349)
                ·
                  refine ⟨57456420361243237116333253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 306434241926630597953777349 57456420361243237116333253)
                  ·
                    refine ⟨10773078817733106959312485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 57456420361243237116333253 10773078817733106959312485)
                    ·
                      refine ⟨2019952278324957554871091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10773078817733106959312485 2019952278324957554871091)
                      ·
                        rfl

theorem cell23_3933843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 4, 4, 4].length) (baseStart_3933843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3933843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3933843 prefixEnd_3933843 := by exact prefixLift 3933843
  have htrace : WordTrace (prefixWord ++ tailWord_3933843) baseStart_3933843 baseEnd_3933843 := by
    simpa [prefixWord, tailWord_3933843, baseEnd_3933843] using wordTrace_append hprefix tailTrace_3933843
  have hstable : (prefixWord ++ tailWord_3933843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3933843).length < 2 ^ (prefixWord ++ tailWord_3933843).sum := by decide
  have hdescent : baseEnd_3933843 < baseStart_3933843 := by decide
  rcases family_descends (prefixWord ++ tailWord_3933843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3933847 : List Nat := [1, 1, 3, 3, 2, 2, 2, 1, 2, 4, 2]
def baseStart_3933847 : Nat := 118140960795 + 3933847 * 2 ^ 59
def prefixEnd_3933847 : Nat := 4983230072969 + 3 ^ 40 * 3933847 * 2
def baseEnd_3933847 : Nat := 2019954332247575539221073

theorem tailTrace_3933847 : CollatzResearch.WordTrace tailWord_3933847 prefixEnd_3933847 2019954332247575539221073 := by
  unfold tailWord_3933847
  simp only [CollatzResearch.WordTrace]
  refine ⟨143479187379351641424191795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95652791586234427616127863 143479187379351641424191795)
  ·
    refine ⟨215218781069027462136287693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143479187379351641424191795 215218781069027462136287693)
    ·
      refine ⟨80707042900885298301107885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 215218781069027462136287693 80707042900885298301107885)
      ·
        refine ⟨30265141087831986862915457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80707042900885298301107885 30265141087831986862915457)
        ·
          refine ⟨22698855815873990147186593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30265141087831986862915457 22698855815873990147186593)
          ·
            refine ⟨17024141861905492610389945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22698855815873990147186593 17024141861905492610389945)
            ·
              refine ⟨12768106396429119457792459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17024141861905492610389945 12768106396429119457792459)
              ·
                refine ⟨19152159594643679186688689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12768106396429119457792459 19152159594643679186688689)
                ·
                  refine ⟨14364119695982759390016517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19152159594643679186688689 14364119695982759390016517)
                  ·
                    refine ⟨2693272442996767385628097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14364119695982759390016517 2693272442996767385628097)
                    ·
                      refine ⟨2019954332247575539221073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2693272442996767385628097 2019954332247575539221073)
                      ·
                        rfl

theorem cell23_3933847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2, 1, 2, 4, 2].length) (baseStart_3933847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3933847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3933847 prefixEnd_3933847 := by exact prefixLift 3933847
  have htrace : WordTrace (prefixWord ++ tailWord_3933847) baseStart_3933847 baseEnd_3933847 := by
    simpa [prefixWord, tailWord_3933847, baseEnd_3933847] using wordTrace_append hprefix tailTrace_3933847
  have hstable : (prefixWord ++ tailWord_3933847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3933847).length < 2 ^ (prefixWord ++ tailWord_3933847).sum := by decide
  have hdescent : baseEnd_3933847 < baseStart_3933847 := by decide
  rcases family_descends (prefixWord ++ tailWord_3933847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3933857 : List Nat := [1, 2, 3, 3, 2, 1, 2, 2, 3, 4]
def baseStart_3933857 : Nat := 118140960795 + 3933857 * 2 ^ 59
def prefixEnd_3933857 : Nat := 4983230072969 + 3 ^ 40 * 3933857 * 2
def baseEnd_3933857 : Nat := 673319822351373500032009

theorem tailTrace_3933857 : CollatzResearch.WordTrace tailWord_3933857 prefixEnd_3933857 673319822351373500032009 := by
  unfold tailWord_3933857
  simp only [CollatzResearch.WordTrace]
  refine ⟨143479552109315413132055825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95653034739543608754703883 143479552109315413132055825)
  ·
    refine ⟨107609664081986559849041869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143479552109315413132055825 107609664081986559849041869)
    ·
      refine ⟨40353624030744959943390701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107609664081986559849041869 40353624030744959943390701)
      ·
        refine ⟨15132609011529359978771513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40353624030744959943390701 15132609011529359978771513)
        ·
          refine ⟨11349456758647019984078635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15132609011529359978771513 11349456758647019984078635)
          ·
            refine ⟨17024185137970529976117953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11349456758647019984078635 17024185137970529976117953)
            ·
              refine ⟨12768138853477897482088465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17024185137970529976117953 12768138853477897482088465)
              ·
                refine ⟨9576104140108423111566349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12768138853477897482088465 9576104140108423111566349)
                ·
                  refine ⟨3591039052540658666837381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9576104140108423111566349 3591039052540658666837381)
                  ·
                    refine ⟨673319822351373500032009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3591039052540658666837381 673319822351373500032009)
                    ·
                      rfl

theorem cell23_3933857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 2, 2, 3, 4].length) (baseStart_3933857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3933857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3933857 prefixEnd_3933857 := by exact prefixLift 3933857
  have htrace : WordTrace (prefixWord ++ tailWord_3933857) baseStart_3933857 baseEnd_3933857 := by
    simpa [prefixWord, tailWord_3933857, baseEnd_3933857] using wordTrace_append hprefix tailTrace_3933857
  have hstable : (prefixWord ++ tailWord_3933857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3933857).length < 2 ^ (prefixWord ++ tailWord_3933857).sum := by decide
  have hdescent : baseEnd_3933857 < baseStart_3933857 := by decide
  rcases family_descends (prefixWord ++ tailWord_3933857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3933874 : List Nat := [3, 2, 1, 1, 1, 2, 5, 3, 1, 4]
def baseStart_3933874 : Nat := 118140960795 + 3933874 * 2 ^ 59
def prefixEnd_3933874 : Nat := 4983230072969 + 3 ^ 40 * 3933874 * 2
def baseEnd_3933874 : Nat := 673322732075082311194483

theorem tailTrace_3933874 : CollatzResearch.WordTrace tailWord_3933874 prefixEnd_3933874 673322732075082311194483 := by
  unfold tailWord_3933874
  simp only [CollatzResearch.WordTrace]
  refine ⟨35870043037563456258856169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95653448100169216690283117 35870043037563456258856169)
  ·
    refine ⟨26902532278172592194142127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35870043037563456258856169 26902532278172592194142127)
    ·
      refine ⟨40353798417258888291213191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26902532278172592194142127 40353798417258888291213191)
      ·
        refine ⟨60530697625888332436819787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40353798417258888291213191 60530697625888332436819787)
        ·
          refine ⟨90796046438832498655229681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60530697625888332436819787 90796046438832498655229681)
          ·
            refine ⟨68097034829124373991422261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90796046438832498655229681 68097034829124373991422261)
            ·
              refine ⟨6384097015230410061695837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 68097034829124373991422261 6384097015230410061695837)
              ·
                refine ⟨2394036380711403773135939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6384097015230410061695837 2394036380711403773135939)
                ·
                  refine ⟨3591054571067105659703909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2394036380711403773135939 3591054571067105659703909)
                  ·
                    refine ⟨673322732075082311194483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3591054571067105659703909 673322732075082311194483)
                    ·
                      rfl

theorem cell23_3933874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 5, 3, 1, 4].length) (baseStart_3933874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3933874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3933874 prefixEnd_3933874 := by exact prefixLift 3933874
  have htrace : WordTrace (prefixWord ++ tailWord_3933874) baseStart_3933874 baseEnd_3933874 := by
    simpa [prefixWord, tailWord_3933874, baseEnd_3933874] using wordTrace_append hprefix tailTrace_3933874
  have hstable : (prefixWord ++ tailWord_3933874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3933874).length < 2 ^ (prefixWord ++ tailWord_3933874).sum := by decide
  have hdescent : baseEnd_3933874 < baseStart_3933874 := by decide
  rcases family_descends (prefixWord ++ tailWord_3933874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3933924 : List Nat := [2, 3, 1, 1, 1, 3, 4, 1, 2, 3, 2]
def baseStart_3933924 : Nat := 118140960795 + 3933924 * 2 ^ 59
def prefixEnd_3933924 : Nat := 4983230072969 + 3 ^ 40 * 3933924 * 2
def baseEnd_3933924 : Nat := 2019993870257971737958219

theorem tailTrace_3933924 : CollatzResearch.WordTrace tailWord_3933924 prefixEnd_3933924 2019993870257971737958219 := by
  unfold tailWord_3933924
  simp only [CollatzResearch.WordTrace]
  refine ⟨71740997900036341787372413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95654663866715122383163217 71740997900036341787372413)
  ·
    refine ⟨26902874212513628170264655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71740997900036341787372413 26902874212513628170264655)
    ·
      refine ⟨40354311318770442255396983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26902874212513628170264655 40354311318770442255396983)
      ·
        refine ⟨60531466978155663383095475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40354311318770442255396983 60531466978155663383095475)
        ·
          refine ⟨90797200467233495074643213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60531466978155663383095475 90797200467233495074643213)
          ·
            refine ⟨34048950175212560652991205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90797200467233495074643213 34048950175212560652991205)
            ·
              refine ⟨6384178157852355122435851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34048950175212560652991205 6384178157852355122435851)
              ·
                refine ⟨9576267236778532683653777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6384178157852355122435851 9576267236778532683653777)
                ·
                  refine ⟨7182200427583899512740333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9576267236778532683653777 7182200427583899512740333)
                  ·
                    refine ⟨2693325160343962317277625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7182200427583899512740333 2693325160343962317277625)
                    ·
                      refine ⟨2019993870257971737958219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2693325160343962317277625 2019993870257971737958219)
                      ·
                        rfl

theorem cell23_3933924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 4, 1, 2, 3, 2].length) (baseStart_3933924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3933924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3933924 prefixEnd_3933924 := by exact prefixLift 3933924
  have htrace : WordTrace (prefixWord ++ tailWord_3933924) baseStart_3933924 baseEnd_3933924 := by
    simpa [prefixWord, tailWord_3933924, baseEnd_3933924] using wordTrace_append hprefix tailTrace_3933924
  have hstable : (prefixWord ++ tailWord_3933924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3933924).length < 2 ^ (prefixWord ++ tailWord_3933924).sum := by decide
  have hdescent : baseEnd_3933924 < baseStart_3933924 := by decide
  rcases family_descends (prefixWord ++ tailWord_3933924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3933930 : List Nat := [3, 1, 3, 1, 1, 1, 3, 1, 3, 6]
def baseStart_3933930 : Nat := 118140960795 + 3933930 * 2 ^ 59
def prefixEnd_3933930 : Nat := 4983230072969 + 3 ^ 40 * 3933930 * 2
def baseEnd_3933930 : Nat := 673332317047299571494397

theorem tailTrace_3933930 : CollatzResearch.WordTrace tailWord_3933930 prefixEnd_3933930 673332317047299571494397 := by
  unfold tailWord_3933930
  simp only [CollatzResearch.WordTrace]
  refine ⟨35870553659512736649865811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95654809758700631066308829 35870553659512736649865811)
  ·
    refine ⟨53805830489269104974798717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35870553659512736649865811 53805830489269104974798717)
    ·
      refine ⟨20177186433475914365549519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53805830489269104974798717 20177186433475914365549519)
      ·
        refine ⟨30265779650213871548324279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20177186433475914365549519 30265779650213871548324279)
        ·
          refine ⟨45398669475320807322486419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30265779650213871548324279 45398669475320807322486419)
          ·
            refine ⟨68098004212981210983729629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45398669475320807322486419 68098004212981210983729629)
            ·
              refine ⟨25536751579867954118898611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68098004212981210983729629 25536751579867954118898611)
              ·
                refine ⟨38305127369801931178347917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25536751579867954118898611 38305127369801931178347917)
                ·
                  refine ⟨14364422763675724191880469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38305127369801931178347917 14364422763675724191880469)
                  ·
                    refine ⟨673332317047299571494397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14364422763675724191880469 673332317047299571494397)
                    ·
                      rfl

theorem cell23_3933930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 1, 3, 6].length) (baseStart_3933930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3933930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3933930 prefixEnd_3933930 := by exact prefixLift 3933930
  have htrace : WordTrace (prefixWord ++ tailWord_3933930) baseStart_3933930 baseEnd_3933930 := by
    simpa [prefixWord, tailWord_3933930, baseEnd_3933930] using wordTrace_append hprefix tailTrace_3933930
  have hstable : (prefixWord ++ tailWord_3933930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3933930).length < 2 ^ (prefixWord ++ tailWord_3933930).sum := by decide
  have hdescent : baseEnd_3933930 < baseStart_3933930 := by decide
  rcases family_descends (prefixWord ++ tailWord_3933930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3933934 : List Nat := [4, 1, 2, 1, 1, 2, 5, 1, 1, 5]
def baseStart_3933934 : Nat := 118140960795 + 3933934 * 2 ^ 59
def prefixEnd_3933934 : Nat := 4983230072969 + 3 ^ 40 * 3933934 * 2
def baseEnd_3933934 : Nat := 673333001688172232944391

theorem tailTrace_3933934 : CollatzResearch.WordTrace tailWord_3933934 prefixEnd_3933934 673333001688172232944391 := by
  unfold tailWord_3933934
  simp only [CollatzResearch.WordTrace]
  refine ⟨17935295066254556910326107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95654907020024303521739237 17935295066254556910326107)
  ·
    refine ⟨26902942599381835365489161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17935295066254556910326107 26902942599381835365489161)
    ·
      refine ⟨20177206949536376524116871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26902942599381835365489161 20177206949536376524116871)
      ·
        refine ⟨30265810424304564786175307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20177206949536376524116871 30265810424304564786175307)
        ·
          refine ⟨45398715636456847179262961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30265810424304564786175307 45398715636456847179262961)
          ·
            refine ⟨34049036727342635384447221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45398715636456847179262961 34049036727342635384447221)
            ·
              refine ⟨3192097193188372067291927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34049036727342635384447221 3192097193188372067291927)
              ·
                refine ⟨4788145789782558100937891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3192097193188372067291927 4788145789782558100937891)
                ·
                  refine ⟨7182218684673837151406837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4788145789782558100937891 7182218684673837151406837)
                  ·
                    refine ⟨673333001688172232944391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7182218684673837151406837 673333001688172232944391)
                    ·
                      rfl

theorem cell23_3933934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 5, 1, 1, 5].length) (baseStart_3933934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3933934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3933934 prefixEnd_3933934 := by exact prefixLift 3933934
  have htrace : WordTrace (prefixWord ++ tailWord_3933934) baseStart_3933934 baseEnd_3933934 := by
    simpa [prefixWord, tailWord_3933934, baseEnd_3933934] using wordTrace_append hprefix tailTrace_3933934
  have hstable : (prefixWord ++ tailWord_3933934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3933934).length < 2 ^ (prefixWord ++ tailWord_3933934).sum := by decide
  have hdescent : baseEnd_3933934 < baseStart_3933934 := by decide
  rcases family_descends (prefixWord ++ tailWord_3933934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3933982 : List Nat := [4, 3, 2, 2, 1, 1, 2, 3, 1, 1, 3]
def baseStart_3933982 : Nat := 118140960795 + 3933982 * 2 ^ 59
def prefixEnd_3933982 : Nat := 4983230072969 + 3 ^ 40 * 3933982 * 2
def baseEnd_3933982 : Nat := 2020023652135932511032953

theorem tailTrace_3933982 : CollatzResearch.WordTrace tailWord_3933982 prefixEnd_3933982 2020023652135932511032953 := by
  unfold tailWord_3933982
  simp only [CollatzResearch.WordTrace]
  refine ⟨17935513904232819935044525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95656074155908372986904133 17935513904232819935044525)
  ·
    refine ⟨6725817714087307475641697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17935513904232819935044525 6725817714087307475641697)
    ·
      refine ⟨5044363285565480606731273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6725817714087307475641697 5044363285565480606731273)
      ·
        refine ⟨3783272464174110455048455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5044363285565480606731273 3783272464174110455048455)
        ·
          refine ⟨5674908696261165682572683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3783272464174110455048455 5674908696261165682572683)
          ·
            refine ⟨8512363044391748523859025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5674908696261165682572683 8512363044391748523859025)
            ·
              refine ⟨6384272283293811392894269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8512363044391748523859025 6384272283293811392894269)
              ·
                refine ⟨2394102106235179272335351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6384272283293811392894269 2394102106235179272335351)
                ·
                  refine ⟨3591153159352768908503027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2394102106235179272335351 3591153159352768908503027)
                  ·
                    refine ⟨5386729739029153362754541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3591153159352768908503027 5386729739029153362754541)
                    ·
                      refine ⟨2020023652135932511032953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5386729739029153362754541 2020023652135932511032953)
                      ·
                        rfl

theorem cell23_3933982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 2, 3, 1, 1, 3].length) (baseStart_3933982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3933982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3933982 prefixEnd_3933982 := by exact prefixLift 3933982
  have htrace : WordTrace (prefixWord ++ tailWord_3933982) baseStart_3933982 baseEnd_3933982 := by
    simpa [prefixWord, tailWord_3933982, baseEnd_3933982] using wordTrace_append hprefix tailTrace_3933982
  have hstable : (prefixWord ++ tailWord_3933982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3933982).length < 2 ^ (prefixWord ++ tailWord_3933982).sum := by decide
  have hdescent : baseEnd_3933982 < baseStart_3933982 := by decide
  rcases family_descends (prefixWord ++ tailWord_3933982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3933987 : List Nat := [1, 1, 1, 4, 2, 1, 4, 2, 1, 3, 3]
def baseStart_3933987 : Nat := 118140960795 + 3933987 * 2 ^ 59
def prefixEnd_3933987 : Nat := 4983230072969 + 3 ^ 40 * 3933987 * 2
def baseEnd_3933987 : Nat := 2020026219539204991470429

theorem tailTrace_3933987 : CollatzResearch.WordTrace tailWord_3933987 prefixEnd_3933987 2020026219539204991470429 := by
  unfold tailWord_3933987
  simp only [CollatzResearch.WordTrace]
  refine ⟨143484293598844445334288215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95656195732562963556192143 143484293598844445334288215)
  ·
    refine ⟨215226440398266668001432323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143484293598844445334288215 215226440398266668001432323)
    ·
      refine ⟨322839660597400002002148485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215226440398266668001432323 322839660597400002002148485)
      ·
        refine ⟨60532436362012500375402841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 322839660597400002002148485 60532436362012500375402841)
        ·
          refine ⟨45399327271509375281552131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60532436362012500375402841 45399327271509375281552131)
          ·
            refine ⟨68098990907264062922328197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45399327271509375281552131 68098990907264062922328197)
            ·
              refine ⟨12768560795112011797936537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68098990907264062922328197 12768560795112011797936537)
              ·
                refine ⟨9576420596334008848452403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12768560795112011797936537 9576420596334008848452403)
                ·
                  refine ⟨14364630894501013272678605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9576420596334008848452403 14364630894501013272678605)
                  ·
                    refine ⟨5386736585437879977254477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14364630894501013272678605 5386736585437879977254477)
                    ·
                      refine ⟨2020026219539204991470429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5386736585437879977254477 2020026219539204991470429)
                      ·
                        rfl

theorem cell23_3933987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4, 2, 1, 3, 3].length) (baseStart_3933987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3933987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3933987 prefixEnd_3933987 := by exact prefixLift 3933987
  have htrace : WordTrace (prefixWord ++ tailWord_3933987) baseStart_3933987 baseEnd_3933987 := by
    simpa [prefixWord, tailWord_3933987, baseEnd_3933987] using wordTrace_append hprefix tailTrace_3933987
  have hstable : (prefixWord ++ tailWord_3933987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3933987).length < 2 ^ (prefixWord ++ tailWord_3933987).sum := by decide
  have hdescent : baseEnd_3933987 < baseStart_3933987 := by decide
  rcases family_descends (prefixWord ++ tailWord_3933987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3933988 : List Nat := [2, 3, 1, 3, 2, 1, 1, 5, 1, 2, 2]
def baseStart_3933988 : Nat := 118140960795 + 3933988 * 2 ^ 59
def prefixEnd_3933988 : Nat := 4983230072969 + 3 ^ 40 * 3933988 * 2
def baseEnd_3933988 : Nat := 2020026733019859487557925

theorem tailTrace_3933988 : CollatzResearch.WordTrace tailWord_3933988 prefixEnd_3933988 2020026733019859487557925 := by
  unfold tailWord_3933988
  simp only [CollatzResearch.WordTrace]
  refine ⟨71742165035920411252537309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95656220047893881670049745 71742165035920411252537309)
  ·
    refine ⟨26903311888470154219701491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71742165035920411252537309 26903311888470154219701491)
    ·
      refine ⟨40354967832705231329552237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26903311888470154219701491 40354967832705231329552237)
      ·
        refine ⟨15133112937264461748582089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40354967832705231329552237 15133112937264461748582089)
        ·
          refine ⟨11349834702948346311436567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15133112937264461748582089 11349834702948346311436567)
          ·
            refine ⟨17024752054422519467154851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11349834702948346311436567 17024752054422519467154851)
            ·
              refine ⟨25537128081633779200732277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17024752054422519467154851 25537128081633779200732277)
              ·
                refine ⟨2394105757653166800068651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25537128081633779200732277 2394105757653166800068651)
                ·
                  refine ⟨3591158636479750200102977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2394105757653166800068651 3591158636479750200102977)
                  ·
                    refine ⟨2693368977359812650077233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3591158636479750200102977 2693368977359812650077233)
                    ·
                      refine ⟨2020026733019859487557925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2693368977359812650077233 2020026733019859487557925)
                      ·
                        rfl

theorem cell23_3933988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 5, 1, 2, 2].length) (baseStart_3933988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3933988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3933988 prefixEnd_3933988 := by exact prefixLift 3933988
  have htrace : WordTrace (prefixWord ++ tailWord_3933988) baseStart_3933988 baseEnd_3933988 := by
    simpa [prefixWord, tailWord_3933988, baseEnd_3933988] using wordTrace_append hprefix tailTrace_3933988
  have hstable : (prefixWord ++ tailWord_3933988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3933988).length < 2 ^ (prefixWord ++ tailWord_3933988).sum := by decide
  have hdescent : baseEnd_3933988 < baseStart_3933988 := by decide
  rcases family_descends (prefixWord ++ tailWord_3933988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3933998 : List Nat := [4, 1, 3, 2, 2, 2, 1, 2, 2, 4]
def baseStart_3933998 : Nat := 118140960795 + 3933998 * 2 ^ 59
def prefixEnd_3933998 : Nat := 4983230072969 + 3 ^ 40 * 3933998 * 2
def baseEnd_3933998 : Nat := 673343955942134816144293

theorem tailTrace_3933998 : CollatzResearch.WordTrace tailWord_3933998 prefixEnd_3933998 673343955942134816144293 := by
  unfold tailWord_3933998
  simp only [CollatzResearch.WordTrace]
  refine ⟨17935586850225574276617331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95656463201203062808625765 17935586850225574276617331)
  ·
    refine ⟨26903380275338361414925997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17935586850225574276617331 26903380275338361414925997)
    ·
      refine ⟨10088767603251885530597249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26903380275338361414925997 10088767603251885530597249)
      ·
        refine ⟨7566575702438914147947937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10088767603251885530597249 7566575702438914147947937)
        ·
          refine ⟨5674931776829185610960953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7566575702438914147947937 5674931776829185610960953)
          ·
            refine ⟨4256198832621889208220715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5674931776829185610960953 4256198832621889208220715)
            ·
              refine ⟨6384298248932833812331073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4256198832621889208220715 6384298248932833812331073)
              ·
                refine ⟨4788223686699625359248305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6384298248932833812331073 4788223686699625359248305)
                ·
                  refine ⟨3591167765024719019436229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4788223686699625359248305 3591167765024719019436229)
                  ·
                    refine ⟨673343955942134816144293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3591167765024719019436229 673343955942134816144293)
                    ·
                      rfl

theorem cell23_3933998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 1, 2, 2, 4].length) (baseStart_3933998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3933998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3933998 prefixEnd_3933998 := by exact prefixLift 3933998
  have htrace : WordTrace (prefixWord ++ tailWord_3933998) baseStart_3933998 baseEnd_3933998 := by
    simpa [prefixWord, tailWord_3933998, baseEnd_3933998] using wordTrace_append hprefix tailTrace_3933998
  have hstable : (prefixWord ++ tailWord_3933998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3933998).length < 2 ^ (prefixWord ++ tailWord_3933998).sum := by decide
  have hdescent : baseEnd_3933998 < baseStart_3933998 := by decide
  rcases family_descends (prefixWord ++ tailWord_3933998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3934021 : List Nat := [1, 3, 1, 1, 1, 2, 7, 1, 2, 1, 3]
def baseStart_3934021 : Nat := 118140960795 + 3934021 * 2 ^ 59
def prefixEnd_3934021 : Nat := 4983230072969 + 3 ^ 40 * 3934021 * 2
def baseEnd_3934021 : Nat := 2020043677881457858445273

theorem tailTrace_3934021 : CollatzResearch.WordTrace tailWord_3934021 prefixEnd_3934021 2020043677881457858445273 := by
  unfold tailWord_3934021
  simp only [CollatzResearch.WordTrace]
  refine ⟨143485533680721269141025917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95657022453814179427350611 143485533680721269141025917)
  ·
    refine ⟨53807075130270475927884719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143485533680721269141025917 53807075130270475927884719)
    ·
      refine ⟨80710612695405713891827079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53807075130270475927884719 80710612695405713891827079)
      ·
        refine ⟨121065919043108570837740619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80710612695405713891827079 121065919043108570837740619)
        ·
          refine ⟨181598878564662856256610929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121065919043108570837740619 181598878564662856256610929)
          ·
            refine ⟨136199158923497142192458197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 181598878564662856256610929 136199158923497142192458197)
            ·
              refine ⟨3192167787269464270135739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 136199158923497142192458197 3192167787269464270135739)
              ·
                refine ⟨4788251680904196405203609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3192167787269464270135739 4788251680904196405203609)
                ·
                  refine ⟨3591188760678147303902707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4788251680904196405203609 3591188760678147303902707)
                  ·
                    refine ⟨5386783141017220955854061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3591188760678147303902707 5386783141017220955854061)
                    ·
                      refine ⟨2020043677881457858445273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5386783141017220955854061 2020043677881457858445273)
                      ·
                        rfl

theorem cell23_3934021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 7, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 7, 1, 2, 1, 3].length) (baseStart_3934021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3934021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3934021 prefixEnd_3934021 := by exact prefixLift 3934021
  have htrace : WordTrace (prefixWord ++ tailWord_3934021) baseStart_3934021 baseEnd_3934021 := by
    simpa [prefixWord, tailWord_3934021, baseEnd_3934021] using wordTrace_append hprefix tailTrace_3934021
  have hstable : (prefixWord ++ tailWord_3934021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3934021).length < 2 ^ (prefixWord ++ tailWord_3934021).sum := by decide
  have hdescent : baseEnd_3934021 < baseStart_3934021 := by decide
  rcases family_descends (prefixWord ++ tailWord_3934021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3934047 : List Nat := [1, 1, 2, 3, 1, 5, 1, 1, 2, 1, 5]
def baseStart_3934047 : Nat := 118140960795 + 3934047 * 2 ^ 59
def prefixEnd_3934047 : Nat := 4983230072969 + 3 ^ 40 * 3934047 * 2
def baseEnd_3934047 : Nat := 2020057028378474756720153

theorem tailTrace_3934047 : CollatzResearch.WordTrace tailWord_3934047 prefixEnd_3934047 2020057028378474756720153 := by
  unfold tailWord_3934047
  simp only [CollatzResearch.WordTrace]
  refine ⟨143486481978627075581472395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95657654652418050387648263 143486481978627075581472395)
  ·
    refine ⟨215229722967940613372208593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143486481978627075581472395 215229722967940613372208593)
    ·
      refine ⟨161422292225955460029156445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215229722967940613372208593 161422292225955460029156445)
      ·
        refine ⟨60533359584733297510933667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 161422292225955460029156445 60533359584733297510933667)
        ·
          refine ⟨90800039377099946266400501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60533359584733297510933667 90800039377099946266400501)
          ·
            refine ⟨8512503691603119962475047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 90800039377099946266400501 8512503691603119962475047)
            ·
              refine ⟨12768755537404679943712571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8512503691603119962475047 12768755537404679943712571)
              ·
                refine ⟨19153133306107019915568857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12768755537404679943712571 19153133306107019915568857)
                ·
                  refine ⟨14364849979580264936676643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19153133306107019915568857 14364849979580264936676643)
                  ·
                    refine ⟨21547274969370397405014965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14364849979580264936676643 21547274969370397405014965)
                    ·
                      refine ⟨2020057028378474756720153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21547274969370397405014965 2020057028378474756720153)
                      ·
                        rfl

theorem cell23_3934047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 1, 1, 2, 1, 5].length) (baseStart_3934047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3934047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3934047 prefixEnd_3934047 := by exact prefixLift 3934047
  have htrace : WordTrace (prefixWord ++ tailWord_3934047) baseStart_3934047 baseEnd_3934047 := by
    simpa [prefixWord, tailWord_3934047, baseEnd_3934047] using wordTrace_append hprefix tailTrace_3934047
  have hstable : (prefixWord ++ tailWord_3934047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3934047).length < 2 ^ (prefixWord ++ tailWord_3934047).sum := by decide
  have hdescent : baseEnd_3934047 < baseStart_3934047 := by decide
  rcases family_descends (prefixWord ++ tailWord_3934047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3934061 : List Nat := [1, 5, 1, 1, 1, 1, 4, 1, 4, 2, 2]
def baseStart_3934061 : Nat := 118140960795 + 3934061 * 2 ^ 59
def prefixEnd_3934061 : Nat := 4983230072969 + 3 ^ 40 * 3934061 * 2
def baseEnd_3934061 : Nat := 2020064217107637701945089

theorem tailTrace_3934061 : CollatzResearch.WordTrace tailWord_3934061 prefixEnd_3934061 2020064217107637701945089 := by
  unfold tailWord_3934061
  simp only [CollatzResearch.WordTrace]
  refine ⟨143486992600576355972482037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95657995067050903981654691 143486992600576355972482037)
  ·
    refine ⟨13451905556304033372420191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 143486992600576355972482037 13451905556304033372420191)
    ·
      refine ⟨20177858334456050058630287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13451905556304033372420191 20177858334456050058630287)
      ·
        refine ⟨30266787501684075087945431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20177858334456050058630287 30266787501684075087945431)
        ·
          refine ⟨45400181252526112631918147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30266787501684075087945431 45400181252526112631918147)
          ·
            refine ⟨68100271878789168947877221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45400181252526112631918147 68100271878789168947877221)
            ·
              refine ⟨12768800977272969177726979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68100271878789168947877221 12768800977272969177726979)
              ·
                refine ⟨19153201465909453766590469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12768800977272969177726979 19153201465909453766590469)
                ·
                  refine ⟨3591225274858022581235713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19153201465909453766590469 3591225274858022581235713)
                  ·
                    refine ⟨2693418956143516935926785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3591225274858022581235713 2693418956143516935926785)
                    ·
                      refine ⟨2020064217107637701945089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2693418956143516935926785 2020064217107637701945089)
                      ·
                        rfl

theorem cell23_3934061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 4, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 4, 1, 4, 2, 2].length) (baseStart_3934061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3934061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3934061 prefixEnd_3934061 := by exact prefixLift 3934061
  have htrace : WordTrace (prefixWord ++ tailWord_3934061) baseStart_3934061 baseEnd_3934061 := by
    simpa [prefixWord, tailWord_3934061, baseEnd_3934061] using wordTrace_append hprefix tailTrace_3934061
  have hstable : (prefixWord ++ tailWord_3934061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3934061).length < 2 ^ (prefixWord ++ tailWord_3934061).sum := by decide
  have hdescent : baseEnd_3934061 < baseStart_3934061 := by decide
  rcases family_descends (prefixWord ++ tailWord_3934061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3934077 : List Nat := [1, 4, 1, 1, 2, 1, 1, 3, 1, 5, 3]
def baseStart_3934077 : Nat := 118140960795 + 3934077 * 2 ^ 59
def prefixEnd_3934077 : Nat := 4983230072969 + 3 ^ 40 * 3934077 * 2
def baseEnd_3934077 : Nat := 2020072432798109639345015

theorem tailTrace_3934077 : CollatzResearch.WordTrace tailWord_3934077 prefixEnd_3934077 2020072432798109639345015 := by
  unfold tailWord_3934077
  simp only [CollatzResearch.WordTrace]
  refine ⟨143487576168518390705064485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95658384112345593803376323 143487576168518390705064485)
  ·
    refine ⟨26903920531597198257199591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 143487576168518390705064485 26903920531597198257199591)
    ·
      refine ⟨40355880797395797385799387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26903920531597198257199591 40355880797395797385799387)
      ·
        refine ⟨60533821196093696078699081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40355880797395797385799387 60533821196093696078699081)
        ·
          refine ⟨45400365897070272059024311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60533821196093696078699081 45400365897070272059024311)
          ·
            refine ⟨68100548845605408088536467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45400365897070272059024311 68100548845605408088536467)
            ·
              refine ⟨102150823268408112132804701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68100548845605408088536467 102150823268408112132804701)
              ·
                refine ⟨38306558725653042049801763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 102150823268408112132804701 38306558725653042049801763)
                ·
                  refine ⟨57459838088479563074702645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38306558725653042049801763 57459838088479563074702645)
                  ·
                    refine ⟨5386859820794959038253373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 57459838088479563074702645 5386859820794959038253373)
                    ·
                      refine ⟨2020072432798109639345015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5386859820794959038253373 2020072432798109639345015)
                      ·
                        rfl

theorem cell23_3934077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 3, 1, 5, 3].length) (baseStart_3934077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3934077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3934077 prefixEnd_3934077 := by exact prefixLift 3934077
  have htrace : WordTrace (prefixWord ++ tailWord_3934077) baseStart_3934077 baseEnd_3934077 := by
    simpa [prefixWord, tailWord_3934077, baseEnd_3934077] using wordTrace_append hprefix tailTrace_3934077
  have hstable : (prefixWord ++ tailWord_3934077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3934077).length < 2 ^ (prefixWord ++ tailWord_3934077).sum := by decide
  have hdescent : baseEnd_3934077 < baseStart_3934077 := by decide
  rcases family_descends (prefixWord ++ tailWord_3934077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3934097 : List Nat := [1, 2, 2, 1, 1, 1, 5, 3, 2, 5]
def baseStart_3934097 : Nat := 118140960795 + 3934097 * 2 ^ 59
def prefixEnd_3934097 : Nat := 4983230072969 + 3 ^ 40 * 3934097 * 2
def baseEnd_3934097 : Nat := 673360900803733187031641

theorem tailTrace_3934097 : CollatzResearch.WordTrace tailWord_3934097 prefixEnd_3934097 673360900803733187031641 := by
  unfold tailWord_3934097
  simp only [CollatzResearch.WordTrace]
  refine ⟨143488305628445934120792545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95658870418963956080528363 143488305628445934120792545)
  ·
    refine ⟨107616229221334450590594409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143488305628445934120792545 107616229221334450590594409)
    ·
      refine ⟨80712171916000837942945807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107616229221334450590594409 80712171916000837942945807)
      ·
        refine ⟨121068257874001256914418711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80712171916000837942945807 121068257874001256914418711)
        ·
          refine ⟨181602386811001885371628067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121068257874001256914418711 181602386811001885371628067)
          ·
            refine ⟨272403580216502828057442101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181602386811001885371628067 272403580216502828057442101)
            ·
              refine ⟨25537835645297140130385197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 272403580216502828057442101 25537835645297140130385197)
              ·
                refine ⟨9576688366986427548894449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25537835645297140130385197 9576688366986427548894449)
                ·
                  refine ⟨7182516275239820661670837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9576688366986427548894449 7182516275239820661670837)
                  ·
                    refine ⟨673360900803733187031641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7182516275239820661670837 673360900803733187031641)
                    ·
                      rfl

theorem cell23_3934097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 5].length) (baseStart_3934097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3934097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3934097 prefixEnd_3934097 := by exact prefixLift 3934097
  have htrace : WordTrace (prefixWord ++ tailWord_3934097) baseStart_3934097 baseEnd_3934097 := by
    simpa [prefixWord, tailWord_3934097, baseEnd_3934097] using wordTrace_append hprefix tailTrace_3934097
  have hstable : (prefixWord ++ tailWord_3934097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3934097).length < 2 ^ (prefixWord ++ tailWord_3934097).sum := by decide
  have hdescent : baseEnd_3934097 < baseStart_3934097 := by decide
  rcases family_descends (prefixWord ++ tailWord_3934097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3934144 : List Nat := [2, 1, 1, 2, 3, 2, 3, 2, 3, 4]
def baseStart_3934144 : Nat := 118140960795 + 3934144 * 2 ^ 59
def prefixEnd_3934144 : Nat := 4983230072969 + 3 ^ 40 * 3934144 * 2
def baseEnd_3934144 : Nat := 673368945333986959069069

theorem tailTrace_3934144 : CollatzResearch.WordTrace tailWord_3934144 prefixEnd_3934144 673368945333986959069069 := by
  unfold tailWord_3934144
  simp only [CollatzResearch.WordTrace]
  refine ⟨71745009929637830573876743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95660013239517107431835657 71745009929637830573876743)
  ·
    refine ⟨107617514894456745860815115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71745009929637830573876743 107617514894456745860815115)
    ·
      refine ⟨161426272341685118791222673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107617514894456745860815115 161426272341685118791222673)
      ·
        refine ⟨121069704256263839093417005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161426272341685118791222673 121069704256263839093417005)
        ·
          refine ⟨45401139096098939660031377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121069704256263839093417005 45401139096098939660031377)
          ·
            refine ⟨34050854322074204745023533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45401139096098939660031377 34050854322074204745023533)
            ·
              refine ⟨12769070370777826779383825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34050854322074204745023533 12769070370777826779383825)
              ·
                refine ⟨9576802778083370084537869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12769070370777826779383825 9576802778083370084537869)
                ·
                  refine ⟨3591301041781263781701701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9576802778083370084537869 3591301041781263781701701)
                  ·
                    refine ⟨673368945333986959069069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3591301041781263781701701 673368945333986959069069)
                    ·
                      rfl

theorem cell23_3934144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3, 2, 3, 4].length) (baseStart_3934144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3934144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3934144 prefixEnd_3934144 := by exact prefixLift 3934144
  have htrace : WordTrace (prefixWord ++ tailWord_3934144) baseStart_3934144 baseEnd_3934144 := by
    simpa [prefixWord, tailWord_3934144, baseEnd_3934144] using wordTrace_append hprefix tailTrace_3934144
  have hstable : (prefixWord ++ tailWord_3934144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3934144).length < 2 ^ (prefixWord ++ tailWord_3934144).sum := by decide
  have hdescent : baseEnd_3934144 < baseStart_3934144 := by decide
  rcases family_descends (prefixWord ++ tailWord_3934144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3934177 : List Nat := [1, 2, 3, 1, 2, 1, 3, 1, 1, 2, 6]
def baseStart_3934177 : Nat := 118140960795 + 3934177 * 2 ^ 59
def prefixEnd_3934177 : Nat := 4983230072969 + 3 ^ 40 * 3934177 * 2
def baseEnd_3934177 : Nat := 2020123780863559248094555

theorem tailTrace_3934177 : CollatzResearch.WordTrace tailWord_3934177 prefixEnd_3934177 2020123780863559248094555 := by
  unfold tailWord_3934177
  simp only [CollatzResearch.WordTrace]
  refine ⟨143491223468156107783704785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95660815645437405189136523 143491223468156107783704785)
  ·
    refine ⟨107618417601117080837778589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143491223468156107783704785 107618417601117080837778589)
    ·
      refine ⟨40356906600418905314166971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107618417601117080837778589 40356906600418905314166971)
      ·
        refine ⟨60535359900628357971250457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40356906600418905314166971 60535359900628357971250457)
        ·
          refine ⟨45401519925471268478437843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60535359900628357971250457 45401519925471268478437843)
          ·
            refine ⟨68102279888206902717656765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45401519925471268478437843 68102279888206902717656765)
            ·
              refine ⟨25538354958077588519121287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68102279888206902717656765 25538354958077588519121287)
              ·
                refine ⟨38307532437116382778681931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25538354958077588519121287 38307532437116382778681931)
                ·
                  refine ⟨57461298655674574168022897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38307532437116382778681931 57461298655674574168022897)
                  ·
                    refine ⟨43095973991755930626017173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 57461298655674574168022897 43095973991755930626017173)
                    ·
                      refine ⟨2020123780863559248094555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 43095973991755930626017173 2020123780863559248094555)
                      ·
                        rfl

theorem cell23_3934177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 1, 1, 2, 6].length) (baseStart_3934177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3934177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3934177 prefixEnd_3934177 := by exact prefixLift 3934177
  have htrace : WordTrace (prefixWord ++ tailWord_3934177) baseStart_3934177 baseEnd_3934177 := by
    simpa [prefixWord, tailWord_3934177, baseEnd_3934177] using wordTrace_append hprefix tailTrace_3934177
  have hstable : (prefixWord ++ tailWord_3934177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3934177).length < 2 ^ (prefixWord ++ tailWord_3934177).sum := by decide
  have hdescent : baseEnd_3934177 < baseStart_3934177 := by decide
  rcases family_descends (prefixWord ++ tailWord_3934177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3934187 : List Nat := [1, 1, 1, 1, 2, 3, 1, 3, 5, 5]
def baseStart_3934187 : Nat := 118140960795 + 3934187 * 2 ^ 59
def prefixEnd_3934187 : Nat := 4983230072969 + 3 ^ 40 * 3934187 * 2
def baseEnd_3934187 : Nat := 673376305223368069656503

theorem tailTrace_3934187 : CollatzResearch.WordTrace tailWord_3934187 prefixEnd_3934187 673376305223368069656503 := by
  unfold tailWord_3934187
  simp only [CollatzResearch.WordTrace]
  refine ⟨143491588198119879491568815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95661058798746586327712543 143491588198119879491568815)
  ·
    refine ⟨215237382297179819237353223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143491588198119879491568815 215237382297179819237353223)
    ·
      refine ⟨322856073445769728856029835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215237382297179819237353223 322856073445769728856029835)
      ·
        refine ⟨484284110168654593284044753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 322856073445769728856029835 484284110168654593284044753)
        ·
          refine ⟨363213082626490944963033565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 484284110168654593284044753 363213082626490944963033565)
          ·
            refine ⟨136204905984934104361137587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 363213082626490944963033565 136204905984934104361137587)
            ·
              refine ⟨204307358977401156541706381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136204905984934104361137587 204307358977401156541706381)
              ·
                refine ⟨76615259616525433703139893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 204307358977401156541706381 76615259616525433703139893)
                ·
                  refine ⟨7182680589049259409669365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 76615259616525433703139893 7182680589049259409669365)
                  ·
                    refine ⟨673376305223368069656503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7182680589049259409669365 673376305223368069656503)
                    ·
                      rfl

theorem cell23_3934187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 3, 5, 5].length) (baseStart_3934187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3934187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3934187 prefixEnd_3934187 := by exact prefixLift 3934187
  have htrace : WordTrace (prefixWord ++ tailWord_3934187) baseStart_3934187 baseEnd_3934187 := by
    simpa [prefixWord, tailWord_3934187, baseEnd_3934187] using wordTrace_append hprefix tailTrace_3934187
  have hstable : (prefixWord ++ tailWord_3934187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3934187).length < 2 ^ (prefixWord ++ tailWord_3934187).sum := by decide
  have hdescent : baseEnd_3934187 < baseStart_3934187 := by decide
  rcases family_descends (prefixWord ++ tailWord_3934187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3934201 : List Nat := [1, 2, 1, 3, 1, 4, 2, 2, 3, 1, 3]
def baseStart_3934201 : Nat := 118140960795 + 3934201 * 2 ^ 59
def prefixEnd_3934201 : Nat := 4983230072969 + 3 ^ 40 * 3934201 * 2
def baseEnd_3934201 : Nat := 2020136104399267154194445

theorem tailTrace_3934201 : CollatzResearch.WordTrace tailWord_3934201 prefixEnd_3934201 2020136104399267154194445 := by
  unfold tailWord_3934201
  simp only [CollatzResearch.WordTrace]
  refine ⟨143492098820069159882578457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95661399213379439921718971 143492098820069159882578457)
  ·
    refine ⟨107619074115051869911933843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143492098820069159882578457 107619074115051869911933843)
    ·
      refine ⟨161428611172577804867900765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107619074115051869911933843 161428611172577804867900765)
      ·
        refine ⟨60535729189716676825462787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 161428611172577804867900765 60535729189716676825462787)
        ·
          refine ⟨90803593784575015238194181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60535729189716676825462787 90803593784575015238194181)
          ·
            refine ⟨17025673834607815357161409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 90803593784575015238194181 17025673834607815357161409)
            ·
              refine ⟨12769255375955861517871057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17025673834607815357161409 12769255375955861517871057)
              ·
                refine ⟨9576941531966896138403293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12769255375955861517871057 9576941531966896138403293)
                ·
                  refine ⟨3591353074487586051901235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9576941531966896138403293 3591353074487586051901235)
                  ·
                    refine ⟨5387029611731379077851853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3591353074487586051901235 5387029611731379077851853)
                    ·
                      refine ⟨2020136104399267154194445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5387029611731379077851853 2020136104399267154194445)
                      ·
                        rfl

theorem cell23_3934201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 2, 2, 3, 1, 3].length) (baseStart_3934201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3934201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3934201 prefixEnd_3934201 := by exact prefixLift 3934201
  have htrace : WordTrace (prefixWord ++ tailWord_3934201) baseStart_3934201 baseEnd_3934201 := by
    simpa [prefixWord, tailWord_3934201, baseEnd_3934201] using wordTrace_append hprefix tailTrace_3934201
  have hstable : (prefixWord ++ tailWord_3934201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3934201).length < 2 ^ (prefixWord ++ tailWord_3934201).sum := by decide
  have hdescent : baseEnd_3934201 < baseStart_3934201 := by decide
  rcases family_descends (prefixWord ++ tailWord_3934201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3934207 : List Nat := [1, 1, 2, 2, 1, 2, 1, 2, 2, 5, 4]
def baseStart_3934207 : Nat := 118140960795 + 3934207 * 2 ^ 59
def prefixEnd_3934207 : Nat := 4983230072969 + 3 ^ 40 * 3934207 * 2
def baseEnd_3934207 : Nat := 2020139185283194130719417

theorem tailTrace_3934207 : CollatzResearch.WordTrace tailWord_3934207 prefixEnd_3934207 2020139185283194130719417 := by
  unfold tailWord_3934207
  simp only [CollatzResearch.WordTrace]
  refine ⟨143492317658047422907296875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95661545105364948604864583 143492317658047422907296875)
  ·
    refine ⟨215238476487071134360945313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143492317658047422907296875 215238476487071134360945313)
    ·
      refine ⟨161428857365303350770708985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215238476487071134360945313 161428857365303350770708985)
      ·
        refine ⟨121071643023977513078031739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161428857365303350770708985 121071643023977513078031739)
        ·
          refine ⟨181607464535966269617047609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121071643023977513078031739 181607464535966269617047609)
          ·
            refine ⟨136205598401974702212785707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 181607464535966269617047609 136205598401974702212785707)
            ·
              refine ⟨204308397602962053319178561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136205598401974702212785707 204308397602962053319178561)
              ·
                refine ⟨153231298202221539989383921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 204308397602962053319178561 153231298202221539989383921)
                ·
                  refine ⟨114923473651666154992037941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 153231298202221539989383921 114923473651666154992037941)
                  ·
                    refine ⟨10774075654843702030503557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 114923473651666154992037941 10774075654843702030503557)
                    ·
                      refine ⟨2020139185283194130719417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10774075654843702030503557 2020139185283194130719417)
                      ·
                        rfl

theorem cell23_3934207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 2, 2, 5, 4].length) (baseStart_3934207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3934207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3934207 prefixEnd_3934207 := by exact prefixLift 3934207
  have htrace : WordTrace (prefixWord ++ tailWord_3934207) baseStart_3934207 baseEnd_3934207 := by
    simpa [prefixWord, tailWord_3934207, baseEnd_3934207] using wordTrace_append hprefix tailTrace_3934207
  have hstable : (prefixWord ++ tailWord_3934207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3934207).length < 2 ^ (prefixWord ++ tailWord_3934207).sum := by decide
  have hdescent : baseEnd_3934207 < baseStart_3934207 := by decide
  rcases family_descends (prefixWord ++ tailWord_3934207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3934212 : List Nat := [2, 3, 2, 4, 1, 2, 1, 3, 1, 4]
def baseStart_3934212 : Nat := 118140960795 + 3934212 * 2 ^ 59
def prefixEnd_3934212 : Nat := 4983230072969 + 3 ^ 40 * 3934212 * 2
def baseEnd_3934212 : Nat := 673380584228822203718965

theorem tailTrace_3934212 : CollatzResearch.WordTrace tailWord_3934212 prefixEnd_3934212 673380584228822203718965 := by
  unfold tailWord_3934212
  simp only [CollatzResearch.WordTrace]
  refine ⟨71746250011514654380614445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95661666682019539174152593 71746250011514654380614445)
  ·
    refine ⟨26904843754317995392730417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71746250011514654380614445 26904843754317995392730417)
    ·
      refine ⟨20178632815738496544547813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26904843754317995392730417 20178632815738496544547813)
      ·
        refine ⟨3783493652950968102102715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20178632815738496544547813 3783493652950968102102715)
        ·
          refine ⟨5675240479426452153154073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3783493652950968102102715 5675240479426452153154073)
          ·
            refine ⟨4256430359569839114865555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5675240479426452153154073 4256430359569839114865555)
            ·
              refine ⟨6384645539354758672298333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4256430359569839114865555 6384645539354758672298333)
              ·
                refine ⟨2394242077258034502111875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6384645539354758672298333 2394242077258034502111875)
                ·
                  refine ⟨3591363115887051753167813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2394242077258034502111875 3591363115887051753167813)
                  ·
                    refine ⟨673380584228822203718965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3591363115887051753167813 673380584228822203718965)
                    ·
                      rfl

theorem cell23_3934212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 1, 3, 1, 4].length) (baseStart_3934212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3934212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3934212 prefixEnd_3934212 := by exact prefixLift 3934212
  have htrace : WordTrace (prefixWord ++ tailWord_3934212) baseStart_3934212 baseEnd_3934212 := by
    simpa [prefixWord, tailWord_3934212, baseEnd_3934212] using wordTrace_append hprefix tailTrace_3934212
  have hstable : (prefixWord ++ tailWord_3934212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3934212).length < 2 ^ (prefixWord ++ tailWord_3934212).sum := by decide
  have hdescent : baseEnd_3934212 < baseStart_3934212 := by decide
  rcases family_descends (prefixWord ++ tailWord_3934212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3934224 : List Nat := [2, 1, 1, 1, 1, 1, 1, 4, 1, 8, 2]
def baseStart_3934224 : Nat := 118140960795 + 3934224 * 2 ^ 59
def prefixEnd_3934224 : Nat := 4983230072969 + 3 ^ 40 * 3934224 * 2
def baseEnd_3934224 : Nat := 2020147914454320564206839

theorem tailTrace_3934224 : CollatzResearch.WordTrace tailWord_3934224 prefixEnd_3934224 2020147914454320564206839 := by
  unfold tailWord_3934224
  simp only [CollatzResearch.WordTrace]
  refine ⟨71746468849492917405332863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95661958465990556540443817 71746468849492917405332863)
  ·
    refine ⟨107619703274239376107999295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71746468849492917405332863 107619703274239376107999295)
    ·
      refine ⟨161429554911359064161998943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107619703274239376107999295 161429554911359064161998943)
      ·
        refine ⟨242144332367038596242998415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161429554911359064161998943 242144332367038596242998415)
        ·
          refine ⟨363216498550557894364497623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242144332367038596242998415 363216498550557894364497623)
          ·
            refine ⟨544824747825836841546746435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 363216498550557894364497623 544824747825836841546746435)
            ·
              refine ⟨817237121738755262320119653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 544824747825836841546746435 817237121738755262320119653)
              ·
                refine ⟨153231960326016611685022435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 817237121738755262320119653 153231960326016611685022435)
                ·
                  refine ⟨229847940489024917527533653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 153231960326016611685022435 229847940489024917527533653)
                  ·
                    refine ⟨2693530552605760752275785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 229847940489024917527533653 2693530552605760752275785)
                    ·
                      refine ⟨2020147914454320564206839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2693530552605760752275785 2020147914454320564206839)
                      ·
                        rfl

theorem cell23_3934224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 1, 8, 2].length) (baseStart_3934224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3934224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3934224 prefixEnd_3934224 := by exact prefixLift 3934224
  have htrace : WordTrace (prefixWord ++ tailWord_3934224) baseStart_3934224 baseEnd_3934224 := by
    simpa [prefixWord, tailWord_3934224, baseEnd_3934224] using wordTrace_append hprefix tailTrace_3934224
  have hstable : (prefixWord ++ tailWord_3934224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3934224).length < 2 ^ (prefixWord ++ tailWord_3934224).sum := by decide
  have hdescent : baseEnd_3934224 < baseStart_3934224 := by decide
  rcases family_descends (prefixWord ++ tailWord_3934224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3934258 : List Nat := [3, 2, 1, 1, 2, 5, 1, 2, 1, 1, 4]
def baseStart_3934258 : Nat := 118140960795 + 3934258 * 2 ^ 59
def prefixEnd_3934258 : Nat := 4983230072969 + 3 ^ 40 * 3934258 * 2
def baseEnd_3934258 : Nat := 2020165372796573431181683

theorem tailTrace_3934258 : CollatzResearch.WordTrace tailWord_3934258 prefixEnd_3934258 2020165372796573431181683 := by
  unfold tailWord_3934258
  simp only [CollatzResearch.WordTrace]
  refine ⟨35873544445215664654350857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95662785187241772411602285 35873544445215664654350857)
  ·
    refine ⟨26905158333911748490763143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35873544445215664654350857 26905158333911748490763143)
    ·
      refine ⟨40357737500867622736144715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26905158333911748490763143 40357737500867622736144715)
      ·
        refine ⟨60536606251301434104217073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40357737500867622736144715 60536606251301434104217073)
        ·
          refine ⟨45402454688476075578162805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60536606251301434104217073 45402454688476075578162805)
          ·
            refine ⟨4256480127044632085452763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 45402454688476075578162805 4256480127044632085452763)
            ·
              refine ⟨6384720190566948128179145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4256480127044632085452763 6384720190566948128179145)
              ·
                refine ⟨4788540142925211096134359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6384720190566948128179145 4788540142925211096134359)
                ·
                  refine ⟨7182810214387816644201539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4788540142925211096134359 7182810214387816644201539)
                  ·
                    refine ⟨10774215321581724966302309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7182810214387816644201539 10774215321581724966302309)
                    ·
                      refine ⟨2020165372796573431181683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10774215321581724966302309 2020165372796573431181683)
                      ·
                        rfl

theorem cell23_3934258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 1, 2, 1, 1, 4].length) (baseStart_3934258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3934258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3934258 prefixEnd_3934258 := by exact prefixLift 3934258
  have htrace : WordTrace (prefixWord ++ tailWord_3934258) baseStart_3934258 baseEnd_3934258 := by
    simpa [prefixWord, tailWord_3934258, baseEnd_3934258] using wordTrace_append hprefix tailTrace_3934258
  have hstable : (prefixWord ++ tailWord_3934258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3934258).length < 2 ^ (prefixWord ++ tailWord_3934258).sum := by decide
  have hdescent : baseEnd_3934258 < baseStart_3934258 := by decide
  rcases family_descends (prefixWord ++ tailWord_3934258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3934267 : List Nat := [1, 1, 1, 1, 1, 2, 1, 4, 1, 4, 6]
def baseStart_3934267 : Nat := 118140960795 + 3934267 * 2 ^ 59
def prefixEnd_3934267 : Nat := 4983230072969 + 3 ^ 40 * 3934267 * 2
def baseEnd_3934267 : Nat := 2020169994122463895969141

theorem tailTrace_3934267 : CollatzResearch.WordTrace tailWord_3934267 prefixEnd_3934267 2020169994122463895969141 := by
  unfold tailWord_3934267
  simp only [CollatzResearch.WordTrace]
  refine ⟨143494506037830053154481055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95663004025220035436320703 143494506037830053154481055)
  ·
    refine ⟨215241759056745079731721583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143494506037830053154481055 215241759056745079731721583)
    ·
      refine ⟨322862638585117619597582375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215241759056745079731721583 322862638585117619597582375)
      ·
        refine ⟨484293957877676429396373563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 322862638585117619597582375 484293957877676429396373563)
        ·
          refine ⟨726440936816514644094560345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 484293957877676429396373563 726440936816514644094560345)
          ·
            refine ⟨544830702612385983070920259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 726440936816514644094560345 544830702612385983070920259)
            ·
              refine ⟨817246053918578974606380389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 544830702612385983070920259 817246053918578974606380389)
              ·
                refine ⟨153233635109733557738696323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 817246053918578974606380389 153233635109733557738696323)
                ·
                  refine ⟨229850452664600336608044485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 153233635109733557738696323 229850452664600336608044485)
                  ·
                    refine ⟨43096959874612563114008341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 229850452664600336608044485 43096959874612563114008341)
                    ·
                      refine ⟨2020169994122463895969141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 43096959874612563114008341 2020169994122463895969141)
                      ·
                        rfl

theorem cell23_3934267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 4, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 4, 1, 4, 6].length) (baseStart_3934267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3934267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3934267 prefixEnd_3934267 := by exact prefixLift 3934267
  have htrace : WordTrace (prefixWord ++ tailWord_3934267) baseStart_3934267 baseEnd_3934267 := by
    simpa [prefixWord, tailWord_3934267, baseEnd_3934267] using wordTrace_append hprefix tailTrace_3934267
  have hstable : (prefixWord ++ tailWord_3934267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3934267).length < 2 ^ (prefixWord ++ tailWord_3934267).sum := by decide
  have hdescent : baseEnd_3934267 < baseStart_3934267 := by decide
  rcases family_descends (prefixWord ++ tailWord_3934267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3934308 : List Nat := [2, 3, 1, 1, 2, 1, 4, 3, 2, 1, 3]
def baseStart_3934308 : Nat := 118140960795 + 3934308 * 2 ^ 59
def prefixEnd_3934308 : Nat := 4983230072969 + 3 ^ 40 * 3934308 * 2
def baseEnd_3934308 : Nat := 2020191046829298235556453

theorem tailTrace_3934308 : CollatzResearch.WordTrace tailWord_3934308 prefixEnd_3934308 2020191046829298235556453 := by
  unfold tailWord_3934308
  simp only [CollatzResearch.WordTrace]
  refine ⟨71748000715340758578361789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95664000953787678104482385 71748000715340758578361789)
  ·
    refine ⟨26905500268252784466885671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71748000715340758578361789 26905500268252784466885671)
    ·
      refine ⟨40358250402379176700328507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26905500268252784466885671 40358250402379176700328507)
      ·
        refine ⟨60537375603568765050492761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40358250402379176700328507 60537375603568765050492761)
        ·
          refine ⟨45403031702676573787869571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60537375603568765050492761 45403031702676573787869571)
          ·
            refine ⟨68104547554014860681804357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45403031702676573787869571 68104547554014860681804357)
            ·
              refine ⟨12769602666377786377838317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68104547554014860681804357 12769602666377786377838317)
              ·
                refine ⟨4788600999891669891689369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12769602666377786377838317 4788600999891669891689369)
                ·
                  refine ⟨3591450749918752418767027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4788600999891669891689369 3591450749918752418767027)
                  ·
                    refine ⟨5387176124878128628150541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3591450749918752418767027 5387176124878128628150541)
                    ·
                      refine ⟨2020191046829298235556453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5387176124878128628150541 2020191046829298235556453)
                      ·
                        rfl

theorem cell23_3934308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4, 3, 2, 1, 3].length) (baseStart_3934308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3934308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3934308 prefixEnd_3934308 := by exact prefixLift 3934308
  have htrace : WordTrace (prefixWord ++ tailWord_3934308) baseStart_3934308 baseEnd_3934308 := by
    simpa [prefixWord, tailWord_3934308, baseEnd_3934308] using wordTrace_append hprefix tailTrace_3934308
  have hstable : (prefixWord ++ tailWord_3934308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3934308).length < 2 ^ (prefixWord ++ tailWord_3934308).sum := by decide
  have hdescent : baseEnd_3934308 < baseStart_3934308 := by decide
  rcases family_descends (prefixWord ++ tailWord_3934308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3934318 : List Nat := [4, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2]
def baseStart_3934318 : Nat := 118140960795 + 3934318 * 2 ^ 59
def prefixEnd_3934318 : Nat := 4983230072969 + 3 ^ 40 * 3934318 * 2
def baseEnd_3934318 : Nat := 2020196181635843196431407

theorem tailTrace_3934318 : CollatzResearch.WordTrace tailWord_3934318 prefixEnd_3934318 2020196181635843196431407 := by
  unfold tailWord_3934318
  simp only [CollatzResearch.WordTrace]
  refine ⟨17937045770080661108073451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95664244107096859243058405 17937045770080661108073451)
  ·
    refine ⟨26905568655120991662110177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17937045770080661108073451 26905568655120991662110177)
    ·
      refine ⟨20179176491340743746582633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26905568655120991662110177 20179176491340743746582633)
      ·
        refine ⟨15134382368505557809936975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20179176491340743746582633 15134382368505557809936975)
        ·
          refine ⟨22701573552758336714905463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15134382368505557809936975 22701573552758336714905463)
          ·
            refine ⟨34052360329137505072358195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22701573552758336714905463 34052360329137505072358195)
            ·
              refine ⟨51078540493706257608537293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34052360329137505072358195 51078540493706257608537293)
              ·
                refine ⟨19154452685139846603201485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51078540493706257608537293 19154452685139846603201485)
                ·
                  refine ⟨7182919756927442476200557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19154452685139846603201485 7182919756927442476200557)
                  ·
                    refine ⟨2693594908847790928575209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7182919756927442476200557 2693594908847790928575209)
                    ·
                      refine ⟨2020196181635843196431407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2693594908847790928575209 2020196181635843196431407)
                      ·
                        rfl

theorem cell23_3934318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2].length) (baseStart_3934318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3934318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3934318 prefixEnd_3934318 := by exact prefixLift 3934318
  have htrace : WordTrace (prefixWord ++ tailWord_3934318) baseStart_3934318 baseEnd_3934318 := by
    simpa [prefixWord, tailWord_3934318, baseEnd_3934318] using wordTrace_append hprefix tailTrace_3934318
  have hstable : (prefixWord ++ tailWord_3934318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3934318).length < 2 ^ (prefixWord ++ tailWord_3934318).sum := by decide
  have hdescent : baseEnd_3934318 < baseStart_3934318 := by decide
  rcases family_descends (prefixWord ++ tailWord_3934318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3934365 : List Nat := [1, 4, 2, 1, 1, 5, 1, 1, 1, 4, 2]
def baseStart_3934365 : Nat := 118140960795 + 3934365 * 2 ^ 59
def prefixEnd_3934365 : Nat := 4983230072969 + 3 ^ 40 * 3934365 * 2
def baseEnd_3934365 : Nat := 2020220315226604512543691

theorem tailTrace_3934365 : CollatzResearch.WordTrace tailWord_3934365 prefixEnd_3934365 2020220315226604512543691 := by
  unfold tailWord_3934365
  simp only [CollatzResearch.WordTrace]
  refine ⟨143498080391475015891548549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95665386927650010594365699 143498080391475015891548549)
  ·
    refine ⟨26905890073401565479665353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 143498080391475015891548549 26905890073401565479665353)
    ·
      refine ⟨20179417555051174109749015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26905890073401565479665353 20179417555051174109749015)
      ·
        refine ⟨30269126332576761164623523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20179417555051174109749015 30269126332576761164623523)
        ·
          refine ⟨45403689498865141746935285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30269126332576761164623523 45403689498865141746935285)
          ·
            refine ⟨4256595890518607038775183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 45403689498865141746935285 4256595890518607038775183)
            ·
              refine ⟨6384893835777910558162775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4256595890518607038775183 6384893835777910558162775)
              ·
                refine ⟨9577340753666865837244163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6384893835777910558162775 9577340753666865837244163)
                ·
                  refine ⟨14366011130500298755866245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9577340753666865837244163 14366011130500298755866245)
                  ·
                    refine ⟨2693627086968806016724921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14366011130500298755866245 2693627086968806016724921)
                    ·
                      refine ⟨2020220315226604512543691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2693627086968806016724921 2020220315226604512543691)
                      ·
                        rfl

theorem cell23_3934365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 1, 1, 1, 4, 2].length) (baseStart_3934365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3934365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3934365 prefixEnd_3934365 := by exact prefixLift 3934365
  have htrace : WordTrace (prefixWord ++ tailWord_3934365) baseStart_3934365 baseEnd_3934365 := by
    simpa [prefixWord, tailWord_3934365, baseEnd_3934365] using wordTrace_append hprefix tailTrace_3934365
  have hstable : (prefixWord ++ tailWord_3934365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3934365).length < 2 ^ (prefixWord ++ tailWord_3934365).sum := by decide
  have hdescent : baseEnd_3934365 < baseStart_3934365 := by decide
  rcases family_descends (prefixWord ++ tailWord_3934365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3934431 : List Nat := [1, 1, 2, 3, 2, 1, 1, 3, 5, 4]
def baseStart_3934431 : Nat := 118140960795 + 3934431 * 2 ^ 59
def prefixEnd_3934431 : Nat := 4983230072969 + 3 ^ 40 * 3934431 * 2
def baseEnd_3934431 : Nat := 673418068316600418106129

theorem tailTrace_3934431 : CollatzResearch.WordTrace tailWord_3934431 prefixEnd_3934431 673418068316600418106129 := by
  unfold tailWord_3934431
  simp only [CollatzResearch.WordTrace]
  refine ⟨143500487609235909163451147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95666991739490606108967431 143500487609235909163451147)
  ·
    refine ⟨215250731413853863745176721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143500487609235909163451147 215250731413853863745176721)
    ·
      refine ⟨161438048560390397808882541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215250731413853863745176721 161438048560390397808882541)
      ·
        refine ⟨60539268210146399178330953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 161438048560390397808882541 60539268210146399178330953)
        ·
          refine ⟨45404451157609799383748215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60539268210146399178330953 45404451157609799383748215)
          ·
            refine ⟨68106676736414699075622323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45404451157609799383748215 68106676736414699075622323)
            ·
              refine ⟨102160015104622048613433485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68106676736414699075622323 102160015104622048613433485)
              ·
                refine ⟨38310005664233268230037557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 102160015104622048613433485 38310005664233268230037557)
                ·
                  refine ⟨3591563031021868896566021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38310005664233268230037557 3591563031021868896566021)
                  ·
                    refine ⟨673418068316600418106129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3591563031021868896566021 673418068316600418106129)
                    ·
                      rfl

theorem cell23_3934431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 3, 5, 4].length) (baseStart_3934431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3934431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3934431 prefixEnd_3934431 := by exact prefixLift 3934431
  have htrace : WordTrace (prefixWord ++ tailWord_3934431) baseStart_3934431 baseEnd_3934431 := by
    simpa [prefixWord, tailWord_3934431, baseEnd_3934431] using wordTrace_append hprefix tailTrace_3934431
  have hstable : (prefixWord ++ tailWord_3934431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3934431).length < 2 ^ (prefixWord ++ tailWord_3934431).sum := by decide
  have hdescent : baseEnd_3934431 < baseStart_3934431 := by decide
  rcases family_descends (prefixWord ++ tailWord_3934431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3934435 : List Nat := [1, 1, 1, 8, 1, 1, 2, 1, 2, 5]
def baseStart_3934435 : Nat := 118140960795 + 3934435 * 2 ^ 59
def prefixEnd_3934435 : Nat := 4983230072969 + 3 ^ 40 * 3934435 * 2
def baseEnd_3934435 : Nat := 673418752957473079556123

theorem tailTrace_3934435 : CollatzResearch.WordTrace tailWord_3934435 prefixEnd_3934435 673418752957473079556123 := by
  unfold tailWord_3934435
  simp only [CollatzResearch.WordTrace]
  refine ⟨143500633501221417846596759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95667089000814278564397839 143500633501221417846596759)
  ·
    refine ⟨215250950251832126769895139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143500633501221417846596759 215250950251832126769895139)
    ·
      refine ⟨322876425377748190154842709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215250950251832126769895139 322876425377748190154842709)
      ·
        refine ⟨3783708109895486603377063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 322876425377748190154842709 3783708109895486603377063)
        ·
          refine ⟨5675562164843229905065595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3783708109895486603377063 5675562164843229905065595)
          ·
            refine ⟨8513343247264844857598393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5675562164843229905065595 8513343247264844857598393)
            ·
              refine ⟨6385007435448633643198795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8513343247264844857598393 6385007435448633643198795)
              ·
                refine ⟨9577511153172950464798193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6385007435448633643198795 9577511153172950464798193)
                ·
                  refine ⟨7183133364879712848598645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9577511153172950464798193 7183133364879712848598645)
                  ·
                    refine ⟨673418752957473079556123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7183133364879712848598645 673418752957473079556123)
                    ·
                      rfl

theorem cell23_3934435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 2, 1, 2, 5].length) (baseStart_3934435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3934435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3934435 prefixEnd_3934435 := by exact prefixLift 3934435
  have htrace : WordTrace (prefixWord ++ tailWord_3934435) baseStart_3934435 baseEnd_3934435 := by
    simpa [prefixWord, tailWord_3934435, baseEnd_3934435] using wordTrace_append hprefix tailTrace_3934435
  have hstable : (prefixWord ++ tailWord_3934435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3934435).length < 2 ^ (prefixWord ++ tailWord_3934435).sum := by decide
  have hdescent : baseEnd_3934435 < baseStart_3934435 := by decide
  rcases family_descends (prefixWord ++ tailWord_3934435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3934441 : List Nat := [1, 2, 1, 1, 1, 2, 2, 2, 6, 2, 3]
def baseStart_3934441 : Nat := 118140960795 + 3934441 * 2 ^ 59
def prefixEnd_3934441 : Nat := 4983230072969 + 3 ^ 40 * 3934441 * 2
def baseEnd_3934441 : Nat := 2020259339756346215193341

theorem tailTrace_3934441 : CollatzResearch.WordTrace tailWord_3934441 prefixEnd_3934441 2020259339756346215193341 := by
  unfold tailWord_3934441
  simp only [CollatzResearch.WordTrace]
  refine ⟨143500852339199680871315177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95667234892799787247543451 143500852339199680871315177)
  ·
    refine ⟨107625639254399760653486383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143500852339199680871315177 107625639254399760653486383)
    ·
      refine ⟨161438458881599640980229575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107625639254399760653486383 161438458881599640980229575)
      ·
        refine ⟨242157688322399461470344363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161438458881599640980229575 242157688322399461470344363)
        ·
          refine ⟨363236532483599192205516545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242157688322399461470344363 363236532483599192205516545)
          ·
            refine ⟨272427399362699394154137409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 363236532483599192205516545 272427399362699394154137409)
            ·
              refine ⟨204320549522024545615603057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 272427399362699394154137409 204320549522024545615603057)
              ·
                refine ⟨153240412141518409211702293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 204320549522024545615603057 153240412141518409211702293)
                ·
                  refine ⟨7183144319133675431798545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 153240412141518409211702293 7183144319133675431798545)
                  ·
                    refine ⟨5387358239350256573848909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7183144319133675431798545 5387358239350256573848909)
                    ·
                      refine ⟨2020259339756346215193341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5387358239350256573848909 2020259339756346215193341)
                      ·
                        rfl

theorem cell23_3934441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 2, 6, 2, 3].length) (baseStart_3934441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3934441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3934441 prefixEnd_3934441 := by exact prefixLift 3934441
  have htrace : WordTrace (prefixWord ++ tailWord_3934441) baseStart_3934441 baseEnd_3934441 := by
    simpa [prefixWord, tailWord_3934441, baseEnd_3934441] using wordTrace_append hprefix tailTrace_3934441
  have hstable : (prefixWord ++ tailWord_3934441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3934441).length < 2 ^ (prefixWord ++ tailWord_3934441).sum := by decide
  have hdescent : baseEnd_3934441 < baseStart_3934441 := by decide
  rcases family_descends (prefixWord ++ tailWord_3934441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3934458 : List Nat := [3, 1, 1, 1, 1, 5, 2, 2, 2, 2, 3]
def baseStart_3934458 : Nat := 118140960795 + 3934458 * 2 ^ 59
def prefixEnd_3934458 : Nat := 4983230072969 + 3 ^ 40 * 3934458 * 2
def baseEnd_3934458 : Nat := 2020268068927472648680763

theorem tailTrace_3934458 : CollatzResearch.WordTrace tailWord_3934458 prefixEnd_3934458 2020268068927472648680763 := by
  unfold tailWord_3934458
  simp only [CollatzResearch.WordTrace]
  refine ⟨35875368095034523193671007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95667648253425395183122685 35875368095034523193671007)
  ·
    refine ⟨53813052142551784790506511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35875368095034523193671007 53813052142551784790506511)
    ·
      refine ⟨80719578213827677185759767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53813052142551784790506511 80719578213827677185759767)
      ·
        refine ⟨121079367320741515778639651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80719578213827677185759767 121079367320741515778639651)
        ·
          refine ⟨181619050981112273667959477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121079367320741515778639651 181619050981112273667959477)
          ·
            refine ⟨17026786029479275656371201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 181619050981112273667959477 17026786029479275656371201)
            ·
              refine ⟨12770089522109456742278401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17026786029479275656371201 12770089522109456742278401)
              ·
                refine ⟨9577567141582092556708801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12770089522109456742278401 9577567141582092556708801)
                ·
                  refine ⟨7183175356186569417531601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9577567141582092556708801 7183175356186569417531601)
                  ·
                    refine ⟨5387381517139927063148701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7183175356186569417531601 5387381517139927063148701)
                    ·
                      refine ⟨2020268068927472648680763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5387381517139927063148701 2020268068927472648680763)
                      ·
                        rfl

theorem cell23_3934458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 2, 2, 2, 2, 3].length) (baseStart_3934458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3934458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3934458 prefixEnd_3934458 := by exact prefixLift 3934458
  have htrace : WordTrace (prefixWord ++ tailWord_3934458) baseStart_3934458 baseEnd_3934458 := by
    simpa [prefixWord, tailWord_3934458, baseEnd_3934458] using wordTrace_append hprefix tailTrace_3934458
  have hstable : (prefixWord ++ tailWord_3934458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3934458).length < 2 ^ (prefixWord ++ tailWord_3934458).sum := by decide
  have hdescent : baseEnd_3934458 < baseStart_3934458 := by decide
  rcases family_descends (prefixWord ++ tailWord_3934458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3934465 : List Nat := [1, 2, 4, 1, 1, 2, 3, 4, 1, 4]
def baseStart_3934465 : Nat := 118140960795 + 3934465 * 2 ^ 59
def prefixEnd_3934465 : Nat := 4983230072969 + 3 ^ 40 * 3934465 * 2
def baseEnd_3934465 : Nat := 673423887764018040431077

theorem tailTrace_3934465 : CollatzResearch.WordTrace tailWord_3934465 prefixEnd_3934465 673423887764018040431077 := by
  unfold tailWord_3934465
  simp only [CollatzResearch.WordTrace]
  refine ⟨143501727691112732970188849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95667818460741821980125899 143501727691112732970188849)
  ·
    refine ⟨107626295768334549727641637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143501727691112732970188849 107626295768334549727641637)
    ·
      refine ⟨20179930456562728073932807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 107626295768334549727641637 20179930456562728073932807)
      ·
        refine ⟨30269895684844092110899211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20179930456562728073932807 30269895684844092110899211)
        ·
          refine ⟨45404843527266138166348817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30269895684844092110899211 45404843527266138166348817)
          ·
            refine ⟨34053632645449603624761613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45404843527266138166348817 34053632645449603624761613)
            ·
              refine ⟨12770112242043601359285605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34053632645449603624761613 12770112242043601359285605)
              ·
                refine ⟨2394396045383175254866051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12770112242043601359285605 2394396045383175254866051)
                ·
                  refine ⟨3591594068074762882299077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2394396045383175254866051 3591594068074762882299077)
                  ·
                    refine ⟨673423887764018040431077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3591594068074762882299077 673423887764018040431077)
                    ·
                      rfl

theorem cell23_3934465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 3, 4, 1, 4].length) (baseStart_3934465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3934465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3934465 prefixEnd_3934465 := by exact prefixLift 3934465
  have htrace : WordTrace (prefixWord ++ tailWord_3934465) baseStart_3934465 baseEnd_3934465 := by
    simpa [prefixWord, tailWord_3934465, baseEnd_3934465] using wordTrace_append hprefix tailTrace_3934465
  have hstable : (prefixWord ++ tailWord_3934465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3934465).length < 2 ^ (prefixWord ++ tailWord_3934465).sum := by decide
  have hdescent : baseEnd_3934465 < baseStart_3934465 := by decide
  rcases family_descends (prefixWord ++ tailWord_3934465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3934491 : List Nat := [1, 1, 1, 1, 1, 1, 8, 1, 3, 5]
def baseStart_3934491 : Nat := 118140960795 + 3934491 * 2 ^ 59
def prefixEnd_3934491 : Nat := 4983230072969 + 3 ^ 40 * 3934491 * 2
def baseEnd_3934491 : Nat := 673428337929690339856037

theorem tailTrace_3934491 : CollatzResearch.WordTrace tailWord_3934491 prefixEnd_3934491 673428337929690339856037 := by
  unfold tailWord_3934491
  simp only [CollatzResearch.WordTrace]
  refine ⟨143502675989018539410635327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95668450659345692940423551 143502675989018539410635327)
  ·
    refine ⟨215254013983527809115952991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143502675989018539410635327 215254013983527809115952991)
    ·
      refine ⟨322881020975291713673929487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215254013983527809115952991 322881020975291713673929487)
      ·
        refine ⟨484321531462937570510894231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 322881020975291713673929487 484321531462937570510894231)
        ·
          refine ⟨726482297194406355766341347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 484321531462937570510894231 726482297194406355766341347)
          ·
            refine ⟨1089723445791609533649512021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 726482297194406355766341347 1089723445791609533649512021)
            ·
              refine ⟨12770196630370424222455219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1089723445791609533649512021 12770196630370424222455219)
              ·
                refine ⟨19155294945555636333682829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12770196630370424222455219 19155294945555636333682829)
                ·
                  refine ⟨7183235604583363625131061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19155294945555636333682829 7183235604583363625131061)
                  ·
                    refine ⟨673428337929690339856037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7183235604583363625131061 673428337929690339856037)
                    ·
                      rfl

theorem cell23_3934491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8, 1, 3, 5].length) (baseStart_3934491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3934491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3934491 prefixEnd_3934491 := by exact prefixLift 3934491
  have htrace : WordTrace (prefixWord ++ tailWord_3934491) baseStart_3934491 baseEnd_3934491 := by
    simpa [prefixWord, tailWord_3934491, baseEnd_3934491] using wordTrace_append hprefix tailTrace_3934491
  have hstable : (prefixWord ++ tailWord_3934491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3934491).length < 2 ^ (prefixWord ++ tailWord_3934491).sum := by decide
  have hdescent : baseEnd_3934491 < baseStart_3934491 := by decide
  rcases family_descends (prefixWord ++ tailWord_3934491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3934522 : List Nat := [3, 1, 1, 1, 4, 2, 2, 4, 1, 1, 3]
def baseStart_3934522 : Nat := 118140960795 + 3934522 * 2 ^ 59
def prefixEnd_3934522 : Nat := 4983230072969 + 3 ^ 40 * 3934522 * 2
def baseEnd_3934522 : Nat := 2020300931689360398280469

theorem tailTrace_3934522 : CollatzResearch.WordTrace tailWord_3934522 prefixEnd_3934522 2020300931689360398280469 := by
  unfold tailWord_3934522
  simp only [CollatzResearch.WordTrace]
  refine ⟨35875951662976557926253455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95669204434604154470009213 35875951662976557926253455)
  ·
    refine ⟨53813927494464836889380183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35875951662976557926253455 53813927494464836889380183)
    ·
      refine ⟨80720891241697255334070275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53813927494464836889380183 80720891241697255334070275)
      ·
        refine ⟨121081336862545883001105413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80720891241697255334070275 121081336862545883001105413)
        ·
          refine ⟨22702750661727353062707265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 121081336862545883001105413 22702750661727353062707265)
          ·
            refine ⟨17027062996295514797030449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22702750661727353062707265 17027062996295514797030449)
            ·
              refine ⟨12770297247221636097772837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17027062996295514797030449 12770297247221636097772837)
              ·
                refine ⟨2394430733854056768332407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12770297247221636097772837 2394430733854056768332407)
                ·
                  refine ⟨3591646100781085152498611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2394430733854056768332407 3591646100781085152498611)
                  ·
                    refine ⟨5387469151171627728747917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3591646100781085152498611 5387469151171627728747917)
                    ·
                      refine ⟨2020300931689360398280469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5387469151171627728747917 2020300931689360398280469)
                      ·
                        rfl

theorem cell23_3934522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 2, 4, 1, 1, 3].length) (baseStart_3934522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3934522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3934522 prefixEnd_3934522 := by exact prefixLift 3934522
  have htrace : WordTrace (prefixWord ++ tailWord_3934522) baseStart_3934522 baseEnd_3934522 := by
    simpa [prefixWord, tailWord_3934522, baseEnd_3934522] using wordTrace_append hprefix tailTrace_3934522
  have hstable : (prefixWord ++ tailWord_3934522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3934522).length < 2 ^ (prefixWord ++ tailWord_3934522).sum := by decide
  have hdescent : baseEnd_3934522 < baseStart_3934522 := by decide
  rcases family_descends (prefixWord ++ tailWord_3934522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3934531 : List Nat := [1, 1, 1, 3, 1, 3, 3, 1, 3, 1, 5]
def baseStart_3934531 : Nat := 118140960795 + 3934531 * 2 ^ 59
def prefixEnd_3934531 : Nat := 4983230072969 + 3 ^ 40 * 3934531 * 2
def baseEnd_3934531 : Nat := 2020305553015250863067927

theorem tailTrace_3934531 : CollatzResearch.WordTrace tailWord_3934531 prefixEnd_3934531 2020305553015250863067927 := by
  unfold tailWord_3934531
  simp only [CollatzResearch.WordTrace]
  refine ⟨143504134908873626242091447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95669423272582417494727631 143504134908873626242091447)
  ·
    refine ⟨215256202363310439363137171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143504134908873626242091447 215256202363310439363137171)
    ·
      refine ⟨322884303544965659044705757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215256202363310439363137171 322884303544965659044705757)
      ·
        refine ⟨121081613829362122141764659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 322884303544965659044705757 121081613829362122141764659)
        ·
          refine ⟨181622420744043183212646989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121081613829362122141764659 181622420744043183212646989)
          ·
            refine ⟨68108407779016193704742621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 181622420744043183212646989 68108407779016193704742621)
            ·
              refine ⟨25540652917131072639278483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68108407779016193704742621 25540652917131072639278483)
              ·
                refine ⟨38310979375696608958917725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25540652917131072639278483 38310979375696608958917725)
                ·
                  refine ⟨14366617265886228359594147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38310979375696608958917725 14366617265886228359594147)
                  ·
                    refine ⟨21549925898829342539391221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14366617265886228359594147 21549925898829342539391221)
                    ·
                      refine ⟨2020305553015250863067927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21549925898829342539391221 2020305553015250863067927)
                      ·
                        rfl

theorem cell23_3934531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 1, 3, 1, 5].length) (baseStart_3934531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3934531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3934531 prefixEnd_3934531 := by exact prefixLift 3934531
  have htrace : WordTrace (prefixWord ++ tailWord_3934531) baseStart_3934531 baseEnd_3934531 := by
    simpa [prefixWord, tailWord_3934531, baseEnd_3934531] using wordTrace_append hprefix tailTrace_3934531
  have hstable : (prefixWord ++ tailWord_3934531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3934531).length < 2 ^ (prefixWord ++ tailWord_3934531).sum := by decide
  have hdescent : baseEnd_3934531 < baseStart_3934531 := by decide
  rcases family_descends (prefixWord ++ tailWord_3934531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3934545 : List Nat := [1, 2, 2, 1, 4, 3, 2, 2, 1, 1, 4]
def baseStart_3934545 : Nat := 118140960795 + 3934545 * 2 ^ 59
def prefixEnd_3934545 : Nat := 4983230072969 + 3 ^ 40 * 3934545 * 2
def baseEnd_3934545 : Nat := 2020312741744413808292863

theorem tailTrace_3934545 : CollatzResearch.WordTrace tailWord_3934545 prefixEnd_3934545 2020312741744413808292863 := by
  unfold tailWord_3934545
  simp only [CollatzResearch.WordTrace]
  refine ⟨143504645530822906633101089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95669763687215271088734059 143504645530822906633101089)
  ·
    refine ⟨107628484148117179974825817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143504645530822906633101089 107628484148117179974825817)
    ·
      refine ⟨80721363111087884981119363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107628484148117179974825817 80721363111087884981119363)
      ·
        refine ⟨121082044666631827471679045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80721363111087884981119363 121082044666631827471679045)
        ·
          refine ⟨22702883374993467650939821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 121082044666631827471679045 22702883374993467650939821)
          ·
            refine ⟨8513581265622550369102433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22702883374993467650939821 8513581265622550369102433)
            ·
              refine ⟨6385185949216912776826825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8513581265622550369102433 6385185949216912776826825)
              ·
                refine ⟨4788889461912684582620119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6385185949216912776826825 4788889461912684582620119)
                ·
                  refine ⟨7183334192869026873930179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4788889461912684582620119 7183334192869026873930179)
                  ·
                    refine ⟨10775001289303540310895269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7183334192869026873930179 10775001289303540310895269)
                    ·
                      refine ⟨2020312741744413808292863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10775001289303540310895269 2020312741744413808292863)
                      ·
                        rfl

theorem cell23_3934545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 2, 2, 1, 1, 4].length) (baseStart_3934545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3934545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3934545 prefixEnd_3934545 := by exact prefixLift 3934545
  have htrace : WordTrace (prefixWord ++ tailWord_3934545) baseStart_3934545 baseEnd_3934545 := by
    simpa [prefixWord, tailWord_3934545, baseEnd_3934545] using wordTrace_append hprefix tailTrace_3934545
  have hstable : (prefixWord ++ tailWord_3934545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3934545).length < 2 ^ (prefixWord ++ tailWord_3934545).sum := by decide
  have hdescent : baseEnd_3934545 < baseStart_3934545 := by decide
  rcases family_descends (prefixWord ++ tailWord_3934545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3934551 : List Nat := [1, 1, 3, 2, 3, 1, 3, 9]
def baseStart_3934551 : Nat := 118140960795 + 3934551 * 2 ^ 59
def prefixEnd_3934551 : Nat := 4983230072969 + 3 ^ 40 * 3934551 * 2
def baseEnd_3934551 : Nat := 74826511949197806845105

theorem tailTrace_3934551 : CollatzResearch.WordTrace tailWord_3934551 prefixEnd_3934551 74826511949197806845105 := by
  unfold tailWord_3934551
  simp only [CollatzResearch.WordTrace]
  refine ⟨143504864368801169657819507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95669909579200779771879671 143504864368801169657819507)
  ·
    refine ⟨215257296553201754486729261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143504864368801169657819507 215257296553201754486729261)
    ·
      refine ⟨80721486207450657932523473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 215257296553201754486729261 80721486207450657932523473)
      ·
        refine ⟨60541114655587993449392605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80721486207450657932523473 60541114655587993449392605)
        ·
          refine ⟨22702917995845497543522227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60541114655587993449392605 22702917995845497543522227)
          ·
            refine ⟨34054376993768246315283341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22702917995845497543522227 34054376993768246315283341)
            ·
              refine ⟨12770391372663092368231253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34054376993768246315283341 12770391372663092368231253)
              ·
                refine ⟨74826511949197806845105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 12770391372663092368231253 74826511949197806845105)
                ·
                  rfl

theorem cell23_3934551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 3, 9].length) (baseStart_3934551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3934551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3934551 prefixEnd_3934551 := by exact prefixLift 3934551
  have htrace : WordTrace (prefixWord ++ tailWord_3934551) baseStart_3934551 baseEnd_3934551 := by
    simpa [prefixWord, tailWord_3934551, baseEnd_3934551] using wordTrace_append hprefix tailTrace_3934551
  have hstable : (prefixWord ++ tailWord_3934551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3934551).length < 2 ^ (prefixWord ++ tailWord_3934551).sum := by decide
  have hdescent : baseEnd_3934551 < baseStart_3934551 := by decide
  rcases family_descends (prefixWord ++ tailWord_3934551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3934565 : List Nat := [1, 3, 1, 3, 1, 3, 2, 3, 1, 2, 3]
def baseStart_3934565 : Nat := 118140960795 + 3934565 * 2 ^ 59
def prefixEnd_3934565 : Nat := 4983230072969 + 3 ^ 40 * 3934565 * 2
def baseEnd_3934565 : Nat := 2020323011357503730042771

theorem tailTrace_3934565 : CollatzResearch.WordTrace tailWord_3934565 prefixEnd_3934565 2020323011357503730042771 := by
  unfold tailWord_3934565
  simp only [CollatzResearch.WordTrace]
  refine ⟨143505374990750450048829149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95670249993833633365886099 143505374990750450048829149)
  ·
    refine ⟨53814515621531418768310931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143505374990750450048829149 53814515621531418768310931)
    ·
      refine ⟨80721773432297128152466397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53814515621531418768310931 80721773432297128152466397)
      ·
        refine ⟨30270665037111423057174899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80721773432297128152466397 30270665037111423057174899)
        ·
          refine ⟨45405997555667134585762349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30270665037111423057174899 45405997555667134585762349)
          ·
            refine ⟨17027249083375175469660881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45405997555667134585762349 17027249083375175469660881)
            ·
              refine ⟨12770436812531381602245661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17027249083375175469660881 12770436812531381602245661)
              ·
                refine ⟨4788913804699268100842123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12770436812531381602245661 4788913804699268100842123)
                ·
                  refine ⟨7183370707048902151263185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4788913804699268100842123 7183370707048902151263185)
                  ·
                    refine ⟨5387528030286676613447389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7183370707048902151263185 5387528030286676613447389)
                    ·
                      refine ⟨2020323011357503730042771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5387528030286676613447389 2020323011357503730042771)
                      ·
                        rfl

theorem cell23_3934565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 2, 3, 1, 2, 3].length) (baseStart_3934565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3934565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3934565 prefixEnd_3934565 := by exact prefixLift 3934565
  have htrace : WordTrace (prefixWord ++ tailWord_3934565) baseStart_3934565 baseEnd_3934565 := by
    simpa [prefixWord, tailWord_3934565, baseEnd_3934565] using wordTrace_append hprefix tailTrace_3934565
  have hstable : (prefixWord ++ tailWord_3934565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3934565).length < 2 ^ (prefixWord ++ tailWord_3934565).sum := by decide
  have hdescent : baseEnd_3934565 < baseStart_3934565 := by decide
  rcases family_descends (prefixWord ++ tailWord_3934565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3934568 : List Nat := [2, 1, 4, 2, 2, 3, 9]
def baseStart_3934568 : Nat := 118140960795 + 3934568 * 2 ^ 59
def prefixEnd_3934568 : Nat := 4983230072969 + 3 ^ 40 * 3934568 * 2
def baseEnd_3934568 : Nat := 24942278417277373065497

theorem tailTrace_3934568 : CollatzResearch.WordTrace tailWord_3934568 prefixEnd_3934568 24942278417277373065497 := by
  unfold tailWord_3934568
  simp only [CollatzResearch.WordTrace]
  refine ⟨71752742204869790780594179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95670322939826387707458905 71752742204869790780594179)
  ·
    refine ⟨107629113307304686170891269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71752742204869790780594179 107629113307304686170891269)
    ·
      refine ⟨20180458745119628657042113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 107629113307304686170891269 20180458745119628657042113)
      ·
        refine ⟨15135344058839721492781585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20180458745119628657042113 15135344058839721492781585)
        ·
          refine ⟨11351508044129791119586189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15135344058839721492781585 11351508044129791119586189)
          ·
            refine ⟨4256815516548671669844821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11351508044129791119586189 4256815516548671669844821)
            ·
              refine ⟨24942278417277373065497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4256815516548671669844821 24942278417277373065497)
              ·
                rfl

theorem cell23_3934568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 9].length) (baseStart_3934568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3934568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3934568 prefixEnd_3934568 := by exact prefixLift 3934568
  have htrace : WordTrace (prefixWord ++ tailWord_3934568) baseStart_3934568 baseEnd_3934568 := by
    simpa [prefixWord, tailWord_3934568, baseEnd_3934568] using wordTrace_append hprefix tailTrace_3934568
  have hstable : (prefixWord ++ tailWord_3934568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3934568).length < 2 ^ (prefixWord ++ tailWord_3934568).sum := by decide
  have hdescent : baseEnd_3934568 < baseStart_3934568 := by decide
  rcases family_descends (prefixWord ++ tailWord_3934568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3934591 : List Nat := [1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 5]
def baseStart_3934591 : Nat := 118140960795 + 3934591 * 2 ^ 59
def prefixEnd_3934591 : Nat := 4983230072969 + 3 ^ 40 * 3934591 * 2
def baseEnd_3934591 : Nat := 2020336361854520628317651

theorem tailTrace_3934591 : CollatzResearch.WordTrace tailWord_3934591 prefixEnd_3934591 2020336361854520628317651 := by
  unfold tailWord_3934591
  simp only [CollatzResearch.WordTrace]
  refine ⟨143506323288656256489275627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95670882192437504326183751 143506323288656256489275627)
  ·
    refine ⟨215259484932984384733913441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143506323288656256489275627 215259484932984384733913441)
    ·
      refine ⟨161444613699738288550435081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215259484932984384733913441 161444613699738288550435081)
      ·
        refine ⟨121083460274803716412826311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161444613699738288550435081 121083460274803716412826311)
        ·
          refine ⟨181625190412205574619239467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121083460274803716412826311 181625190412205574619239467)
          ·
            refine ⟨272437785618308361928859201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181625190412205574619239467 272437785618308361928859201)
            ·
              refine ⟨204328339213731271446644401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 272437785618308361928859201 204328339213731271446644401)
              ·
                refine ⟨153246254410298453584983301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 204328339213731271446644401 153246254410298453584983301)
                ·
                  refine ⟨28733672701930960047184369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 153246254410298453584983301 28733672701930960047184369)
                  ·
                    refine ⟨21550254526448220035388277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28733672701930960047184369 21550254526448220035388277)
                    ·
                      refine ⟨2020336361854520628317651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21550254526448220035388277 2020336361854520628317651)
                      ·
                        rfl

theorem cell23_3934591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 5].length) (baseStart_3934591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3934591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3934591 prefixEnd_3934591 := by exact prefixLift 3934591
  have htrace : WordTrace (prefixWord ++ tailWord_3934591) baseStart_3934591 baseEnd_3934591 := by
    simpa [prefixWord, tailWord_3934591, baseEnd_3934591] using wordTrace_append hprefix tailTrace_3934591
  have hstable : (prefixWord ++ tailWord_3934591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3934591).length < 2 ^ (prefixWord ++ tailWord_3934591).sum := by decide
  have hdescent : baseEnd_3934591 < baseStart_3934591 := by decide
  rcases family_descends (prefixWord ++ tailWord_3934591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3934612 : List Nat := [2, 4, 2, 1, 3, 1, 1, 2, 1, 3, 3]
def baseStart_3934612 : Nat := 118140960795 + 3934612 * 2 ^ 59
def prefixEnd_3934612 : Nat := 4983230072969 + 3 ^ 40 * 3934612 * 2
def baseEnd_3934612 : Nat := 2020347144948265046155055

theorem tailTrace_3934612 : CollatzResearch.WordTrace tailWord_3934612 prefixEnd_3934612 2020347144948265046155055 := by
  unfold tailWord_3934612
  simp only [CollatzResearch.WordTrace]
  refine ⟨71753544610790088537895045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95671392814386784717193393 71753544610790088537895045)
  ·
    refine ⟨13453789614523141600855321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71753544610790088537895045 13453789614523141600855321)
    ·
      refine ⟨10090342210892356200641491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13453789614523141600855321 10090342210892356200641491)
      ·
        refine ⟨15135513316338534300962237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10090342210892356200641491 15135513316338534300962237)
        ·
          refine ⟨5675817493626950362860839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15135513316338534300962237 5675817493626950362860839)
          ·
            refine ⟨8513726240440425544291259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5675817493626950362860839 8513726240440425544291259)
            ·
              refine ⟨12770589360660638316436889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8513726240440425544291259 12770589360660638316436889)
              ·
                refine ⟨9577942020495478737327667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12770589360660638316436889 9577942020495478737327667)
                ·
                  refine ⟨14366913030743218105991501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9577942020495478737327667 14366913030743218105991501)
                  ·
                    refine ⟨5387592386528706789746813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14366913030743218105991501 5387592386528706789746813)
                    ·
                      refine ⟨2020347144948265046155055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5387592386528706789746813 2020347144948265046155055)
                      ·
                        rfl

theorem cell23_3934612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 1, 2, 1, 3, 3].length) (baseStart_3934612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3934612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3934612 prefixEnd_3934612 := by exact prefixLift 3934612
  have htrace : WordTrace (prefixWord ++ tailWord_3934612) baseStart_3934612 baseEnd_3934612 := by
    simpa [prefixWord, tailWord_3934612, baseEnd_3934612] using wordTrace_append hprefix tailTrace_3934612
  have hstable : (prefixWord ++ tailWord_3934612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3934612).length < 2 ^ (prefixWord ++ tailWord_3934612).sum := by decide
  have hdescent : baseEnd_3934612 < baseStart_3934612 := by decide
  rcases family_descends (prefixWord ++ tailWord_3934612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3934645 : List Nat := [1, 3, 3, 2, 3, 1, 1, 1, 2, 6]
def baseStart_3934645 : Nat := 118140960795 + 3934645 * 2 ^ 59
def prefixEnd_3934645 : Nat := 4983230072969 + 3 ^ 40 * 3934645 * 2
def baseEnd_3934645 : Nat := 673454696603287805680801

theorem tailTrace_3934645 : CollatzResearch.WordTrace tailWord_3934645 prefixEnd_3934645 673454696603287805680801 := by
  unfold tailWord_3934645
  simp only [CollatzResearch.WordTrace]
  refine ⟨143508292830460623711741389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95672195220307082474494259 143508292830460623711741389)
  ·
    refine ⟨53815609811422733891903021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143508292830460623711741389 53815609811422733891903021)
    ·
      refine ⟨20180853679283525209463633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53815609811422733891903021 20180853679283525209463633)
      ·
        refine ⟨15135640259462643907097725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20180853679283525209463633 15135640259462643907097725)
        ·
          refine ⟨5675865097298491465161647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15135640259462643907097725 5675865097298491465161647)
          ·
            refine ⟨8513797645947737197742471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5675865097298491465161647 8513797645947737197742471)
            ·
              refine ⟨12770696468921605796613707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8513797645947737197742471 12770696468921605796613707)
              ·
                refine ⟨19156044703382408694920561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12770696468921605796613707 19156044703382408694920561)
                ·
                  refine ⟨14367033527536806521190421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19156044703382408694920561 14367033527536806521190421)
                  ·
                    refine ⟨673454696603287805680801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14367033527536806521190421 673454696603287805680801)
                    ·
                      rfl

theorem cell23_3934645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 1, 1, 2, 6].length) (baseStart_3934645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3934645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3934645 prefixEnd_3934645 := by exact prefixLift 3934645
  have htrace : WordTrace (prefixWord ++ tailWord_3934645) baseStart_3934645 baseEnd_3934645 := by
    simpa [prefixWord, tailWord_3934645, baseEnd_3934645] using wordTrace_append hprefix tailTrace_3934645
  have hstable : (prefixWord ++ tailWord_3934645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3934645).length < 2 ^ (prefixWord ++ tailWord_3934645).sum := by decide
  have hdescent : baseEnd_3934645 < baseStart_3934645 := by decide
  rcases family_descends (prefixWord ++ tailWord_3934645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3934651 : List Nat := [1, 1, 1, 1, 1, 2, 2, 1, 3, 1, 9]
def baseStart_3934651 : Nat := 118140960795 + 3934651 * 2 ^ 59
def prefixEnd_3934651 : Nat := 4983230072969 + 3 ^ 40 * 3934651 * 2
def baseEnd_3934651 : Nat := 2020367170693790393567375

theorem tailTrace_3934651 : CollatzResearch.WordTrace tailWord_3934651 prefixEnd_3934651 2020367170693790393567375 := by
  unfold tailWord_3934651
  simp only [CollatzResearch.WordTrace]
  refine ⟨143508511668438886736459807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95672341112292591157639871 143508511668438886736459807)
  ·
    refine ⟨215262767502658330104689711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143508511668438886736459807 215262767502658330104689711)
    ·
      refine ⟨322894151253987495157034567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215262767502658330104689711 322894151253987495157034567)
      ·
        refine ⟨484341226880981242735551851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 322894151253987495157034567 484341226880981242735551851)
        ·
          refine ⟨726511840321471864103327777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 484341226880981242735551851 726511840321471864103327777)
          ·
            refine ⟨544883880241103898077495833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 726511840321471864103327777 544883880241103898077495833)
            ·
              refine ⟨408662910180827923558121875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 544883880241103898077495833 408662910180827923558121875)
              ·
                refine ⟨612994365271241885337182813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 408662910180827923558121875 612994365271241885337182813)
                ·
                  refine ⟨229872886976715707001443555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 612994365271241885337182813 229872886976715707001443555)
                  ·
                    refine ⟨344809330465073560502165333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 229872886976715707001443555 344809330465073560502165333)
                    ·
                      refine ⟨2020367170693790393567375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 344809330465073560502165333 2020367170693790393567375)
                      ·
                        rfl

theorem cell23_3934651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 3, 1, 9].length) (baseStart_3934651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3934651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3934651 prefixEnd_3934651 := by exact prefixLift 3934651
  have htrace : WordTrace (prefixWord ++ tailWord_3934651) baseStart_3934651 baseEnd_3934651 := by
    simpa [prefixWord, tailWord_3934651, baseEnd_3934651] using wordTrace_append hprefix tailTrace_3934651
  have hstable : (prefixWord ++ tailWord_3934651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3934651).length < 2 ^ (prefixWord ++ tailWord_3934651).sum := by decide
  have hdescent : baseEnd_3934651 < baseStart_3934651 := by decide
  rcases family_descends (prefixWord ++ tailWord_3934651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3934652 : List Nat := [2, 2, 2, 4, 1, 1, 1, 3, 1, 4, 2]
def baseStart_3934652 : Nat := 118140960795 + 3934652 * 2 ^ 59
def prefixEnd_3934652 : Nat := 4983230072969 + 3 ^ 40 * 3934652 * 2
def baseEnd_3934652 : Nat := 2020367684174444889654871

theorem tailTrace_3934652 : CollatzResearch.WordTrace tailWord_3934652 prefixEnd_3934652 2020367684174444889654871 := by
  unfold tailWord_3934652
  simp only [CollatzResearch.WordTrace]
  refine ⟨71754274070717631953623105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95672365427623509271497473 71754274070717631953623105)
  ·
    refine ⟨53815705553038223965217329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71754274070717631953623105 53815705553038223965217329)
    ·
      refine ⟨40361779164778667973912997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53815705553038223965217329 40361779164778667973912997)
      ·
        refine ⟨7567833593396000245108687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40361779164778667973912997 7567833593396000245108687)
        ·
          refine ⟨11351750390094000367663031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7567833593396000245108687 11351750390094000367663031)
          ·
            refine ⟨17027625585141000551494547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11351750390094000367663031 17027625585141000551494547)
            ·
              refine ⟨25541438377711500827241821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17027625585141000551494547 25541438377711500827241821)
              ·
                refine ⟨9578039391641812810215683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25541438377711500827241821 9578039391641812810215683)
                ·
                  refine ⟨14367059087462719215323525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9578039391641812810215683 14367059087462719215323525)
                  ·
                    refine ⟨2693823578899259852873161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14367059087462719215323525 2693823578899259852873161)
                    ·
                      refine ⟨2020367684174444889654871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2693823578899259852873161 2020367684174444889654871)
                      ·
                        rfl

theorem cell23_3934652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 3, 1, 4, 2].length) (baseStart_3934652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3934652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3934652 prefixEnd_3934652 := by exact prefixLift 3934652
  have htrace : WordTrace (prefixWord ++ tailWord_3934652) baseStart_3934652 baseEnd_3934652 := by
    simpa [prefixWord, tailWord_3934652, baseEnd_3934652] using wordTrace_append hprefix tailTrace_3934652
  have hstable : (prefixWord ++ tailWord_3934652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3934652).length < 2 ^ (prefixWord ++ tailWord_3934652).sum := by decide
  have hdescent : baseEnd_3934652 < baseStart_3934652 := by decide
  rcases family_descends (prefixWord ++ tailWord_3934652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3934685 : List Nat := [1, 4, 3, 1, 1, 1, 1, 1, 4, 3, 3]
def baseStart_3934685 : Nat := 118140960795 + 3934685 * 2 ^ 59
def prefixEnd_3934685 : Nat := 4983230072969 + 3 ^ 40 * 3934685 * 2
def baseEnd_3934685 : Nat := 2020384629036043260542219

theorem tailTrace_3934685 : CollatzResearch.WordTrace tailWord_3934685 prefixEnd_3934685 2020384629036043260542219 := by
  unfold tailWord_3934685
  simp only [CollatzResearch.WordTrace]
  refine ⟨143509751750315710543197509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95673167833543807028798339 143509751750315710543197509)
  ·
    refine ⟨26908078453184195726849533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 143509751750315710543197509 26908078453184195726849533)
    ·
      refine ⟨10090529419944073397568575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26908078453184195726849533 10090529419944073397568575)
      ·
        refine ⟨15135794129916110096352863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10090529419944073397568575 15135794129916110096352863)
        ·
          refine ⟨22703691194874165144529295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15135794129916110096352863 22703691194874165144529295)
          ·
            refine ⟨34055536792311247716793943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22703691194874165144529295 34055536792311247716793943)
            ·
              refine ⟨51083305188466871575190915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34055536792311247716793943 51083305188466871575190915)
              ·
                refine ⟨76624957782700307362786373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51083305188466871575190915 76624957782700307362786373)
                ·
                  refine ⟨14367179584256307630522445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 76624957782700307362786373 14367179584256307630522445)
                  ·
                    refine ⟨5387692344096115361445917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14367179584256307630522445 5387692344096115361445917)
                    ·
                      refine ⟨2020384629036043260542219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5387692344096115361445917 2020384629036043260542219)
                      ·
                        rfl

theorem cell23_3934685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 1, 4, 3, 3].length) (baseStart_3934685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3934685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3934685 prefixEnd_3934685 := by exact prefixLift 3934685
  have htrace : WordTrace (prefixWord ++ tailWord_3934685) baseStart_3934685 baseEnd_3934685 := by
    simpa [prefixWord, tailWord_3934685, baseEnd_3934685] using wordTrace_append hprefix tailTrace_3934685
  have hstable : (prefixWord ++ tailWord_3934685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3934685).length < 2 ^ (prefixWord ++ tailWord_3934685).sum := by decide
  have hdescent : baseEnd_3934685 < baseStart_3934685 := by decide
  rcases family_descends (prefixWord ++ tailWord_3934685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3934688 : List Nat := [2, 1, 1, 3, 1, 1, 4, 1, 4, 5]
def baseStart_3934688 : Nat := 118140960795 + 3934688 * 2 ^ 59
def prefixEnd_3934688 : Nat := 4983230072969 + 3 ^ 40 * 3934688 * 2
def baseEnd_3934688 : Nat := 673462056492668916268235

theorem tailTrace_3934688 : CollatzResearch.WordTrace tailWord_3934688 prefixEnd_3934688 673462056492668916268235 := by
  unfold tailWord_3934688
  simp only [CollatzResearch.WordTrace]
  refine ⟨71754930584652421027778359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95673240779536561370371145 71754930584652421027778359)
  ·
    refine ⟨107632395876978631541667539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71754930584652421027778359 107632395876978631541667539)
    ·
      refine ⟨161448593815467947312501309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107632395876978631541667539 161448593815467947312501309)
      ·
        refine ⟨60543222680800480242187991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 161448593815467947312501309 60543222680800480242187991)
        ·
          refine ⟨90814834021200720363281987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60543222680800480242187991 90814834021200720363281987)
          ·
            refine ⟨136222251031801080544922981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90814834021200720363281987 136222251031801080544922981)
            ·
              refine ⟨25541672068462702602173059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 136222251031801080544922981 25541672068462702602173059)
              ·
                refine ⟨38312508102694053903259589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25541672068462702602173059 38312508102694053903259589)
                ·
                  refine ⟨7183595269255135106861173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38312508102694053903259589 7183595269255135106861173)
                  ·
                    refine ⟨673462056492668916268235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7183595269255135106861173 673462056492668916268235)
                    ·
                      rfl

theorem cell23_3934688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 1, 4, 5].length) (baseStart_3934688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3934688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3934688 prefixEnd_3934688 := by exact prefixLift 3934688
  have htrace : WordTrace (prefixWord ++ tailWord_3934688) baseStart_3934688 baseEnd_3934688 := by
    simpa [prefixWord, tailWord_3934688, baseEnd_3934688] using wordTrace_append hprefix tailTrace_3934688
  have hstable : (prefixWord ++ tailWord_3934688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3934688).length < 2 ^ (prefixWord ++ tailWord_3934688).sum := by decide
  have hdescent : baseEnd_3934688 < baseStart_3934688 := by decide
  rcases family_descends (prefixWord ++ tailWord_3934688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3934725 : List Nat := [1, 3, 1, 1, 2, 2, 2, 2, 1, 6, 2]
def baseStart_3934725 : Nat := 118140960795 + 3934725 * 2 ^ 59
def prefixEnd_3934725 : Nat := 4983230072969 + 3 ^ 40 * 3934725 * 2
def baseEnd_3934725 : Nat := 2020405168262223104042035

theorem tailTrace_3934725 : CollatzResearch.WordTrace tailWord_3934725 prefixEnd_3934725 2020405168262223104042035 := by
  unfold tailWord_3934725
  simp only [CollatzResearch.WordTrace]
  refine ⟨143511210670170797374653629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95674140446780531583102419 143511210670170797374653629)
  ·
    refine ⟨53816704001314049015495111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143511210670170797374653629 53816704001314049015495111)
    ·
      refine ⟨80725056001971073523242667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53816704001314049015495111 80725056001971073523242667)
      ·
        refine ⟨121087584002956610284864001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80725056001971073523242667 121087584002956610284864001)
        ·
          refine ⟨90815688002217457713648001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121087584002956610284864001 90815688002217457713648001)
          ·
            refine ⟨68111766001663093285236001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90815688002217457713648001 68111766001663093285236001)
            ·
              refine ⟨51083824501247319963927001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68111766001663093285236001 51083824501247319963927001)
              ·
                refine ⟨38312868375935489972945251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51083824501247319963927001 38312868375935489972945251)
                ·
                  refine ⟨57469302563903234959417877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38312868375935489972945251 57469302563903234959417877)
                  ·
                    refine ⟨2693873557682964138722713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 57469302563903234959417877 2693873557682964138722713)
                    ·
                      refine ⟨2020405168262223104042035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2693873557682964138722713 2020405168262223104042035)
                      ·
                        rfl

theorem cell23_3934725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 2, 1, 6, 2].length) (baseStart_3934725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3934725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3934725 prefixEnd_3934725 := by exact prefixLift 3934725
  have htrace : WordTrace (prefixWord ++ tailWord_3934725) baseStart_3934725 baseEnd_3934725 := by
    simpa [prefixWord, tailWord_3934725, baseEnd_3934725] using wordTrace_append hprefix tailTrace_3934725
  have hstable : (prefixWord ++ tailWord_3934725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3934725).length < 2 ^ (prefixWord ++ tailWord_3934725).sum := by decide
  have hdescent : baseEnd_3934725 < baseStart_3934725 := by decide
  rcases family_descends (prefixWord ++ tailWord_3934725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3934728 : List Nat := [2, 1, 3, 2, 1, 1, 1, 2, 2, 3, 5]
def baseStart_3934728 : Nat := 118140960795 + 3934728 * 2 ^ 59
def prefixEnd_3934728 : Nat := 4983230072969 + 3 ^ 40 * 3934728 * 2
def baseEnd_3934728 : Nat := 2020406708704186592304521

theorem tailTrace_3934728 : CollatzResearch.WordTrace tailWord_3934728 prefixEnd_3934728 2020406708704186592304521 := by
  unfold tailWord_3934728
  simp only [CollatzResearch.WordTrace]
  refine ⟨71755660044579964443506419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95674213392773285924675225 71755660044579964443506419)
  ·
    refine ⟨107633490066869946665259629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71755660044579964443506419 107633490066869946665259629)
    ·
      refine ⟨40362558775076229999472361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107633490066869946665259629 40362558775076229999472361)
      ·
        refine ⟨30271919081307172499604271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40362558775076229999472361 30271919081307172499604271)
        ·
          refine ⟨45407878621960758749406407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30271919081307172499604271 45407878621960758749406407)
          ·
            refine ⟨68111817932941138124109611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45407878621960758749406407 68111817932941138124109611)
            ·
              refine ⟨102167726899411707186164417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68111817932941138124109611 102167726899411707186164417)
              ·
                refine ⟨76625795174558780389623313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102167726899411707186164417 76625795174558780389623313)
                ·
                  refine ⟨57469346380919085292217485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76625795174558780389623313 57469346380919085292217485)
                  ·
                    refine ⟨21551004892844656984581557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 57469346380919085292217485 21551004892844656984581557)
                    ·
                      refine ⟨2020406708704186592304521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21551004892844656984581557 2020406708704186592304521)
                      ·
                        rfl

theorem cell23_3934728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 2, 2, 3, 5].length) (baseStart_3934728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3934728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3934728 prefixEnd_3934728 := by exact prefixLift 3934728
  have htrace : WordTrace (prefixWord ++ tailWord_3934728) baseStart_3934728 baseEnd_3934728 := by
    simpa [prefixWord, tailWord_3934728, baseEnd_3934728] using wordTrace_append hprefix tailTrace_3934728
  have hstable : (prefixWord ++ tailWord_3934728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3934728).length < 2 ^ (prefixWord ++ tailWord_3934728).sum := by decide
  have hdescent : baseEnd_3934728 < baseStart_3934728 := by decide
  rcases family_descends (prefixWord ++ tailWord_3934728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3934745 : List Nat := [1, 2, 1, 2, 1, 1, 2, 6, 2, 2, 3]
def baseStart_3934745 : Nat := 118140960795 + 3934745 * 2 ^ 59
def prefixEnd_3934745 : Nat := 4983230072969 + 3 ^ 40 * 3934745 * 2
def baseEnd_3934745 : Nat := 2020415437875313025791943

theorem tailTrace_3934745 : CollatzResearch.WordTrace tailWord_3934745 prefixEnd_3934745 2020415437875313025791943 := by
  unfold tailWord_3934745
  simp only [CollatzResearch.WordTrace]
  refine ⟨143511940130098340790381689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95674626753398893860254459 143511940130098340790381689)
  ·
    refine ⟨107633955097573755592786267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143511940130098340790381689 107633955097573755592786267)
    ·
      refine ⟨161450932646360633389179401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107633955097573755592786267 161450932646360633389179401)
      ·
        refine ⟨121088199484770475041884551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161450932646360633389179401 121088199484770475041884551)
        ·
          refine ⟨181632299227155712562826827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121088199484770475041884551 181632299227155712562826827)
          ·
            refine ⟨272448448840733568844240241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181632299227155712562826827 272448448840733568844240241)
            ·
              refine ⟨204336336630550176633180181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 272448448840733568844240241 204336336630550176633180181)
              ·
                refine ⟨9578265779557039529680321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 204336336630550176633180181 9578265779557039529680321)
                ·
                  refine ⟨7183699334667779647260241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9578265779557039529680321 7183699334667779647260241)
                  ·
                    refine ⟨5387774501000834735445181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7183699334667779647260241 5387774501000834735445181)
                    ·
                      refine ⟨2020415437875313025791943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5387774501000834735445181 2020415437875313025791943)
                      ·
                        rfl

theorem cell23_3934745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 6, 2, 2, 3].length) (baseStart_3934745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3934745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3934745 prefixEnd_3934745 := by exact prefixLift 3934745
  have htrace : WordTrace (prefixWord ++ tailWord_3934745) baseStart_3934745 baseEnd_3934745 := by
    simpa [prefixWord, tailWord_3934745, baseEnd_3934745] using wordTrace_append hprefix tailTrace_3934745
  have hstable : (prefixWord ++ tailWord_3934745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3934745).length < 2 ^ (prefixWord ++ tailWord_3934745).sum := by decide
  have hdescent : baseEnd_3934745 < baseStart_3934745 := by decide
  rcases family_descends (prefixWord ++ tailWord_3934745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3934768 : List Nat := [2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 6]
def baseStart_3934768 : Nat := 118140960795 + 3934768 * 2 ^ 59
def prefixEnd_3934768 : Nat := 4983230072969 + 3 ^ 40 * 3934768 * 2
def baseEnd_3934768 : Nat := 2020427247930366435804337

theorem tailTrace_3934768 : CollatzResearch.WordTrace tailWord_3934768 prefixEnd_3934768 2020427247930366435804337 := by
  unfold tailWord_3934768
  simp only [CollatzResearch.WordTrace]
  refine ⟨71756389504507507859234479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95675186006010010478979305 71756389504507507859234479)
  ·
    refine ⟨107634584256761261788851719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71756389504507507859234479 107634584256761261788851719)
    ·
      refine ⟨161451876385141892683277579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107634584256761261788851719 161451876385141892683277579)
      ·
        refine ⟨242177814577712839024916369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161451876385141892683277579 242177814577712839024916369)
        ·
          refine ⟨181633360933284629268687277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 242177814577712839024916369 181633360933284629268687277)
          ·
            refine ⟨68112510349981735975757729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 181633360933284629268687277 68112510349981735975757729)
            ·
              refine ⟨51084382762486301981818297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68112510349981735975757729 51084382762486301981818297)
              ·
                refine ⟨38313287071864726486363723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51084382762486301981818297 38313287071864726486363723)
                ·
                  refine ⟨57469930607797089729545585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38313287071864726486363723 57469930607797089729545585)
                  ·
                    refine ⟨43102447955847817297159189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 57469930607797089729545585 43102447955847817297159189)
                    ·
                      refine ⟨2020427247930366435804337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 43102447955847817297159189 2020427247930366435804337)
                      ·
                        rfl

theorem cell23_3934768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 6].length) (baseStart_3934768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3934768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3934768 prefixEnd_3934768 := by exact prefixLift 3934768
  have htrace : WordTrace (prefixWord ++ tailWord_3934768) baseStart_3934768 baseEnd_3934768 := by
    simpa [prefixWord, tailWord_3934768, baseEnd_3934768] using wordTrace_append hprefix tailTrace_3934768
  have hstable : (prefixWord ++ tailWord_3934768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3934768).length < 2 ^ (prefixWord ++ tailWord_3934768).sum := by decide
  have hdescent : baseEnd_3934768 < baseStart_3934768 := by decide
  rcases family_descends (prefixWord ++ tailWord_3934768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3934795 : List Nat := [1, 1, 1, 1, 3, 1, 4, 5, 1, 5]
def baseStart_3934795 : Nat := 118140960795 + 3934795 * 2 ^ 59
def prefixEnd_3934795 : Nat := 4983230072969 + 3 ^ 40 * 3934795 * 2
def baseEnd_3934795 : Nat := 673480370636012610055571

theorem tailTrace_3934795 : CollatzResearch.WordTrace tailWord_3934795 prefixEnd_3934795 673480370636012610055571 := by
  unfold tailWord_3934795
  simp only [CollatzResearch.WordTrace]
  refine ⟨143513763779917199329701839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95675842519944799553134559 143513763779917199329701839)
  ·
    refine ⟨215270645669875798994552759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143513763779917199329701839 215270645669875798994552759)
    ·
      refine ⟨322905968504813698491829139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215270645669875798994552759 322905968504813698491829139)
      ·
        refine ⟨484358952757220547737743709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 322905968504813698491829139 484358952757220547737743709)
        ·
          refine ⟨181634607283957705401653891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 484358952757220547737743709 181634607283957705401653891)
          ·
            refine ⟨272451910925936558102480837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181634607283957705401653891 272451910925936558102480837)
            ·
              refine ⟨51084733298613104644215157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 272451910925936558102480837 51084733298613104644215157)
              ·
                refine ⟨4789193746744978560395171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51084733298613104644215157 4789193746744978560395171)
                ·
                  refine ⟨7183790620117467840592757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4789193746744978560395171 7183790620117467840592757)
                  ·
                    refine ⟨673480370636012610055571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7183790620117467840592757 673480370636012610055571)
                    ·
                      rfl

theorem cell23_3934795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 5, 1, 5].length) (baseStart_3934795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3934795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3934795 prefixEnd_3934795 := by exact prefixLift 3934795
  have htrace : WordTrace (prefixWord ++ tailWord_3934795) baseStart_3934795 baseEnd_3934795 := by
    simpa [prefixWord, tailWord_3934795, baseEnd_3934795] using wordTrace_append hprefix tailTrace_3934795
  have hstable : (prefixWord ++ tailWord_3934795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3934795).length < 2 ^ (prefixWord ++ tailWord_3934795).sum := by decide
  have hdescent : baseEnd_3934795 < baseStart_3934795 := by decide
  rcases family_descends (prefixWord ++ tailWord_3934795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3934825 : List Nat := [1, 2, 1, 1, 1, 4, 1, 2, 6, 4]
def baseStart_3934825 : Nat := 118140960795 + 3934825 * 2 ^ 59
def prefixEnd_3934825 : Nat := 4983230072969 + 3 ^ 40 * 3934825 * 2
def baseEnd_3934825 : Nat := 673485505442557570930525

theorem tailTrace_3934825 : CollatzResearch.WordTrace tailWord_3934825 prefixEnd_3934825 673485505442557570930525 := by
  unfold tailWord_3934825
  simp only [CollatzResearch.WordTrace]
  refine ⟨143514857969808514453293929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95676571979872342968862619 143514857969808514453293929)
  ·
    refine ⟨107636143477356385839970447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143514857969808514453293929 107636143477356385839970447)
    ·
      refine ⟨161454215216034578759955671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107636143477356385839970447 161454215216034578759955671)
      ·
        refine ⟨242181322824051868139933507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161454215216034578759955671 242181322824051868139933507)
        ·
          refine ⟨363271984236077802209900261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242181322824051868139933507 363271984236077802209900261)
          ·
            refine ⟨68113497044264587914356299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 363271984236077802209900261 68113497044264587914356299)
            ·
              refine ⟨102170245566396881871534449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68113497044264587914356299 102170245566396881871534449)
              ·
                refine ⟨76627684174797661403650837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102170245566396881871534449 76627684174797661403650837)
                ·
                  refine ⟨3591922695693640378296133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 76627684174797661403650837 3591922695693640378296133)
                  ·
                    refine ⟨673485505442557570930525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3591922695693640378296133 673485505442557570930525)
                    ·
                      rfl

theorem cell23_3934825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 2, 6, 4].length) (baseStart_3934825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3934825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3934825 prefixEnd_3934825 := by exact prefixLift 3934825
  have htrace : WordTrace (prefixWord ++ tailWord_3934825) baseStart_3934825 baseEnd_3934825 := by
    simpa [prefixWord, tailWord_3934825, baseEnd_3934825] using wordTrace_append hprefix tailTrace_3934825
  have hstable : (prefixWord ++ tailWord_3934825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3934825).length < 2 ^ (prefixWord ++ tailWord_3934825).sum := by decide
  have hdescent : baseEnd_3934825 < baseStart_3934825 := by decide
  rcases family_descends (prefixWord ++ tailWord_3934825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3934849 : List Nat := [1, 2, 4, 2, 1, 1, 1, 2, 5, 2, 2]
def baseStart_3934849 : Nat := 118140960795 + 3934849 * 2 ^ 59
def prefixEnd_3934849 : Nat := 4983230072969 + 3 ^ 40 * 3934849 * 2
def baseEnd_3934849 : Nat := 2020468839863380618891465

theorem tailTrace_3934849 : CollatzResearch.WordTrace tailWord_3934849 prefixEnd_3934849 2020468839863380618891465 := by
  unfold tailWord_3934849
  simp only [CollatzResearch.WordTrace]
  refine ⟨143515733321721566552167601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95677155547814377701445067 143515733321721566552167601)
  ·
    refine ⟨107636799991291174914125701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143515733321721566552167601 107636799991291174914125701)
    ·
      refine ⟨20181899998367095296398569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 107636799991291174914125701 20181899998367095296398569)
      ·
        refine ⟨15136424998775321472298927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20181899998367095296398569 15136424998775321472298927)
        ·
          refine ⟨22704637498162982208448391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15136424998775321472298927 22704637498162982208448391)
          ·
            refine ⟨34056956247244473312672587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22704637498162982208448391 34056956247244473312672587)
            ·
              refine ⟨51085434370866709969008881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34056956247244473312672587 51085434370866709969008881)
              ·
                refine ⟨38314075778150032476756661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51085434370866709969008881 38314075778150032476756661)
                ·
                  refine ⟨3591944604201565544695937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38314075778150032476756661 3591944604201565544695937)
                  ·
                    refine ⟨2693958453151174158521953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3591944604201565544695937 2693958453151174158521953)
                    ·
                      refine ⟨2020468839863380618891465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2693958453151174158521953 2020468839863380618891465)
                      ·
                        rfl

theorem cell23_3934849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 2, 5, 2, 2].length) (baseStart_3934849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3934849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3934849 prefixEnd_3934849 := by exact prefixLift 3934849
  have htrace : WordTrace (prefixWord ++ tailWord_3934849) baseStart_3934849 baseEnd_3934849 := by
    simpa [prefixWord, tailWord_3934849, baseEnd_3934849] using wordTrace_append hprefix tailTrace_3934849
  have hstable : (prefixWord ++ tailWord_3934849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3934849).length < 2 ^ (prefixWord ++ tailWord_3934849).sum := by decide
  have hdescent : baseEnd_3934849 < baseStart_3934849 := by decide
  rcases family_descends (prefixWord ++ tailWord_3934849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3934850 : List Nat := [3, 4, 3, 1, 2, 1, 1, 2, 6]
def baseStart_3934850 : Nat := 118140960795 + 3934850 * 2 ^ 59
def prefixEnd_3934850 : Nat := 4983230072969 + 3 ^ 40 * 3934850 * 2
def baseEnd_3934850 : Nat := 224496594816003901664329

theorem tailTrace_3934850 : CollatzResearch.WordTrace tailWord_3934850 prefixEnd_3934850 224496594816003901664329 := by
  unfold tailWord_3934850
  simp only [CollatzResearch.WordTrace]
  refine ⟨35878942448679485930738501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95677179863145295815302669 35878942448679485930738501)
  ·
    refine ⟨6727301709127403612013469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35878942448679485930738501 6727301709127403612013469)
    ·
      refine ⟨2522738140922776354505051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6727301709127403612013469 2522738140922776354505051)
      ·
        refine ⟨3784107211384164531757577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2522738140922776354505051 3784107211384164531757577)
        ·
          refine ⟨2838080408538123398818183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3784107211384164531757577 2838080408538123398818183)
          ·
            refine ⟨4257120612807185098227275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2838080408538123398818183 4257120612807185098227275)
            ·
              refine ⟨6385680919210777647340913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4257120612807185098227275 6385680919210777647340913)
              ·
                refine ⟨4789260689408083235505685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6385680919210777647340913 4789260689408083235505685)
                ·
                  refine ⟨224496594816003901664329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4789260689408083235505685 224496594816003901664329)
                  ·
                    rfl

theorem cell23_3934850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 1, 2, 6].length) (baseStart_3934850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3934850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3934850 prefixEnd_3934850 := by exact prefixLift 3934850
  have htrace : WordTrace (prefixWord ++ tailWord_3934850) baseStart_3934850 baseEnd_3934850 := by
    simpa [prefixWord, tailWord_3934850, baseEnd_3934850] using wordTrace_append hprefix tailTrace_3934850
  have hstable : (prefixWord ++ tailWord_3934850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3934850).length < 2 ^ (prefixWord ++ tailWord_3934850).sum := by decide
  have hdescent : baseEnd_3934850 < baseStart_3934850 := by decide
  rcases family_descends (prefixWord ++ tailWord_3934850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3934866 : List Nat := [3, 2, 3, 1, 2, 1, 1, 3, 3, 2, 2]
def baseStart_3934866 : Nat := 118140960795 + 3934866 * 2 ^ 59
def prefixEnd_3934866 : Nat := 4983230072969 + 3 ^ 40 * 3934866 * 2
def baseEnd_3934866 : Nat := 2020477569034507052378887

theorem tailTrace_3934866 : CollatzResearch.WordTrace tailWord_3934866 prefixEnd_3934866 2020477569034507052378887 := by
  unfold tailWord_3934866
  simp only [CollatzResearch.WordTrace]
  refine ⟨35879088340664994613884113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95677568908439985637024301 35879088340664994613884113)
  ·
    refine ⟨26909316255498745960413085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35879088340664994613884113 26909316255498745960413085)
    ·
      refine ⟨10090993595812029735154907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26909316255498745960413085 10090993595812029735154907)
      ·
        refine ⟨15136490393718044602732361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10090993595812029735154907 15136490393718044602732361)
        ·
          refine ⟨11352367795288533452049271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15136490393718044602732361 11352367795288533452049271)
          ·
            refine ⟨17028551692932800178073907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11352367795288533452049271 17028551692932800178073907)
            ·
              refine ⟨25542827539399200267110861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17028551692932800178073907 25542827539399200267110861)
              ·
                refine ⟨9578560327274700100166573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25542827539399200267110861 9578560327274700100166573)
                ·
                  refine ⟨3591960122728012537562465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9578560327274700100166573 3591960122728012537562465)
                  ·
                    refine ⟨2693970092046009403171849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3591960122728012537562465 2693970092046009403171849)
                    ·
                      refine ⟨2020477569034507052378887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2693970092046009403171849 2020477569034507052378887)
                      ·
                        rfl

theorem cell23_3934866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 3, 3, 2, 2].length) (baseStart_3934866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3934866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3934866 prefixEnd_3934866 := by exact prefixLift 3934866
  have htrace : WordTrace (prefixWord ++ tailWord_3934866) baseStart_3934866 baseEnd_3934866 := by
    simpa [prefixWord, tailWord_3934866, baseEnd_3934866] using wordTrace_append hprefix tailTrace_3934866
  have hstable : (prefixWord ++ tailWord_3934866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3934866).length < 2 ^ (prefixWord ++ tailWord_3934866).sum := by decide
  have hdescent : baseEnd_3934866 < baseStart_3934866 := by decide
  rcases family_descends (prefixWord ++ tailWord_3934866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3934876 : List Nat := [2, 2, 3, 2, 2, 2, 3, 1, 2, 4]
def baseStart_3934876 : Nat := 118140960795 + 3934876 * 2 ^ 59
def prefixEnd_3934876 : Nat := 4983230072969 + 3 ^ 40 * 3934876 * 2
def baseEnd_3934876 : Nat := 673494234613684004417947

theorem tailTrace_3934876 : CollatzResearch.WordTrace tailWord_3934876 prefixEnd_3934876 673494234613684004417947 := by
  unfold tailWord_3934876
  simp only [CollatzResearch.WordTrace]
  refine ⟨71758359046311875081700241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95677812061749166775600321 71758359046311875081700241)
  ·
    refine ⟨53818769284733906311275181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71758359046311875081700241 53818769284733906311275181)
    ·
      refine ⟨20182038481775214866728193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53818769284733906311275181 20182038481775214866728193)
      ·
        refine ⟨15136528861331411150046145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20182038481775214866728193 15136528861331411150046145)
        ·
          refine ⟨11352396645998558362534609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15136528861331411150046145 11352396645998558362534609)
          ·
            refine ⟨8514297484498918771900957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11352396645998558362534609 8514297484498918771900957)
            ·
              refine ⟨3192861556687094539462859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8514297484498918771900957 3192861556687094539462859)
              ·
                refine ⟨4789292335030641809194289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3192861556687094539462859 4789292335030641809194289)
                ·
                  refine ⟨3591969251272981356895717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4789292335030641809194289 3591969251272981356895717)
                  ·
                    refine ⟨673494234613684004417947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3591969251272981356895717 673494234613684004417947)
                    ·
                      rfl

theorem cell23_3934876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 3, 1, 2, 4].length) (baseStart_3934876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3934876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3934876 prefixEnd_3934876 := by exact prefixLift 3934876
  have htrace : WordTrace (prefixWord ++ tailWord_3934876) baseStart_3934876 baseEnd_3934876 := by
    simpa [prefixWord, tailWord_3934876, baseEnd_3934876] using wordTrace_append hprefix tailTrace_3934876
  have hstable : (prefixWord ++ tailWord_3934876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3934876).length < 2 ^ (prefixWord ++ tailWord_3934876).sum := by decide
  have hdescent : baseEnd_3934876 < baseStart_3934876 := by decide
  rcases family_descends (prefixWord ++ tailWord_3934876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3934895 : List Nat := [1, 1, 2, 1, 2, 5, 1, 1, 2, 2, 5]
def baseStart_3934895 : Nat := 118140960795 + 3934895 * 2 ^ 59
def prefixEnd_3934895 : Nat := 4983230072969 + 3 ^ 40 * 3934895 * 2
def baseEnd_3934895 : Nat := 2020492459973487438916253

theorem tailTrace_3934895 : CollatzResearch.WordTrace tailWord_3934895 prefixEnd_3934895 2020492459973487438916253 := by
  unfold tailWord_3934895
  simp only [CollatzResearch.WordTrace]
  refine ⟨143517411079554916408342139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95678274053036610938894759 143517411079554916408342139)
  ·
    refine ⟨215276116619332374612513209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143517411079554916408342139 215276116619332374612513209)
    ·
      refine ⟨161457087464499280959384907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215276116619332374612513209 161457087464499280959384907)
      ·
        refine ⟨242185631196748921439077361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161457087464499280959384907 242185631196748921439077361)
        ·
          refine ⟨181639223397561691079308021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 242185631196748921439077361 181639223397561691079308021)
          ·
            refine ⟨17028677193521408538685127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 181639223397561691079308021 17028677193521408538685127)
            ·
              refine ⟨25543015790282112808027691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17028677193521408538685127 25543015790282112808027691)
              ·
                refine ⟨38314523685423169212041537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25543015790282112808027691 38314523685423169212041537)
                ·
                  refine ⟨28735892764067376909031153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38314523685423169212041537 28735892764067376909031153)
                  ·
                    refine ⟨21551919573050532681773365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28735892764067376909031153 21551919573050532681773365)
                    ·
                      refine ⟨2020492459973487438916253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21551919573050532681773365 2020492459973487438916253)
                      ·
                        rfl

theorem cell23_3934895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 1, 2, 2, 5].length) (baseStart_3934895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3934895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3934895 prefixEnd_3934895 := by exact prefixLift 3934895
  have htrace : WordTrace (prefixWord ++ tailWord_3934895) baseStart_3934895 baseEnd_3934895 := by
    simpa [prefixWord, tailWord_3934895, baseEnd_3934895] using wordTrace_append hprefix tailTrace_3934895
  have hstable : (prefixWord ++ tailWord_3934895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3934895).length < 2 ^ (prefixWord ++ tailWord_3934895).sum := by decide
  have hdescent : baseEnd_3934895 < baseStart_3934895 := by decide
  rcases family_descends (prefixWord ++ tailWord_3934895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3934905 : List Nat := [1, 2, 1, 4, 1, 1, 1, 2, 1, 5, 4]
def baseStart_3934905 : Nat := 118140960795 + 3934905 * 2 ^ 59
def prefixEnd_3934905 : Nat := 4983230072969 + 3 ^ 40 * 3934905 * 2
def baseEnd_3934905 : Nat := 2020497594780032399791207

theorem tailTrace_3934905 : CollatzResearch.WordTrace tailWord_3934905 prefixEnd_3934905 2020497594780032399791207 := by
  unfold tailWord_3934905
  simp only [CollatzResearch.WordTrace]
  refine ⟨143517775809518688116206169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95678517206345792077470779 143517775809518688116206169)
  ·
    refine ⟨107638331857139016087154627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143517775809518688116206169 107638331857139016087154627)
    ·
      refine ⟨161457497785708524130731941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107638331857139016087154627 161457497785708524130731941)
      ·
        refine ⟨30273280834820348274512239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 161457497785708524130731941 30273280834820348274512239)
        ·
          refine ⟨45409921252230522411768359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30273280834820348274512239 45409921252230522411768359)
          ·
            refine ⟨68114881878345783617652539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45409921252230522411768359 68114881878345783617652539)
            ·
              refine ⟨102172322817518675426478809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68114881878345783617652539 102172322817518675426478809)
              ·
                refine ⟨76629242113139006569859107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102172322817518675426478809 76629242113139006569859107)
                ·
                  refine ⟨114943863169708509854788661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76629242113139006569859107 114943863169708509854788661)
                  ·
                    refine ⟨10775987172160172798886437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 114943863169708509854788661 10775987172160172798886437)
                    ·
                      refine ⟨2020497594780032399791207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10775987172160172798886437 2020497594780032399791207)
                      ·
                        rfl

theorem cell23_3934905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 2, 1, 5, 4].length) (baseStart_3934905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3934905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3934905 prefixEnd_3934905 := by exact prefixLift 3934905
  have htrace : WordTrace (prefixWord ++ tailWord_3934905) baseStart_3934905 baseEnd_3934905 := by
    simpa [prefixWord, tailWord_3934905, baseEnd_3934905] using wordTrace_append hprefix tailTrace_3934905
  have hstable : (prefixWord ++ tailWord_3934905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3934905).length < 2 ^ (prefixWord ++ tailWord_3934905).sum := by decide
  have hdescent : baseEnd_3934905 < baseStart_3934905 := by decide
  rcases family_descends (prefixWord ++ tailWord_3934905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3934933 : List Nat := [1, 3, 2, 5, 1, 1, 1, 3, 2, 1, 3]
def baseStart_3934933 : Nat := 118140960795 + 3934933 * 2 ^ 59
def prefixEnd_3934933 : Nat := 4983230072969 + 3 ^ 40 * 3934933 * 2
def baseEnd_3934933 : Nat := 2020511972238358290241079

theorem tailTrace_3934933 : CollatzResearch.WordTrace tailWord_3934933 prefixEnd_3934933 2020511972238358290241079 := by
  unfold tailWord_3934933
  simp only [CollatzResearch.WordTrace]
  refine ⟨143518797053417248898225453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95679198035611499265483635 143518797053417248898225453)
  ·
    refine ⟨53819548895031468336834545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143518797053417248898225453 53819548895031468336834545)
    ·
      refine ⟨40364661671273601252625909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53819548895031468336834545 40364661671273601252625909)
      ·
        refine ⟨3784187031681900117433679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 40364661671273601252625909 3784187031681900117433679)
        ·
          refine ⟨5676280547522850176150519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3784187031681900117433679 5676280547522850176150519)
          ·
            refine ⟨8514420821284275264225779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5676280547522850176150519 8514420821284275264225779)
            ·
              refine ⟨12771631231926412896338669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8514420821284275264225779 12771631231926412896338669)
              ·
                refine ⟨4789361711972404836127001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12771631231926412896338669 4789361711972404836127001)
                ·
                  refine ⟨3592021283979303627095251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4789361711972404836127001 3592021283979303627095251)
                  ·
                    refine ⟨5388031925968955440642877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3592021283979303627095251 5388031925968955440642877)
                    ·
                      refine ⟨2020511972238358290241079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5388031925968955440642877 2020511972238358290241079)
                      ·
                        rfl

theorem cell23_3934933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 1, 3, 2, 1, 3].length) (baseStart_3934933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3934933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3934933 prefixEnd_3934933 := by exact prefixLift 3934933
  have htrace : WordTrace (prefixWord ++ tailWord_3934933) baseStart_3934933 baseEnd_3934933 := by
    simpa [prefixWord, tailWord_3934933, baseEnd_3934933] using wordTrace_append hprefix tailTrace_3934933
  have hstable : (prefixWord ++ tailWord_3934933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3934933).length < 2 ^ (prefixWord ++ tailWord_3934933).sum := by decide
  have hdescent : baseEnd_3934933 < baseStart_3934933 := by decide
  rcases family_descends (prefixWord ++ tailWord_3934933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3934975 : List Nat := [1, 1, 2, 2, 1, 3, 1, 2, 3, 7]
def baseStart_3934975 : Nat := 118140960795 + 3934975 * 2 ^ 59
def prefixEnd_3934975 : Nat := 4983230072969 + 3 ^ 40 * 3934975 * 2
def baseEnd_3934975 : Nat := 673511179475282375305295

theorem tailTrace_3934975 : CollatzResearch.WordTrace tailWord_3934975 prefixEnd_3934975 673511179475282375305295 := by
  unfold tailWord_3934975
  simp only [CollatzResearch.WordTrace]
  refine ⟨143520328919265090071254379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95680219279510060047502919 143520328919265090071254379)
  ·
    refine ⟨215280493378897635106881569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143520328919265090071254379 215280493378897635106881569)
    ·
      refine ⟨161460370034173226330161177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215280493378897635106881569 161460370034173226330161177)
      ·
        refine ⟨121095277525629919747620883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161460370034173226330161177 121095277525629919747620883)
        ·
          refine ⟨181642916288444879621431325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121095277525629919747620883 181642916288444879621431325)
          ·
            refine ⟨68116093608166829858036747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 181642916288444879621431325 68116093608166829858036747)
            ·
              refine ⟨102174140412250244787055121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68116093608166829858036747 102174140412250244787055121)
              ·
                refine ⟨76630605309187683590291341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102174140412250244787055121 76630605309187683590291341)
                ·
                  refine ⟨28736476990945381346359253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76630605309187683590291341 28736476990945381346359253)
                  ·
                    refine ⟨673511179475282375305295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28736476990945381346359253 673511179475282375305295)
                    ·
                      rfl

theorem cell23_3934975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 2, 3, 7].length) (baseStart_3934975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3934975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3934975 prefixEnd_3934975 := by exact prefixLift 3934975
  have htrace : WordTrace (prefixWord ++ tailWord_3934975) baseStart_3934975 baseEnd_3934975 := by
    simpa [prefixWord, tailWord_3934975, baseEnd_3934975] using wordTrace_append hprefix tailTrace_3934975
  have hstable : (prefixWord ++ tailWord_3934975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3934975).length < 2 ^ (prefixWord ++ tailWord_3934975).sum := by decide
  have hdescent : baseEnd_3934975 < baseStart_3934975 := by decide
  rcases family_descends (prefixWord ++ tailWord_3934975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3935039 : List Nat := [1, 1, 2, 2, 5, 1, 1, 3, 3, 4]
def baseStart_3935039 : Nat := 118140960795 + 3935039 * 2 ^ 59
def prefixEnd_3935039 : Nat := 4983230072969 + 3 ^ 40 * 3935039 * 2
def baseEnd_3935039 : Nat := 673522133729244958505197

theorem tailTrace_3935039 : CollatzResearch.WordTrace tailWord_3935039 prefixEnd_3935039 673522133729244958505197 := by
  unfold tailWord_3935039
  simp only [CollatzResearch.WordTrace]
  refine ⟨143522663191033229001584171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95681775460688819334389447 143522663191033229001584171)
  ·
    refine ⟨215283994786549843502376257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143522663191033229001584171 215283994786549843502376257)
    ·
      refine ⟨161462996089912382626782193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215283994786549843502376257 161462996089912382626782193)
      ·
        refine ⟨121097247067434286970086645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161462996089912382626782193 121097247067434286970086645)
        ·
          refine ⟨11352866912571964403445623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 121097247067434286970086645 11352866912571964403445623)
          ·
            refine ⟨17029300368857946605168435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11352866912571964403445623 17029300368857946605168435)
            ·
              refine ⟨25543950553286919907752653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17029300368857946605168435 25543950553286919907752653)
              ·
                refine ⟨9578981457482594965407245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25543950553286919907752653 9578981457482594965407245)
                ·
                  refine ⟨3592118046555973112027717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9578981457482594965407245 3592118046555973112027717)
                  ·
                    refine ⟨673522133729244958505197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3592118046555973112027717 673522133729244958505197)
                    ·
                      rfl

theorem cell23_3935039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 3, 3, 4].length) (baseStart_3935039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3935039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3935039 prefixEnd_3935039 := by exact prefixLift 3935039
  have htrace : WordTrace (prefixWord ++ tailWord_3935039) baseStart_3935039 baseEnd_3935039 := by
    simpa [prefixWord, tailWord_3935039, baseEnd_3935039] using wordTrace_append hprefix tailTrace_3935039
  have hstable : (prefixWord ++ tailWord_3935039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3935039).length < 2 ^ (prefixWord ++ tailWord_3935039).sum := by decide
  have hdescent : baseEnd_3935039 < baseStart_3935039 := by decide
  rcases family_descends (prefixWord ++ tailWord_3935039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3935139 : List Nat := [1, 1, 1, 4, 1, 2, 5, 1, 1, 1, 5]
def baseStart_3935139 : Nat := 118140960795 + 3935139 * 2 ^ 59
def prefixEnd_3935139 : Nat := 4983230072969 + 3 ^ 40 * 3935139 * 2
def baseEnd_3935139 : Nat := 2020617749253184484265131

theorem tailTrace_3935139 : CollatzResearch.WordTrace tailWord_3935139 prefixEnd_3935139 2020617749253184484265131 := by
  unfold tailWord_3935139
  simp only [CollatzResearch.WordTrace]
  refine ⟨143526310490670946080224471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95684206993780630720149647 143526310490670946080224471)
  ·
    refine ⟨215289465736006419120336707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143526310490670946080224471 215289465736006419120336707)
    ·
      refine ⟨322934198604009628680505061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215289465736006419120336707 322934198604009628680505061)
      ·
        refine ⟨60550162238251805377594699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 322934198604009628680505061 60550162238251805377594699)
        ·
          refine ⟨90825243357377708066392049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60550162238251805377594699 90825243357377708066392049)
          ·
            refine ⟨68118932518033281049794037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90825243357377708066392049 68118932518033281049794037)
            ·
              refine ⟨6386149923565620098418191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 68118932518033281049794037 6386149923565620098418191)
              ·
                refine ⟨9579224885348430147627287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6386149923565620098418191 9579224885348430147627287)
                ·
                  refine ⟨14368837328022645221440931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9579224885348430147627287 14368837328022645221440931)
                  ·
                    refine ⟨21553255992033967832161397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14368837328022645221440931 21553255992033967832161397)
                    ·
                      refine ⟨2020617749253184484265131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21553255992033967832161397 2020617749253184484265131)
                      ·
                        rfl

theorem cell23_3935139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 5, 1, 1, 1, 5].length) (baseStart_3935139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3935139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3935139 prefixEnd_3935139 := by exact prefixLift 3935139
  have htrace : WordTrace (prefixWord ++ tailWord_3935139) baseStart_3935139 baseEnd_3935139 := by
    simpa [prefixWord, tailWord_3935139, baseEnd_3935139] using wordTrace_append hprefix tailTrace_3935139
  have hstable : (prefixWord ++ tailWord_3935139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3935139).length < 2 ^ (prefixWord ++ tailWord_3935139).sum := by decide
  have hdescent : baseEnd_3935139 < baseStart_3935139 := by decide
  rcases family_descends (prefixWord ++ tailWord_3935139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3935166 : List Nat := [4, 2, 1, 1, 1, 2, 4, 1, 1, 2, 4]
def baseStart_3935166 : Nat := 118140960795 + 3935166 * 2 ^ 59
def prefixEnd_3935166 : Nat := 4983230072969 + 3 ^ 40 * 3935166 * 2
def baseEnd_3935166 : Nat := 2020631613230855878627507

theorem tailTrace_3935166 : CollatzResearch.WordTrace tailWord_3935166 prefixEnd_3935166 2020631613230855878627507 := by
  unfold tailWord_3935166
  simp only [CollatzResearch.WordTrace]
  refine ⟨17940911907696641211432169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95684863507715419794304901 17940911907696641211432169)
  ·
    refine ⟨13455683930772480908574127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17940911907696641211432169 13455683930772480908574127)
    ·
      refine ⟨20183525896158721362861191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13455683930772480908574127 20183525896158721362861191)
      ·
        refine ⟨30275288844238082044291787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20183525896158721362861191 30275288844238082044291787)
        ·
          refine ⟨45412933266357123066437681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30275288844238082044291787 45412933266357123066437681)
          ·
            refine ⟨34059699949767842299828261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45412933266357123066437681 34059699949767842299828261)
            ·
              refine ⟨6386193740581470431217799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34059699949767842299828261 6386193740581470431217799)
              ·
                refine ⟨9579290610872205646826699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6386193740581470431217799 9579290610872205646826699)
                ·
                  refine ⟨14368935916308308470240049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9579290610872205646826699 14368935916308308470240049)
                  ·
                    refine ⟨10776701937231231352680037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14368935916308308470240049 10776701937231231352680037)
                    ·
                      refine ⟨2020631613230855878627507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10776701937231231352680037 2020631613230855878627507)
                      ·
                        rfl

theorem cell23_3935166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 4, 1, 1, 2, 4].length) (baseStart_3935166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3935166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3935166 prefixEnd_3935166 := by exact prefixLift 3935166
  have htrace : WordTrace (prefixWord ++ tailWord_3935166) baseStart_3935166 baseEnd_3935166 := by
    simpa [prefixWord, tailWord_3935166, baseEnd_3935166] using wordTrace_append hprefix tailTrace_3935166
  have hstable : (prefixWord ++ tailWord_3935166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3935166).length < 2 ^ (prefixWord ++ tailWord_3935166).sum := by decide
  have hdescent : baseEnd_3935166 < baseStart_3935166 := by decide
  rcases family_descends (prefixWord ++ tailWord_3935166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3935174 : List Nat := [6, 1, 3, 1, 1, 1, 1, 1, 1, 5, 2]
def baseStart_3935174 : Nat := 118140960795 + 3935174 * 2 ^ 59
def prefixEnd_3935174 : Nat := 4983230072969 + 3 ^ 40 * 3935174 * 2
def baseEnd_3935174 : Nat := 2020635721076091847327471

theorem tailTrace_3935174 : CollatzResearch.WordTrace tailWord_3935174 prefixEnd_3935174 2020635721076091847327471 := by
  unfold tailWord_3935174
  simp only [CollatzResearch.WordTrace]
  refine ⟨4485237095173254595554643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 95685058030362764705165717 4485237095173254595554643)
  ·
    refine ⟨6727855642759881893331965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4485237095173254595554643 6727855642759881893331965)
    ·
      refine ⟨2522945866034955709999487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6727855642759881893331965 2522945866034955709999487)
      ·
        refine ⟨3784418799052433564999231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2522945866034955709999487 3784418799052433564999231)
        ·
          refine ⟨5676628198578650347498847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3784418799052433564999231 5676628198578650347498847)
          ·
            refine ⟨8514942297867975521248271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5676628198578650347498847 8514942297867975521248271)
            ·
              refine ⟨12772413446801963281872407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8514942297867975521248271 12772413446801963281872407)
              ·
                refine ⟨19158620170202944922808611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12772413446801963281872407 19158620170202944922808611)
                ·
                  refine ⟨28737930255304417384212917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19158620170202944922808611 28737930255304417384212917)
                  ·
                    refine ⟨2694180961434789129769961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 28737930255304417384212917 2694180961434789129769961)
                    ·
                      refine ⟨2020635721076091847327471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2694180961434789129769961 2020635721076091847327471)
                      ·
                        rfl

theorem cell23_3935174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 1, 1, 1, 5, 2].length) (baseStart_3935174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3935174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3935174 prefixEnd_3935174 := by exact prefixLift 3935174
  have htrace : WordTrace (prefixWord ++ tailWord_3935174) baseStart_3935174 baseEnd_3935174 := by
    simpa [prefixWord, tailWord_3935174, baseEnd_3935174] using wordTrace_append hprefix tailTrace_3935174
  have hstable : (prefixWord ++ tailWord_3935174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3935174).length < 2 ^ (prefixWord ++ tailWord_3935174).sum := by decide
  have hdescent : baseEnd_3935174 < baseStart_3935174 := by decide
  rcases family_descends (prefixWord ++ tailWord_3935174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3935176 : List Nat := [2, 1, 3, 1, 5, 1, 3, 7]
def baseStart_3935176 : Nat := 118140960795 + 3935176 * 2 ^ 59
def prefixEnd_3935176 : Nat := 4983230072969 + 3 ^ 40 * 3935176 * 2
def baseEnd_3935176 : Nat := 74838398075459290351943

theorem tailTrace_3935176 : CollatzResearch.WordTrace tailWord_3935176 prefixEnd_3935176 74838398075459290351943 := by
  unfold tailWord_3935176
  simp only [CollatzResearch.WordTrace]
  refine ⟨71763829995768450699660691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95685106661024600932880921 71763829995768450699660691)
  ·
    refine ⟨107645744993652676049491037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71763829995768450699660691 107645744993652676049491037)
    ·
      refine ⟨40367154372619753518559139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107645744993652676049491037 40367154372619753518559139)
      ·
        refine ⟨60550731558929630277838709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40367154372619753518559139 60550731558929630277838709)
        ·
          refine ⟨5676631083649652838547379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 60550731558929630277838709 5676631083649652838547379)
          ·
            refine ⟨8514946625474479257821069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5676631083649652838547379 8514946625474479257821069)
            ·
              refine ⟨3193104984552929721682901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8514946625474479257821069 3193104984552929721682901)
              ·
                refine ⟨74838398075459290351943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3193104984552929721682901 74838398075459290351943)
                ·
                  rfl

theorem cell23_3935176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 3, 7].length) (baseStart_3935176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3935176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3935176 prefixEnd_3935176 := by exact prefixLift 3935176
  have htrace : WordTrace (prefixWord ++ tailWord_3935176) baseStart_3935176 baseEnd_3935176 := by
    simpa [prefixWord, tailWord_3935176, baseEnd_3935176] using wordTrace_append hprefix tailTrace_3935176
  have hstable : (prefixWord ++ tailWord_3935176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3935176).length < 2 ^ (prefixWord ++ tailWord_3935176).sum := by decide
  have hdescent : baseEnd_3935176 < baseStart_3935176 := by decide
  rcases family_descends (prefixWord ++ tailWord_3935176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3935181 : List Nat := [1, 6, 3, 1, 1, 1, 2, 3, 1, 1, 3]
def baseStart_3935181 : Nat := 118140960795 + 3935181 * 2 ^ 59
def prefixEnd_3935181 : Nat := 4983230072969 + 3 ^ 40 * 3935181 * 2
def baseEnd_3935181 : Nat := 2020639315440673319939939

theorem tailTrace_3935181 : CollatzResearch.WordTrace tailWord_3935181 prefixEnd_3935181 2020639315440673319939939 := by
  unfold tailWord_3935181
  simp only [CollatzResearch.WordTrace]
  refine ⟨143527842356518787253253397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95685228237679191502168931 143527842356518787253253397)
  ·
    refine ⟨6727867610461818152496253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 143527842356518787253253397 6727867610461818152496253)
    ·
      refine ⟨2522950353923181807186095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6727867610461818152496253 2522950353923181807186095)
      ·
        refine ⟨3784425530884772710779143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2522950353923181807186095 3784425530884772710779143)
        ·
          refine ⟨5676638296327159066168715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3784425530884772710779143 5676638296327159066168715)
          ·
            refine ⟨8514957444490738599253073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5676638296327159066168715 8514957444490738599253073)
            ·
              refine ⟨6386218083368053949439805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8514957444490738599253073 6386218083368053949439805)
              ·
                refine ⟨2394831781263020231039927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6386218083368053949439805 2394831781263020231039927)
                ·
                  refine ⟨3592247671894530346559891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2394831781263020231039927 3592247671894530346559891)
                  ·
                    refine ⟨5388371507841795519839837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3592247671894530346559891 5388371507841795519839837)
                    ·
                      refine ⟨2020639315440673319939939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5388371507841795519839837 2020639315440673319939939)
                      ·
                        rfl

theorem cell23_3935181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 2, 3, 1, 1, 3].length) (baseStart_3935181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3935181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3935181 prefixEnd_3935181 := by exact prefixLift 3935181
  have htrace : WordTrace (prefixWord ++ tailWord_3935181) baseStart_3935181 baseEnd_3935181 := by
    simpa [prefixWord, tailWord_3935181, baseEnd_3935181] using wordTrace_append hprefix tailTrace_3935181
  have hstable : (prefixWord ++ tailWord_3935181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3935181).length < 2 ^ (prefixWord ++ tailWord_3935181).sum := by decide
  have hdescent : baseEnd_3935181 < baseStart_3935181 := by decide
  rcases family_descends (prefixWord ++ tailWord_3935181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3935190 : List Nat := [5, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3]
def baseStart_3935190 : Nat := 118140960795 + 3935190 * 2 ^ 59
def prefixEnd_3935190 : Nat := 4983230072969 + 3 ^ 40 * 3935190 * 2
def baseEnd_3935190 : Nat := 2020643936766563784727397

theorem tailTrace_3935190 : CollatzResearch.WordTrace tailWord_3935190 prefixEnd_3935190 2020643936766563784727397 := by
  unfold tailWord_3935190
  simp only [CollatzResearch.WordTrace]
  refine ⟨8970510663342886361895689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 95685447075657454526887349 8970510663342886361895689)
  ·
    refine ⟨6727882997507164771421767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8970510663342886361895689 6727882997507164771421767)
    ·
      refine ⟨10091824496260747157132651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6727882997507164771421767 10091824496260747157132651)
      ·
        refine ⟨15137736744391120735698977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10091824496260747157132651 15137736744391120735698977)
        ·
          refine ⟨11353302558293340551774233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15137736744391120735698977 11353302558293340551774233)
          ·
            refine ⟨8514976918720005413830675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11353302558293340551774233 8514976918720005413830675)
            ·
              refine ⟨12772465378080008120746013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8514976918720005413830675 12772465378080008120746013)
              ·
                refine ⟨4789674516780003045279755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12772465378080008120746013 4789674516780003045279755)
                ·
                  refine ⟨7184511775170004567919633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4789674516780003045279755 7184511775170004567919633)
                  ·
                    refine ⟨5388383831377503425939725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7184511775170004567919633 5388383831377503425939725)
                    ·
                      refine ⟨2020643936766563784727397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5388383831377503425939725 2020643936766563784727397)
                      ·
                        rfl

theorem cell23_3935190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3].length) (baseStart_3935190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3935190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3935190 prefixEnd_3935190 := by exact prefixLift 3935190
  have htrace : WordTrace (prefixWord ++ tailWord_3935190) baseStart_3935190 baseEnd_3935190 := by
    simpa [prefixWord, tailWord_3935190, baseEnd_3935190] using wordTrace_append hprefix tailTrace_3935190
  have hstable : (prefixWord ++ tailWord_3935190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3935190).length < 2 ^ (prefixWord ++ tailWord_3935190).sum := by decide
  have hdescent : baseEnd_3935190 < baseStart_3935190 := by decide
  rcases family_descends (prefixWord ++ tailWord_3935190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3935229 : List Nat := [1, 4, 1, 1, 1, 2, 1, 4, 2, 1, 5]
def baseStart_3935229 : Nat := 118140960795 + 3935229 * 2 ^ 59
def prefixEnd_3935229 : Nat := 4983230072969 + 3 ^ 40 * 3935229 * 2
def baseEnd_3935229 : Nat := 2020663962512089132139717

theorem tailTrace_3935229 : CollatzResearch.WordTrace tailWord_3935229 prefixEnd_3935229 2020663962512089132139717 := by
  unfold tailWord_3935229
  simp only [CollatzResearch.WordTrace]
  refine ⟨143529593060344891451000741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95686395373563260967333827 143529593060344891451000741)
  ·
    refine ⟨26911798698814667147062639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 143529593060344891451000741 26911798698814667147062639)
    ·
      refine ⟨40367698048222000720593959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26911798698814667147062639 40367698048222000720593959)
      ·
        refine ⟨60551547072333001080890939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40367698048222000720593959 60551547072333001080890939)
        ·
          refine ⟨90827320608499501621336409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60551547072333001080890939 90827320608499501621336409)
          ·
            refine ⟨68120490456374626216002307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90827320608499501621336409 68120490456374626216002307)
            ·
              refine ⟨102180735684561939324003461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68120490456374626216002307 102180735684561939324003461)
              ·
                refine ⟨19158887940855363623250649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 102180735684561939324003461 19158887940855363623250649)
                ·
                  refine ⟨14369165955641522717437987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19158887940855363623250649 14369165955641522717437987)
                  ·
                    refine ⟨21553748933462284076156981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14369165955641522717437987 21553748933462284076156981)
                    ·
                      refine ⟨2020663962512089132139717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21553748933462284076156981 2020663962512089132139717)
                      ·
                        rfl

theorem cell23_3935229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 4, 2, 1, 5].length) (baseStart_3935229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3935229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3935229 prefixEnd_3935229 := by exact prefixLift 3935229
  have htrace : WordTrace (prefixWord ++ tailWord_3935229) baseStart_3935229 baseEnd_3935229 := by
    simpa [prefixWord, tailWord_3935229, baseEnd_3935229] using wordTrace_append hprefix tailTrace_3935229
  have hstable : (prefixWord ++ tailWord_3935229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3935229).length < 2 ^ (prefixWord ++ tailWord_3935229).sum := by decide
  have hdescent : baseEnd_3935229 < baseStart_3935229 := by decide
  rcases family_descends (prefixWord ++ tailWord_3935229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3935243 : List Nat := [1, 1, 1, 1, 6, 2, 1, 2, 4, 2, 2]
def baseStart_3935243 : Nat := 118140960795 + 3935243 * 2 ^ 59
def prefixEnd_3935243 : Nat := 4983230072969 + 3 ^ 40 * 3935243 * 2
def baseEnd_3935243 : Nat := 2020671151241252077364653

theorem tailTrace_3935243 : CollatzResearch.WordTrace tailWord_3935243 prefixEnd_3935243 2020671151241252077364653 := by
  unfold tailWord_3935243
  simp only [CollatzResearch.WordTrace]
  refine ⟨143530103682294171842010383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95686735788196114561340255 143530103682294171842010383)
  ·
    refine ⟨215295155523441257763015575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143530103682294171842010383 215295155523441257763015575)
    ·
      refine ⟨322942733285161886644523363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215295155523441257763015575 322942733285161886644523363)
      ·
        refine ⟨484414099927742829966785045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 322942733285161886644523363 484414099927742829966785045)
        ·
          refine ⟨22706910934112945154693049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 484414099927742829966785045 22706910934112945154693049)
          ·
            refine ⟨17030183200584708866019787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22706910934112945154693049 17030183200584708866019787)
            ·
              refine ⟨25545274800877063299029681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17030183200584708866019787 25545274800877063299029681)
              ·
                refine ⟨19158956100657797474272261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25545274800877063299029681 19158956100657797474272261)
                ·
                  refine ⟨3592304268873337026426049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19158956100657797474272261 3592304268873337026426049)
                  ·
                    refine ⟨2694228201655002769819537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3592304268873337026426049 2694228201655002769819537)
                    ·
                      refine ⟨2020671151241252077364653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2694228201655002769819537 2020671151241252077364653)
                      ·
                        rfl

theorem cell23_3935243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 2, 4, 2, 2].length) (baseStart_3935243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3935243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3935243 prefixEnd_3935243 := by exact prefixLift 3935243
  have htrace : WordTrace (prefixWord ++ tailWord_3935243) baseStart_3935243 baseEnd_3935243 := by
    simpa [prefixWord, tailWord_3935243, baseEnd_3935243] using wordTrace_append hprefix tailTrace_3935243
  have hstable : (prefixWord ++ tailWord_3935243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3935243).length < 2 ^ (prefixWord ++ tailWord_3935243).sum := by decide
  have hdescent : baseEnd_3935243 < baseStart_3935243 := by decide
  rcases family_descends (prefixWord ++ tailWord_3935243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3935246 : List Nat := [4, 1, 1, 2, 2, 3, 1, 1, 2, 1, 5]
def baseStart_3935246 : Nat := 118140960795 + 3935246 * 2 ^ 59
def prefixEnd_3935246 : Nat := 4983230072969 + 3 ^ 40 * 3935246 * 2
def baseEnd_3935246 : Nat := 2020672691683215565627139

theorem tailTrace_3935246 : CollatzResearch.WordTrace tailWord_3935246 prefixEnd_3935246 2020672691683215565627139 := by
  unfold tailWord_3935246
  simp only [CollatzResearch.WordTrace]
  refine ⟨17941276637660412919296199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95686808734188868902913061 17941276637660412919296199)
  ·
    refine ⟨26911914956490619378944299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17941276637660412919296199 26911914956490619378944299)
    ·
      refine ⟨40367872434735929068416449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26911914956490619378944299 40367872434735929068416449)
      ·
        refine ⟨30275904326051946801312337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40367872434735929068416449 30275904326051946801312337)
        ·
          refine ⟨22706928244538960100984253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30275904326051946801312337 22706928244538960100984253)
          ·
            refine ⟨8515098091702110037869095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22706928244538960100984253 8515098091702110037869095)
            ·
              refine ⟨12772647137553165056803643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8515098091702110037869095 12772647137553165056803643)
              ·
                refine ⟨19158970706329747585205465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12772647137553165056803643 19158970706329747585205465)
                ·
                  refine ⟨14369228029747310688904099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19158970706329747585205465 14369228029747310688904099)
                  ·
                    refine ⟨21553842044620966033356149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14369228029747310688904099 21553842044620966033356149)
                    ·
                      refine ⟨2020672691683215565627139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21553842044620966033356149 2020672691683215565627139)
                      ·
                        rfl

theorem cell23_3935246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 1, 1, 2, 1, 5].length) (baseStart_3935246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3935246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3935246 prefixEnd_3935246 := by exact prefixLift 3935246
  have htrace : WordTrace (prefixWord ++ tailWord_3935246) baseStart_3935246 baseEnd_3935246 := by
    simpa [prefixWord, tailWord_3935246, baseEnd_3935246] using wordTrace_append hprefix tailTrace_3935246
  have hstable : (prefixWord ++ tailWord_3935246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3935246).length < 2 ^ (prefixWord ++ tailWord_3935246).sum := by decide
  have hdescent : baseEnd_3935246 < baseStart_3935246 := by decide
  rcases family_descends (prefixWord ++ tailWord_3935246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3935266 : List Nat := [3, 3, 1, 1, 1, 3, 3, 1, 7]
def baseStart_3935266 : Nat := 118140960795 + 3935266 * 2 ^ 59
def prefixEnd_3935266 : Nat := 4983230072969 + 3 ^ 40 * 3935266 * 2
def baseEnd_3935266 : Nat := 224520329032922831930783

theorem tailTrace_3935266 : CollatzResearch.WordTrace tailWord_3935266 prefixEnd_3935266 224520329032922831930783 := by
  unfold tailWord_3935266
  simp only [CollatzResearch.WordTrace]
  refine ⟨35882735640302711692524413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95687295040807231180065101 35882735640302711692524413)
  ·
    refine ⟨13456025865113516884696655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35882735640302711692524413 13456025865113516884696655)
    ·
      refine ⟨20184038797670275327044983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13456025865113516884696655 20184038797670275327044983)
      ·
        refine ⟨30276058196505412990567475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20184038797670275327044983 30276058196505412990567475)
        ·
          refine ⟨45414087294758119485851213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30276058196505412990567475 45414087294758119485851213)
          ·
            refine ⟨17030282735534294807194205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45414087294758119485851213 17030282735534294807194205)
            ·
              refine ⟨6386356025825360552697827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17030282735534294807194205 6386356025825360552697827)
              ·
                refine ⟨9579534038738040829046741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6386356025825360552697827 9579534038738040829046741)
                ·
                  refine ⟨224520329032922831930783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9579534038738040829046741 224520329032922831930783)
                  ·
                    rfl

theorem cell23_3935266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 3, 1, 7].length) (baseStart_3935266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3935266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3935266 prefixEnd_3935266 := by exact prefixLift 3935266
  have htrace : WordTrace (prefixWord ++ tailWord_3935266) baseStart_3935266 baseEnd_3935266 := by
    simpa [prefixWord, tailWord_3935266, baseEnd_3935266] using wordTrace_append hprefix tailTrace_3935266
  have hstable : (prefixWord ++ tailWord_3935266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3935266).length < 2 ^ (prefixWord ++ tailWord_3935266).sum := by decide
  have hdescent : baseEnd_3935266 < baseStart_3935266 := by decide
  rcases family_descends (prefixWord ++ tailWord_3935266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3935296 : List Nat := [2, 1, 1, 2, 2, 3, 4, 1, 2, 5]
def baseStart_3935296 : Nat := 118140960795 + 3935296 * 2 ^ 59
def prefixEnd_3935296 : Nat := 4983230072969 + 3 ^ 40 * 3935296 * 2
def baseEnd_3935296 : Nat := 673566121905313456667303

theorem tailTrace_3935296 : CollatzResearch.WordTrace tailWord_3935296 prefixEnd_3935296 673566121905313456667303 := by
  unfold tailWord_3935296
  simp only [CollatzResearch.WordTrace]
  refine ⟨71766018375551080946844871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95688024500734774595793161 71766018375551080946844871)
  ·
    refine ⟨107649027563326621420267307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71766018375551080946844871 107649027563326621420267307)
    ·
      refine ⟨161473541344989932130400961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107649027563326621420267307 161473541344989932130400961)
      ·
        refine ⟨121105156008742449097800721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161473541344989932130400961 121105156008742449097800721)
        ·
          refine ⟨90828867006556836823350541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121105156008742449097800721 90828867006556836823350541)
          ·
            refine ⟨34060825127458813808756453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90828867006556836823350541 34060825127458813808756453)
            ·
              refine ⟨6386404711398527589141835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34060825127458813808756453 6386404711398527589141835)
              ·
                refine ⟨9579607067097791383712753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6386404711398527589141835 9579607067097791383712753)
                ·
                  refine ⟨7184705300323343537784565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9579607067097791383712753 7184705300323343537784565)
                  ·
                    refine ⟨673566121905313456667303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7184705300323343537784565 673566121905313456667303)
                    ·
                      rfl

theorem cell23_3935296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 4, 1, 2, 5].length) (baseStart_3935296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3935296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3935296 prefixEnd_3935296 := by exact prefixLift 3935296
  have htrace : WordTrace (prefixWord ++ tailWord_3935296) baseStart_3935296 baseEnd_3935296 := by
    simpa [prefixWord, tailWord_3935296, baseEnd_3935296] using wordTrace_append hprefix tailTrace_3935296
  have hstable : (prefixWord ++ tailWord_3935296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3935296).length < 2 ^ (prefixWord ++ tailWord_3935296).sum := by decide
  have hdescent : baseEnd_3935296 < baseStart_3935296 := by decide
  rcases family_descends (prefixWord ++ tailWord_3935296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3935319 : List Nat := [1, 1, 3, 2, 2, 1, 1, 1, 1, 5, 5]
def baseStart_3935319 : Nat := 118140960795 + 3935319 * 2 ^ 59
def prefixEnd_3935319 : Nat := 4983230072969 + 3 ^ 40 * 3935319 * 2
def baseEnd_3935319 : Nat := 2020710175770993780014303

theorem tailTrace_3935319 : CollatzResearch.WordTrace tailWord_3935319 prefixEnd_3935319 2020710175770993780014303 := by
  unfold tailWord_3935319
  simp only [CollatzResearch.WordTrace]
  refine ⟨143532875630018836821777011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95688583753345891214518007 143532875630018836821777011)
  ·
    refine ⟨215299313445028255232665517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143532875630018836821777011 215299313445028255232665517)
    ·
      refine ⟨80737242541885595712249569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 215299313445028255232665517 80737242541885595712249569)
      ·
        refine ⟨60552931906414196784187177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80737242541885595712249569 60552931906414196784187177)
        ·
          refine ⟨45414698929810647588140383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60552931906414196784187177 45414698929810647588140383)
          ·
            refine ⟨68122048394715971382210575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45414698929810647588140383 68122048394715971382210575)
            ·
              refine ⟨102183072592073957073315863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68122048394715971382210575 102183072592073957073315863)
              ·
                refine ⟨153274608888110935609973795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102183072592073957073315863 153274608888110935609973795)
                ·
                  refine ⟨229911913332166403414960693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 153274608888110935609973795 229911913332166403414960693)
                  ·
                    refine ⟨21554241874890600320152565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 229911913332166403414960693 21554241874890600320152565)
                    ·
                      refine ⟨2020710175770993780014303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21554241874890600320152565 2020710175770993780014303)
                      ·
                        rfl

theorem cell23_3935319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 1, 1, 5, 5].length) (baseStart_3935319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3935319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3935319 prefixEnd_3935319 := by exact prefixLift 3935319
  have htrace : WordTrace (prefixWord ++ tailWord_3935319) baseStart_3935319 baseEnd_3935319 := by
    simpa [prefixWord, tailWord_3935319, baseEnd_3935319] using wordTrace_append hprefix tailTrace_3935319
  have hstable : (prefixWord ++ tailWord_3935319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3935319).length < 2 ^ (prefixWord ++ tailWord_3935319).sum := by decide
  have hdescent : baseEnd_3935319 < baseStart_3935319 := by decide
  rcases family_descends (prefixWord ++ tailWord_3935319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3935333 : List Nat := [1, 3, 1, 3, 2, 1, 3, 1, 2, 4, 2]
def baseStart_3935333 : Nat := 118140960795 + 3935333 * 2 ^ 59
def prefixEnd_3935333 : Nat := 4983230072969 + 3 ^ 40 * 3935333 * 2
def baseEnd_3935333 : Nat := 2020717364500156725239239

theorem tailTrace_3935333 : CollatzResearch.WordTrace tailWord_3935333 prefixEnd_3935333 2020717364500156725239239 := by
  unfold tailWord_3935333
  simp only [CollatzResearch.WordTrace]
  refine ⟨143533386251968117212786653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95688924167978744808524435 143533386251968117212786653)
  ·
    refine ⟨53825019844488043954794995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143533386251968117212786653 53825019844488043954794995)
    ·
      refine ⟨80737529766732065932192493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53825019844488043954794995 80737529766732065932192493)
      ·
        refine ⟨30276573662524524724572185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80737529766732065932192493 30276573662524524724572185)
        ·
          refine ⟨22707430246893393543429139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30276573662524524724572185 22707430246893393543429139)
          ·
            refine ⟨34061145370340090315143709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22707430246893393543429139 34061145370340090315143709)
            ·
              refine ⟨12772929513877533868178891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34061145370340090315143709 12772929513877533868178891)
              ·
                refine ⟨19159394270816300802268337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12772929513877533868178891 19159394270816300802268337)
                ·
                  refine ⟨14369545703112225601701253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19159394270816300802268337 14369545703112225601701253)
                  ·
                    refine ⟨2694289819333542300318985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14369545703112225601701253 2694289819333542300318985)
                    ·
                      refine ⟨2020717364500156725239239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2694289819333542300318985 2020717364500156725239239)
                      ·
                        rfl

theorem cell23_3935333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 3, 1, 2, 4, 2].length) (baseStart_3935333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3935333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3935333 prefixEnd_3935333 := by exact prefixLift 3935333
  have htrace : WordTrace (prefixWord ++ tailWord_3935333) baseStart_3935333 baseEnd_3935333 := by
    simpa [prefixWord, tailWord_3935333, baseEnd_3935333] using wordTrace_append hprefix tailTrace_3935333
  have hstable : (prefixWord ++ tailWord_3935333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3935333).length < 2 ^ (prefixWord ++ tailWord_3935333).sum := by decide
  have hdescent : baseEnd_3935333 < baseStart_3935333 := by decide
  rcases family_descends (prefixWord ++ tailWord_3935333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3935353 : List Nat := [1, 2, 1, 3, 5, 1, 1, 1, 1, 4, 3]
def baseStart_3935353 : Nat := 118140960795 + 3935353 * 2 ^ 59
def prefixEnd_3935353 : Nat := 4983230072969 + 3 ^ 40 * 3935353 * 2
def baseEnd_3935353 : Nat := 2020727634113246646989147

theorem tailTrace_3935353 : CollatzResearch.WordTrace tailWord_3935353 prefixEnd_3935353 2020727634113246646989147 := by
  unfold tailWord_3935353
  simp only [CollatzResearch.WordTrace]
  refine ⟨143534115711895660628514713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95689410474597107085676475 143534115711895660628514713)
  ·
    refine ⟨107650586783921745471386035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143534115711895660628514713 107650586783921745471386035)
    ·
      refine ⟨161475880175882618207079053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107650586783921745471386035 161475880175882618207079053)
      ·
        refine ⟨60553455065955981827654645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 161475880175882618207079053 60553455065955981827654645)
        ·
          refine ⟨5676886412433373296342623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 60553455065955981827654645 5676886412433373296342623)
          ·
            refine ⟨8515329618650059944513935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5676886412433373296342623 8515329618650059944513935)
            ·
              refine ⟨12772994427975089916770903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8515329618650059944513935 12772994427975089916770903)
              ·
                refine ⟨19159491641962634875156355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12772994427975089916770903 19159491641962634875156355)
                ·
                  refine ⟨28739237462943952312734533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19159491641962634875156355 28739237462943952312734533)
                  ·
                    refine ⟨5388607024301991058637725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28739237462943952312734533 5388607024301991058637725)
                    ·
                      refine ⟨2020727634113246646989147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5388607024301991058637725 2020727634113246646989147)
                      ·
                        rfl

theorem cell23_3935353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 1, 1, 1, 4, 3].length) (baseStart_3935353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3935353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3935353 prefixEnd_3935353 := by exact prefixLift 3935353
  have htrace : WordTrace (prefixWord ++ tailWord_3935353) baseStart_3935353 baseEnd_3935353 := by
    simpa [prefixWord, tailWord_3935353, baseEnd_3935353] using wordTrace_append hprefix tailTrace_3935353
  have hstable : (prefixWord ++ tailWord_3935353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3935353).length < 2 ^ (prefixWord ++ tailWord_3935353).sum := by decide
  have hdescent : baseEnd_3935353 < baseStart_3935353 := by decide
  rcases family_descends (prefixWord ++ tailWord_3935353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3935359 : List Nat := [1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 6]
def baseStart_3935359 : Nat := 118140960795 + 3935359 * 2 ^ 59
def prefixEnd_3935359 : Nat := 4983230072969 + 3 ^ 40 * 3935359 * 2
def baseEnd_3935359 : Nat := 2020730714997173623514119

theorem tailTrace_3935359 : CollatzResearch.WordTrace tailWord_3935359 prefixEnd_3935359 2020730714997173623514119 := by
  unfold tailWord_3935359
  simp only [CollatzResearch.WordTrace]
  refine ⟨143534334549873923653233131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95689556366582615768822087 143534334549873923653233131)
  ·
    refine ⟨215301501824810885479849697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143534334549873923653233131 215301501824810885479849697)
    ·
      refine ⟨161476126368608164109887273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215301501824810885479849697 161476126368608164109887273)
      ·
        refine ⟨121107094776456123082415455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161476126368608164109887273 121107094776456123082415455)
        ·
          refine ⟨181660642164684184623623183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121107094776456123082415455 181660642164684184623623183)
          ·
            refine ⟨272490963247026276935434775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181660642164684184623623183 272490963247026276935434775)
            ·
              refine ⟨408736444870539415403152163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 272490963247026276935434775 408736444870539415403152163)
              ·
                refine ⟨613104667305809123104728245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 408736444870539415403152163 613104667305809123104728245)
                ·
                  refine ⟨57478562559919605291068273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 613104667305809123104728245 57478562559919605291068273)
                  ·
                    refine ⟨43108921919939703968301205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 57478562559919605291068273 43108921919939703968301205)
                    ·
                      refine ⟨2020730714997173623514119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 43108921919939703968301205 2020730714997173623514119)
                      ·
                        rfl

theorem cell23_3935359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 6].length) (baseStart_3935359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3935359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3935359 prefixEnd_3935359 := by exact prefixLift 3935359
  have htrace : WordTrace (prefixWord ++ tailWord_3935359) baseStart_3935359 baseEnd_3935359 := by
    simpa [prefixWord, tailWord_3935359, baseEnd_3935359] using wordTrace_append hprefix tailTrace_3935359
  have hstable : (prefixWord ++ tailWord_3935359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3935359).length < 2 ^ (prefixWord ++ tailWord_3935359).sum := by decide
  have hdescent : baseEnd_3935359 < baseStart_3935359 := by decide
  rcases family_descends (prefixWord ++ tailWord_3935359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3935393 : List Nat := [1, 2, 3, 3, 1, 1, 1, 1, 3, 5, 2]
def baseStart_3935393 : Nat := 118140960795 + 3935393 * 2 ^ 59
def prefixEnd_3935393 : Nat := 4983230072969 + 3 ^ 40 * 3935393 * 2
def baseEnd_3935393 : Nat := 2020748173339426490488963

theorem tailTrace_3935393 : CollatzResearch.WordTrace tailWord_3935393 prefixEnd_3935393 2020748173339426490488963 := by
  unfold tailWord_3935393
  simp only [CollatzResearch.WordTrace]
  refine ⟨143535574631750747459970833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95690383087833831639980555 143535574631750747459970833)
  ·
    refine ⟨107651680973813060594978125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143535574631750747459970833 107651680973813060594978125)
    ·
      refine ⟨40369380365179897723116797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107651680973813060594978125 40369380365179897723116797)
      ·
        refine ⟨15138517636942461646168799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40369380365179897723116797 15138517636942461646168799)
        ·
          refine ⟨22707776455413692469253199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15138517636942461646168799 22707776455413692469253199)
          ·
            refine ⟨34061664683120538703879799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22707776455413692469253199 34061664683120538703879799)
            ·
              refine ⟨51092497024680808055819699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34061664683120538703879799 51092497024680808055819699)
              ·
                refine ⟨76638745537021212083729549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51092497024680808055819699 76638745537021212083729549)
                ·
                  refine ⟨28739529576382954531398581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76638745537021212083729549 28739529576382954531398581)
                  ·
                    refine ⟨2694330897785901987318617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 28739529576382954531398581 2694330897785901987318617)
                    ·
                      refine ⟨2020748173339426490488963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2694330897785901987318617 2020748173339426490488963)
                      ·
                        rfl

theorem cell23_3935393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 1, 3, 5, 2].length) (baseStart_3935393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3935393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3935393 prefixEnd_3935393 := by exact prefixLift 3935393
  have htrace : WordTrace (prefixWord ++ tailWord_3935393) baseStart_3935393 baseEnd_3935393 := by
    simpa [prefixWord, tailWord_3935393, baseEnd_3935393] using wordTrace_append hprefix tailTrace_3935393
  have hstable : (prefixWord ++ tailWord_3935393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3935393).length < 2 ^ (prefixWord ++ tailWord_3935393).sum := by decide
  have hdescent : baseEnd_3935393 < baseStart_3935393 := by decide
  rcases family_descends (prefixWord ++ tailWord_3935393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3935417 : List Nat := [1, 2, 1, 4, 1, 3, 3, 3, 1, 1, 3]
def baseStart_3935417 : Nat := 118140960795 + 3935417 * 2 ^ 59
def prefixEnd_3935417 : Nat := 4983230072969 + 3 ^ 40 * 3935417 * 2
def baseEnd_3935417 : Nat := 2020760496875134396588853

theorem tailTrace_3935417 : CollatzResearch.WordTrace tailWord_3935417 prefixEnd_3935417 2020760496875134396588853 := by
  unfold tailWord_3935417
  simp only [CollatzResearch.WordTrace]
  refine ⟨143536449983663799558844505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95690966655775866372563003 143536449983663799558844505)
  ·
    refine ⟨107652337487747849669133379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143536449983663799558844505 107652337487747849669133379)
    ·
      refine ⟨161478506231621774503700069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107652337487747849669133379 161478506231621774503700069)
      ·
        refine ⟨30277219918429082719443763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 161478506231621774503700069 30277219918429082719443763)
        ·
          refine ⟨45415829877643624079165645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30277219918429082719443763 45415829877643624079165645)
          ·
            refine ⟨17030936204116359029687117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45415829877643624079165645 17030936204116359029687117)
            ·
              refine ⟨6386601076543634636132669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17030936204116359029687117 6386601076543634636132669)
              ·
                refine ⟨2394975403703862988549751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6386601076543634636132669 2394975403703862988549751)
                ·
                  refine ⟨3592463105555794482824627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2394975403703862988549751 3592463105555794482824627)
                  ·
                    refine ⟨5388694658333691724236941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3592463105555794482824627 5388694658333691724236941)
                    ·
                      refine ⟨2020760496875134396588853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5388694658333691724236941 2020760496875134396588853)
                      ·
                        rfl

theorem cell23_3935417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 3, 3, 1, 1, 3].length) (baseStart_3935417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3935417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3935417 prefixEnd_3935417 := by exact prefixLift 3935417
  have htrace : WordTrace (prefixWord ++ tailWord_3935417) baseStart_3935417 baseEnd_3935417 := by
    simpa [prefixWord, tailWord_3935417, baseEnd_3935417] using wordTrace_append hprefix tailTrace_3935417
  have hstable : (prefixWord ++ tailWord_3935417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3935417).length < 2 ^ (prefixWord ++ tailWord_3935417).sum := by decide
  have hdescent : baseEnd_3935417 < baseStart_3935417 := by decide
  rcases family_descends (prefixWord ++ tailWord_3935417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3935423 : List Nat := [1, 1, 2, 2, 2, 2, 4, 3, 1, 1, 4]
def baseStart_3935423 : Nat := 118140960795 + 3935423 * 2 ^ 59
def prefixEnd_3935423 : Nat := 4983230072969 + 3 ^ 40 * 3935423 * 2
def baseEnd_3935423 : Nat := 2020763577759061373113825

theorem tailTrace_3935423 : CollatzResearch.WordTrace tailWord_3935423 prefixEnd_3935423 2020763577759061373113825 := by
  unfold tailWord_3935423
  simp only [CollatzResearch.WordTrace]
  refine ⟨143536668821642062583562923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95691112547761375055708615 143536668821642062583562923)
  ·
    refine ⟨215305003232463093875344385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143536668821642062583562923 215305003232463093875344385)
    ·
      refine ⟨161478752424347320406508289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215305003232463093875344385 161478752424347320406508289)
      ·
        refine ⟨121109064318260490304881217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161478752424347320406508289 121109064318260490304881217)
        ·
          refine ⟨90831798238695367728660913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121109064318260490304881217 90831798238695367728660913)
          ·
            refine ⟨68123848679021525796495685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90831798238695367728660913 68123848679021525796495685)
            ·
              refine ⟨12773221627316536086842941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68123848679021525796495685 12773221627316536086842941)
              ·
                refine ⟨4789958110243701032566103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12773221627316536086842941 4789958110243701032566103)
                ·
                  refine ⟨7184937165365551548849155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4789958110243701032566103 7184937165365551548849155)
                  ·
                    refine ⟨10777405748048327323273733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7184937165365551548849155 10777405748048327323273733)
                    ·
                      refine ⟨2020763577759061373113825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10777405748048327323273733 2020763577759061373113825)
                      ·
                        rfl

theorem cell23_3935423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4, 3, 1, 1, 4].length) (baseStart_3935423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3935423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3935423 prefixEnd_3935423 := by exact prefixLift 3935423
  have htrace : WordTrace (prefixWord ++ tailWord_3935423) baseStart_3935423 baseEnd_3935423 := by
    simpa [prefixWord, tailWord_3935423, baseEnd_3935423] using wordTrace_append hprefix tailTrace_3935423
  have hstable : (prefixWord ++ tailWord_3935423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3935423).length < 2 ^ (prefixWord ++ tailWord_3935423).sum := by decide
  have hdescent : baseEnd_3935423 < baseStart_3935423 := by decide
  rcases family_descends (prefixWord ++ tailWord_3935423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3935434 : List Nat := [3, 1, 2, 1, 3, 3, 3, 2, 1, 1, 3]
def baseStart_3935434 : Nat := 118140960795 + 3935434 * 2 ^ 59
def prefixEnd_3935434 : Nat := 4983230072969 + 3 ^ 40 * 3935434 * 2
def baseEnd_3935434 : Nat := 2020769226046260830076275

theorem tailTrace_3935434 : CollatzResearch.WordTrace tailWord_3935434 prefixEnd_3935434 2020769226046260830076275 := by
  unfold tailWord_3935434
  simp only [CollatzResearch.WordTrace]
  refine ⟨35884267506150552865553339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95691380016401474308142237 35884267506150552865553339)
  ·
    refine ⟨53826401259225829298330009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35884267506150552865553339 53826401259225829298330009)
    ·
      refine ⟨40369800944419371973747507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53826401259225829298330009 40369800944419371973747507)
      ·
        refine ⟨60554701416629057960621261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40369800944419371973747507 60554701416629057960621261)
        ·
          refine ⟨22708013031235896735232973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60554701416629057960621261 22708013031235896735232973)
          ·
            refine ⟨8515504886713461275712365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22708013031235896735232973 8515504886713461275712365)
            ·
              refine ⟨3193314332517547978392137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8515504886713461275712365 3193314332517547978392137)
              ·
                refine ⟨2394985749388160983794103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3193314332517547978392137 2394985749388160983794103)
                ·
                  refine ⟨3592478624082241475691155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2394985749388160983794103 3592478624082241475691155)
                  ·
                    refine ⟨5388717936123362213536733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3592478624082241475691155 5388717936123362213536733)
                    ·
                      refine ⟨2020769226046260830076275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5388717936123362213536733 2020769226046260830076275)
                      ·
                        rfl

theorem cell23_3935434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 3, 2, 1, 1, 3].length) (baseStart_3935434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3935434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3935434 prefixEnd_3935434 := by exact prefixLift 3935434
  have htrace : WordTrace (prefixWord ++ tailWord_3935434) baseStart_3935434 baseEnd_3935434 := by
    simpa [prefixWord, tailWord_3935434, baseEnd_3935434] using wordTrace_append hprefix tailTrace_3935434
  have hstable : (prefixWord ++ tailWord_3935434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3935434).length < 2 ^ (prefixWord ++ tailWord_3935434).sum := by decide
  have hdescent : baseEnd_3935434 < baseStart_3935434 := by decide
  rcases family_descends (prefixWord ++ tailWord_3935434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3935460 : List Nat := [2, 3, 1, 1, 1, 2, 5, 2, 1, 2, 3]
def baseStart_3935460 : Nat := 118140960795 + 3935460 * 2 ^ 59
def prefixEnd_3935460 : Nat := 4983230072969 + 3 ^ 40 * 3935460 * 2
def baseEnd_3935460 : Nat := 2020782576543277728351155

theorem tailTrace_3935460 : CollatzResearch.WordTrace tailWord_3935460 prefixEnd_3935460 2020782576543277728351155 := by
  unfold tailWord_3935460
  simp only [CollatzResearch.WordTrace]
  refine ⟨71769009161254008951329917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95692012215005345268439889 71769009161254008951329917)
  ·
    refine ⟨26913378435470253356748719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71769009161254008951329917 26913378435470253356748719)
    ·
      refine ⟨40370067653205380035123079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26913378435470253356748719 40370067653205380035123079)
      ·
        refine ⟨60555101479808070052684619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40370067653205380035123079 60555101479808070052684619)
        ·
          refine ⟨90832652219712105079026929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60555101479808070052684619 90832652219712105079026929)
          ·
            refine ⟨68124489164784078809270197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90832652219712105079026929 68124489164784078809270197)
            ·
              refine ⟨6386670859198507388369081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 68124489164784078809270197 6386670859198507388369081)
              ·
                refine ⟨4790003144398880541276811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6386670859198507388369081 4790003144398880541276811)
                ·
                  refine ⟨7185004716598320811915217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4790003144398880541276811 7185004716598320811915217)
                  ·
                    refine ⟨5388753537448740608936413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7185004716598320811915217 5388753537448740608936413)
                    ·
                      refine ⟨2020782576543277728351155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5388753537448740608936413 2020782576543277728351155)
                      ·
                        rfl

theorem cell23_3935460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 5, 2, 1, 2, 3].length) (baseStart_3935460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3935460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3935460 prefixEnd_3935460 := by exact prefixLift 3935460
  have htrace : WordTrace (prefixWord ++ tailWord_3935460) baseStart_3935460 baseEnd_3935460 := by
    simpa [prefixWord, tailWord_3935460, baseEnd_3935460] using wordTrace_append hprefix tailTrace_3935460
  have hstable : (prefixWord ++ tailWord_3935460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3935460).length < 2 ^ (prefixWord ++ tailWord_3935460).sum := by decide
  have hdescent : baseEnd_3935460 < baseStart_3935460 := by decide
  rcases family_descends (prefixWord ++ tailWord_3935460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3935491 : List Nat := [1, 1, 1, 3, 2, 6, 2, 2, 1, 2, 2]
def baseStart_3935491 : Nat := 118140960795 + 3935491 * 2 ^ 59
def prefixEnd_3935491 : Nat := 4983230072969 + 3 ^ 40 * 3935491 * 2
def baseEnd_3935491 : Nat := 2020798494443567107063513

theorem tailTrace_3935491 : CollatzResearch.WordTrace tailWord_3935491 prefixEnd_3935491 2020798494443567107063513 := by
  unfold tailWord_3935491
  simp only [CollatzResearch.WordTrace]
  refine ⟨143539148985395710197038327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95692765990263806798025551 143539148985395710197038327)
  ·
    refine ⟨215308723478093565295557491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143539148985395710197038327 215308723478093565295557491)
    ·
      refine ⟨322963085217140347943336237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215308723478093565295557491 322963085217140347943336237)
      ·
        refine ⟨121111156956427630478751089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 322963085217140347943336237 121111156956427630478751089)
        ·
          refine ⟨90833367717320722859063317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121111156956427630478751089 90833367717320722859063317)
          ·
            refine ⟨4257814111749408884018593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 90833367717320722859063317 4257814111749408884018593)
            ·
              refine ⟨3193360583812056663013945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4257814111749408884018593 3193360583812056663013945)
              ·
                refine ⟨2395020437859042497260459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3193360583812056663013945 2395020437859042497260459)
                ·
                  refine ⟨3592530656788563745890689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2395020437859042497260459 3592530656788563745890689)
                  ·
                    refine ⟨2694397992591422809418017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3592530656788563745890689 2694397992591422809418017)
                    ·
                      refine ⟨2020798494443567107063513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2694397992591422809418017 2020798494443567107063513)
                      ·
                        rfl

theorem cell23_3935491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 2, 2, 1, 2, 2].length) (baseStart_3935491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3935491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3935491 prefixEnd_3935491 := by exact prefixLift 3935491
  have htrace : WordTrace (prefixWord ++ tailWord_3935491) baseStart_3935491 baseEnd_3935491 := by
    simpa [prefixWord, tailWord_3935491, baseEnd_3935491] using wordTrace_append hprefix tailTrace_3935491
  have hstable : (prefixWord ++ tailWord_3935491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3935491).length < 2 ^ (prefixWord ++ tailWord_3935491).sum := by decide
  have hdescent : baseEnd_3935491 < baseStart_3935491 := by decide
  rcases family_descends (prefixWord ++ tailWord_3935491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3935500 : List Nat := [2, 2, 1, 2, 2, 3, 1, 2, 3, 3, 2]
def baseStart_3935500 : Nat := 118140960795 + 3935500 * 2 ^ 59
def prefixEnd_3935500 : Nat := 4983230072969 + 3 ^ 40 * 3935500 * 2
def baseEnd_3935500 : Nat := 2020803115769457571850971

theorem tailTrace_3935500 : CollatzResearch.WordTrace tailWord_3935500 prefixEnd_3935500 2020803115769457571850971 := by
  unfold tailWord_3935500
  simp only [CollatzResearch.WordTrace]
  refine ⟨71769738621181552367057977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95692984828242069822743969 71769738621181552367057977)
  ·
    refine ⟨53827303965886164275293483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71769738621181552367057977 53827303965886164275293483)
    ·
      refine ⟨80740955948829246412940225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53827303965886164275293483 80740955948829246412940225)
      ·
        refine ⟨60555716961621934809705169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80740955948829246412940225 60555716961621934809705169)
        ·
          refine ⟨45416787721216451107278877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60555716961621934809705169 45416787721216451107278877)
          ·
            refine ⟨17031295395456169165229579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45416787721216451107278877 17031295395456169165229579)
            ·
              refine ⟨25546943093184253747844369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17031295395456169165229579 25546943093184253747844369)
              ·
                refine ⟨19160207319888190310883277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25546943093184253747844369 19160207319888190310883277)
                ·
                  refine ⟨7185077744958071366581229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19160207319888190310883277 7185077744958071366581229)
                  ·
                    refine ⟨2694404154359276762467961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7185077744958071366581229 2694404154359276762467961)
                    ·
                      refine ⟨2020803115769457571850971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2694404154359276762467961 2020803115769457571850971)
                      ·
                        rfl

theorem cell23_3935500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 2, 3, 3, 2].length) (baseStart_3935500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3935500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3935500 prefixEnd_3935500 := by exact prefixLift 3935500
  have htrace : WordTrace (prefixWord ++ tailWord_3935500) baseStart_3935500 baseEnd_3935500 := by
    simpa [prefixWord, tailWord_3935500, baseEnd_3935500] using wordTrace_append hprefix tailTrace_3935500
  have hstable : (prefixWord ++ tailWord_3935500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3935500).length < 2 ^ (prefixWord ++ tailWord_3935500).sum := by decide
  have hdescent : baseEnd_3935500 < baseStart_3935500 := by decide
  rcases family_descends (prefixWord ++ tailWord_3935500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3935517 : List Nat := [1, 4, 2, 3, 1, 1, 2, 1, 3, 3, 2]
def baseStart_3935517 : Nat := 118140960795 + 3935517 * 2 ^ 59
def prefixEnd_3935517 : Nat := 4983230072969 + 3 ^ 40 * 3935517 * 2
def baseEnd_3935517 : Nat := 2020811844940584005338393

theorem tailTrace_3935517 : CollatzResearch.WordTrace tailWord_3935517 prefixEnd_3935517 2020811844940584005338393 := by
  unfold tailWord_3935517
  simp only [CollatzResearch.WordTrace]
  refine ⟨143540097283301516637484805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95693398188867677758323203 143540097283301516637484805)
  ·
    refine ⟨26913768240619034369528401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 143540097283301516637484805 26913768240619034369528401)
    ·
      refine ⟨20185326180464275777146301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26913768240619034369528401 20185326180464275777146301)
      ·
        refine ⟨7569497317674103416429863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20185326180464275777146301 7569497317674103416429863)
        ·
          refine ⟨11354245976511155124644795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7569497317674103416429863 11354245976511155124644795)
          ·
            refine ⟨17031368964766732686967193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11354245976511155124644795 17031368964766732686967193)
            ·
              refine ⟨12773526723575049515225395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17031368964766732686967193 12773526723575049515225395)
              ·
                refine ⟨19160290085362574272838093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12773526723575049515225395 19160290085362574272838093)
                ·
                  refine ⟨7185108782010965352314285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19160290085362574272838093 7185108782010965352314285)
                  ·
                    refine ⟨2694415793254112007117857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7185108782010965352314285 2694415793254112007117857)
                    ·
                      refine ⟨2020811844940584005338393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2694415793254112007117857 2020811844940584005338393)
                      ·
                        rfl

theorem cell23_3935517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 2, 1, 3, 3, 2].length) (baseStart_3935517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3935517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3935517 prefixEnd_3935517 := by exact prefixLift 3935517
  have htrace : WordTrace (prefixWord ++ tailWord_3935517) baseStart_3935517 baseEnd_3935517 := by
    simpa [prefixWord, tailWord_3935517, baseEnd_3935517] using wordTrace_append hprefix tailTrace_3935517
  have hstable : (prefixWord ++ tailWord_3935517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3935517).length < 2 ^ (prefixWord ++ tailWord_3935517).sum := by decide
  have hdescent : baseEnd_3935517 < baseStart_3935517 := by decide
  rcases family_descends (prefixWord ++ tailWord_3935517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3935536 : List Nat := [2, 1, 1, 1, 2, 2, 3, 2, 9]
def baseStart_3935536 : Nat := 118140960795 + 3935536 * 2 ^ 59
def prefixEnd_3935536 : Nat := 4983230072969 + 3 ^ 40 * 3935536 * 2
def baseEnd_3935536 : Nat := 224535733452557714555645

theorem tailTrace_3935536 : CollatzResearch.WordTrace tailWord_3935536 prefixEnd_3935536 224535733452557714555645 := by
  unfold tailWord_3935536
  simp only [CollatzResearch.WordTrace]
  refine ⟨71770395135116341441213231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95693860180155121921617641 71770395135116341441213231)
  ·
    refine ⟨107655592702674512161819847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71770395135116341441213231 107655592702674512161819847)
    ·
      refine ⟨161483389054011768242729771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107655592702674512161819847 161483389054011768242729771)
      ·
        refine ⟨242225083581017652364094657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161483389054011768242729771 242225083581017652364094657)
        ·
          refine ⟨181668812685763239273070993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 242225083581017652364094657 181668812685763239273070993)
          ·
            refine ⟨136251609514322429454803245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 181668812685763239273070993 136251609514322429454803245)
            ·
              refine ⟨51094353567870911045551217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 136251609514322429454803245 51094353567870911045551217)
              ·
                refine ⟨38320765175903183284163413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51094353567870911045551217 38320765175903183284163413)
                ·
                  refine ⟨224535733452557714555645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 38320765175903183284163413 224535733452557714555645)
                  ·
                    rfl

theorem cell23_3935536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 2, 9].length) (baseStart_3935536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3935536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3935536 prefixEnd_3935536 := by exact prefixLift 3935536
  have htrace : WordTrace (prefixWord ++ tailWord_3935536) baseStart_3935536 baseEnd_3935536 := by
    simpa [prefixWord, tailWord_3935536, baseEnd_3935536] using wordTrace_append hprefix tailTrace_3935536
  have hstable : (prefixWord ++ tailWord_3935536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3935536).length < 2 ^ (prefixWord ++ tailWord_3935536).sum := by decide
  have hdescent : baseEnd_3935536 < baseStart_3935536 := by decide
  rcases family_descends (prefixWord ++ tailWord_3935536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3935558 : List Nat := [6, 1, 1, 3, 2, 1, 1, 1, 1, 3, 3]
def baseStart_3935558 : Nat := 118140960795 + 3935558 * 2 ^ 59
def prefixEnd_3935558 : Nat := 4983230072969 + 3 ^ 40 * 3935558 * 2
def baseEnd_3935558 : Nat := 2020832897647418344925705

theorem tailTrace_3935558 : CollatzResearch.WordTrace tailWord_3935558 prefixEnd_3935558 2020832897647418344925705 := by
  unfold tailWord_3935558
  simp only [CollatzResearch.WordTrace]
  refine ⟨4485674771129780644991479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 95694395117435320426484885 4485674771129780644991479)
  ·
    refine ⟨6728512156694670967487219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4485674771129780644991479 6728512156694670967487219)
    ·
      refine ⟨10092768235042006451230829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6728512156694670967487219 10092768235042006451230829)
      ·
        refine ⟨3784788088140752419211561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10092768235042006451230829 3784788088140752419211561)
        ·
          refine ⟨2838591066105564314408671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3784788088140752419211561 2838591066105564314408671)
          ·
            refine ⟨4257886599158346471613007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2838591066105564314408671 4257886599158346471613007)
            ·
              refine ⟨6386829898737519707419511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4257886599158346471613007 6386829898737519707419511)
              ·
                refine ⟨9580244848106279561129267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6386829898737519707419511 9580244848106279561129267)
                ·
                  refine ⟨14370367272159419341693901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9580244848106279561129267 14370367272159419341693901)
                  ·
                    refine ⟨5388887727059782253135213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14370367272159419341693901 5388887727059782253135213)
                    ·
                      refine ⟨2020832897647418344925705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5388887727059782253135213 2020832897647418344925705)
                      ·
                        rfl

theorem cell23_3935558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 1, 1, 1, 3, 3].length) (baseStart_3935558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3935558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3935558 prefixEnd_3935558 := by exact prefixLift 3935558
  have htrace : WordTrace (prefixWord ++ tailWord_3935558) baseStart_3935558 baseEnd_3935558 := by
    simpa [prefixWord, tailWord_3935558, baseEnd_3935558] using wordTrace_append hprefix tailTrace_3935558
  have hstable : (prefixWord ++ tailWord_3935558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3935558).length < 2 ^ (prefixWord ++ tailWord_3935558).sum := by decide
  have hdescent : baseEnd_3935558 < baseStart_3935558 := by decide
  rcases family_descends (prefixWord ++ tailWord_3935558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3935583 : List Nat := [1, 1, 2, 3, 1, 2, 1, 5, 2, 5]
def baseStart_3935583 : Nat := 118140960795 + 3935583 * 2 ^ 59
def prefixEnd_3935583 : Nat := 4983230072969 + 3 ^ 40 * 3935583 * 2
def baseEnd_3935583 : Nat := 673615244887926915704363

theorem tailTrace_3935583 : CollatzResearch.WordTrace tailWord_3935583 prefixEnd_3935583 673615244887926915704363 := by
  unfold tailWord_3935583
  simp only [CollatzResearch.WordTrace]
  refine ⟨143542504501062409909387403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95695003000708273272924935 143542504501062409909387403)
  ·
    refine ⟨215313756751593614864081105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143542504501062409909387403 215313756751593614864081105)
    ·
      refine ⟨161485317563695211148060829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215313756751593614864081105 161485317563695211148060829)
      ·
        refine ⟨60556994086385704180522811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 161485317563695211148060829 60556994086385704180522811)
        ·
          refine ⟨90835491129578556270784217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60556994086385704180522811 90835491129578556270784217)
          ·
            refine ⟨68126618347183917203088163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90835491129578556270784217 68126618347183917203088163)
            ·
              refine ⟨102189927520775875804632245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68126618347183917203088163 102189927520775875804632245)
              ·
                refine ⟨9580305705072738356684273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 102189927520775875804632245 9580305705072738356684273)
                ·
                  refine ⟨7185229278804553767513205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9580305705072738356684273 7185229278804553767513205)
                  ·
                    refine ⟨673615244887926915704363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7185229278804553767513205 673615244887926915704363)
                    ·
                      rfl

theorem cell23_3935583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 5, 2, 5].length) (baseStart_3935583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3935583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3935583 prefixEnd_3935583 := by exact prefixLift 3935583
  have htrace : WordTrace (prefixWord ++ tailWord_3935583) baseStart_3935583 baseEnd_3935583 := by
    simpa [prefixWord, tailWord_3935583, baseEnd_3935583] using wordTrace_append hprefix tailTrace_3935583
  have hstable : (prefixWord ++ tailWord_3935583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3935583).length < 2 ^ (prefixWord ++ tailWord_3935583).sum := by decide
  have hdescent : baseEnd_3935583 < baseStart_3935583 := by decide
  rcases family_descends (prefixWord ++ tailWord_3935583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3935587 : List Nat := [1, 1, 1, 5, 2, 4, 1, 3, 5]
def baseStart_3935587 : Nat := 118140960795 + 3935587 * 2 ^ 59
def prefixEnd_3935587 : Nat := 4983230072969 + 3 ^ 40 * 3935587 * 2
def baseEnd_3935587 : Nat := 224538643176266525718119

theorem tailTrace_3935587 : CollatzResearch.WordTrace tailWord_3935587 prefixEnd_3935587 224538643176266525718119 := by
  unfold tailWord_3935587
  simp only [CollatzResearch.WordTrace]
  refine ⟨143542650393047918592533015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95695100262031945728355343 143542650393047918592533015)
  ·
    refine ⟨215313975589571877888799523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143542650393047918592533015 215313975589571877888799523)
    ·
      refine ⟨322970963384357816833199285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215313975589571877888799523 322970963384357816833199285)
      ·
        refine ⟨30278527817283545328112433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 322970963384357816833199285 30278527817283545328112433)
        ·
          refine ⟨22708895862962658996084325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30278527817283545328112433 22708895862962658996084325)
          ·
            refine ⟨4257917974305498561765811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22708895862962658996084325 4257917974305498561765811)
            ·
              refine ⟨6386876961458247842648717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4257917974305498561765811 6386876961458247842648717)
              ·
                refine ⟨2395078860546842940993269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6386876961458247842648717 2395078860546842940993269)
                ·
                  refine ⟨224538643176266525718119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2395078860546842940993269 224538643176266525718119)
                  ·
                    rfl

theorem cell23_3935587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 1, 3, 5].length) (baseStart_3935587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3935587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3935587 prefixEnd_3935587 := by exact prefixLift 3935587
  have htrace : WordTrace (prefixWord ++ tailWord_3935587) baseStart_3935587 baseEnd_3935587 := by
    simpa [prefixWord, tailWord_3935587, baseEnd_3935587] using wordTrace_append hprefix tailTrace_3935587
  have hstable : (prefixWord ++ tailWord_3935587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3935587).length < 2 ^ (prefixWord ++ tailWord_3935587).sum := by decide
  have hdescent : baseEnd_3935587 < baseStart_3935587 := by decide
  rcases family_descends (prefixWord ++ tailWord_3935587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3935634 : List Nat := [3, 2, 3, 3, 1, 1, 2, 1, 2, 5]
def baseStart_3935634 : Nat := 118140960795 + 3935634 * 2 ^ 59
def prefixEnd_3935634 : Nat := 4983230072969 + 3 ^ 40 * 3935634 * 2
def baseEnd_3935634 : Nat := 673623974059053349191785

theorem tailTrace_3935634 : CollatzResearch.WordTrace tailWord_3935634 prefixEnd_3935634 673623974059053349191785 := by
  unfold tailWord_3935634
  simp only [CollatzResearch.WordTrace]
  refine ⟨35886091155969411404873489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95696243082585097079662637 35886091155969411404873489)
  ·
    refine ⟨26914568366977058553655117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35886091155969411404873489 26914568366977058553655117)
    ·
      refine ⟨10092963137616396957620669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26914568366977058553655117 10092963137616396957620669)
      ·
        refine ⟨3784861176606148859107751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10092963137616396957620669 3784861176606148859107751)
        ·
          refine ⟨5677291764909223288661627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3784861176606148859107751 5677291764909223288661627)
          ·
            refine ⟨8515937647363834932992441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5677291764909223288661627 8515937647363834932992441)
            ·
              refine ⟨6386953235522876199744331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8515937647363834932992441 6386953235522876199744331)
              ·
                refine ⟨9580429853284314299616497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6386953235522876199744331 9580429853284314299616497)
                ·
                  refine ⟨7185322389963235724712373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9580429853284314299616497 7185322389963235724712373)
                  ·
                    refine ⟨673623974059053349191785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7185322389963235724712373 673623974059053349191785)
                    ·
                      rfl

theorem cell23_3935634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 2, 1, 2, 5].length) (baseStart_3935634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3935634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3935634 prefixEnd_3935634 := by exact prefixLift 3935634
  have htrace : WordTrace (prefixWord ++ tailWord_3935634) baseStart_3935634 baseEnd_3935634 := by
    simpa [prefixWord, tailWord_3935634, baseEnd_3935634] using wordTrace_append hprefix tailTrace_3935634
  have hstable : (prefixWord ++ tailWord_3935634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3935634).length < 2 ^ (prefixWord ++ tailWord_3935634).sum := by decide
  have hdescent : baseEnd_3935634 < baseStart_3935634 := by decide
  rcases family_descends (prefixWord ++ tailWord_3935634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3935687 : List Nat := [1, 1, 4, 1, 1, 3, 3, 2, 3, 1, 3]
def baseStart_3935687 : Nat := 118140960795 + 3935687 * 2 ^ 59
def prefixEnd_3935687 : Nat := 4983230072969 + 3 ^ 40 * 3935687 * 2
def baseEnd_3935687 : Nat := 2020899136651848340212611

theorem tailTrace_3935687 : CollatzResearch.WordTrace tailWord_3935687 prefixEnd_3935687 2020899136651848340212611 := by
  unfold tailWord_3935687
  simp only [CollatzResearch.WordTrace]
  refine ⟨143546297692685635671173315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95697531795123757114115543 143546297692685635671173315)
  ·
    refine ⟨215319446539028453506759973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143546297692685635671173315 215319446539028453506759973)
    ·
      refine ⟨40372396226067835032517495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 215319446539028453506759973 40372396226067835032517495)
      ·
        refine ⟨60558594339101752548776243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40372396226067835032517495 60558594339101752548776243)
        ·
          refine ⟨90837891508652628823164365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60558594339101752548776243 90837891508652628823164365)
          ·
            refine ⟨34064209315744735808686637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90837891508652628823164365 34064209315744735808686637)
            ·
              refine ⟨12774078493404275928257489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34064209315744735808686637 12774078493404275928257489)
              ·
                refine ⟨9580558870053206946193117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12774078493404275928257489 9580558870053206946193117)
                ·
                  refine ⟨3592709576269952604822419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9580558870053206946193117 3592709576269952604822419)
                  ·
                    refine ⟨5389064364404928907233629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3592709576269952604822419 5389064364404928907233629)
                    ·
                      refine ⟨2020899136651848340212611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5389064364404928907233629 2020899136651848340212611)
                      ·
                        rfl

theorem cell23_3935687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3, 2, 3, 1, 3].length) (baseStart_3935687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3935687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3935687 prefixEnd_3935687 := by exact prefixLift 3935687
  have htrace : WordTrace (prefixWord ++ tailWord_3935687) baseStart_3935687 baseEnd_3935687 := by
    simpa [prefixWord, tailWord_3935687, baseEnd_3935687] using wordTrace_append hprefix tailTrace_3935687
  have hstable : (prefixWord ++ tailWord_3935687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3935687).length < 2 ^ (prefixWord ++ tailWord_3935687).sum := by decide
  have hdescent : baseEnd_3935687 < baseStart_3935687 := by decide
  rcases family_descends (prefixWord ++ tailWord_3935687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3935690 : List Nat := [3, 1, 2, 1, 2, 3, 2, 1, 3, 5]
def baseStart_3935690 : Nat := 118140960795 + 3935690 * 2 ^ 59
def prefixEnd_3935690 : Nat := 4983230072969 + 3 ^ 40 * 3935690 * 2
def baseEnd_3935690 : Nat := 673633559031270609491699

theorem tailTrace_3935690 : CollatzResearch.WordTrace tailWord_3935690 prefixEnd_3935690 673633559031270609491699 := by
  unfold tailWord_3935690
  simp only [CollatzResearch.WordTrace]
  refine ⟨35886601777918691795883131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95697604741116511455688349 35886601777918691795883131)
  ·
    refine ⟨53829902666878037693824697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35886601777918691795883131 53829902666878037693824697)
    ·
      refine ⟨40372427000158528270368523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53829902666878037693824697 40372427000158528270368523)
      ·
        refine ⟨60558640500237792405552785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40372427000158528270368523 60558640500237792405552785)
        ·
          refine ⟨45418980375178344304164589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60558640500237792405552785 45418980375178344304164589)
          ·
            refine ⟨17032117640691879114061721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45418980375178344304164589 17032117640691879114061721)
            ·
              refine ⟨12774088230518909335546291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17032117640691879114061721 12774088230518909335546291)
              ·
                refine ⟨19161132345778364003319437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12774088230518909335546291 19161132345778364003319437)
                ·
                  refine ⟨7185424629666886501244789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19161132345778364003319437 7185424629666886501244789)
                  ·
                    refine ⟨673633559031270609491699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7185424629666886501244789 673633559031270609491699)
                    ·
                      rfl

theorem cell23_3935690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2, 1, 3, 5].length) (baseStart_3935690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3935690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3935690 prefixEnd_3935690 := by exact prefixLift 3935690
  have htrace : WordTrace (prefixWord ++ tailWord_3935690) baseStart_3935690 baseEnd_3935690 := by
    simpa [prefixWord, tailWord_3935690, baseEnd_3935690] using wordTrace_append hprefix tailTrace_3935690
  have hstable : (prefixWord ++ tailWord_3935690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3935690).length < 2 ^ (prefixWord ++ tailWord_3935690).sum := by decide
  have hdescent : baseEnd_3935690 < baseStart_3935690 := by decide
  rcases family_descends (prefixWord ++ tailWord_3935690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3935704 : List Nat := [2, 1, 2, 2, 2, 1, 3, 5, 1, 1, 3]
def baseStart_3935704 : Nat := 118140960795 + 3935704 * 2 ^ 59
def prefixEnd_3935704 : Nat := 4983230072969 + 3 ^ 40 * 3935704 * 2
def baseEnd_3935704 : Nat := 2020907865822974773700033

theorem tailTrace_3935704 : CollatzResearch.WordTrace tailWord_3935704 prefixEnd_3935704 2020907865822974773700033 := by
  unfold tailWord_3935704
  simp only [CollatzResearch.WordTrace]
  refine ⟨71773458866812023787271083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95697945155749365049694777 71773458866812023787271083)
  ·
    refine ⟨107660188300218035680906625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71773458866812023787271083 107660188300218035680906625)
    ·
      refine ⟨80745141225163526760679969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107660188300218035680906625 80745141225163526760679969)
      ·
        refine ⟨60558855918872645070509977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80745141225163526760679969 60558855918872645070509977)
        ·
          refine ⟨45419141939154483802882483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60558855918872645070509977 45419141939154483802882483)
          ·
            refine ⟨68128712908731725704323725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45419141939154483802882483 68128712908731725704323725)
            ·
              refine ⟨25548267340774397139121397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68128712908731725704323725 25548267340774397139121397)
              ·
                refine ⟨2395150063197599731792631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25548267340774397139121397 2395150063197599731792631)
                ·
                  refine ⟨3592725094796399597688947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2395150063197599731792631 3592725094796399597688947)
                  ·
                    refine ⟨5389087642194599396533421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3592725094796399597688947 5389087642194599396533421)
                    ·
                      refine ⟨2020907865822974773700033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5389087642194599396533421 2020907865822974773700033)
                      ·
                        rfl

theorem cell23_3935704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 5, 1, 1, 3].length) (baseStart_3935704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3935704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3935704 prefixEnd_3935704 := by exact prefixLift 3935704
  have htrace : WordTrace (prefixWord ++ tailWord_3935704) baseStart_3935704 baseEnd_3935704 := by
    simpa [prefixWord, tailWord_3935704, baseEnd_3935704] using wordTrace_append hprefix tailTrace_3935704
  have hstable : (prefixWord ++ tailWord_3935704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3935704).length < 2 ^ (prefixWord ++ tailWord_3935704).sum := by decide
  have hdescent : baseEnd_3935704 < baseStart_3935704 := by decide
  rcases family_descends (prefixWord ++ tailWord_3935704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3935798 : List Nat := [5, 1, 2, 1, 3, 2, 1, 2, 1, 2, 3]
def baseStart_3935798 : Nat := 118140960795 + 3935798 * 2 ^ 59
def prefixEnd_3935798 : Nat := 4983230072969 + 3 ^ 40 * 3935798 * 2
def baseEnd_3935798 : Nat := 2020956133004497405924601

theorem tailTrace_3935798 : CollatzResearch.WordTrace tailWord_3935798 prefixEnd_3935798 2020956133004497405924601 := by
  unfold tailWord_3935798
  simp only [CollatzResearch.WordTrace]
  refine ⟨8971896637205218851779003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 95700230796855667752309365 8971896637205218851779003)
  ·
    refine ⟨13457844955807828277668505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8971896637205218851779003 13457844955807828277668505)
    ·
      refine ⟨10093383716855871208251379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13457844955807828277668505 10093383716855871208251379)
      ·
        refine ⟨15140075575283806812377069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10093383716855871208251379 15140075575283806812377069)
        ·
          refine ⟨5677528340731427554641401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15140075575283806812377069 5677528340731427554641401)
          ·
            refine ⟨4258146255548570665981051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5677528340731427554641401 4258146255548570665981051)
            ·
              refine ⟨6387219383322855998971577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4258146255548570665981051 6387219383322855998971577)
              ·
                refine ⟨4790414537492141999228683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6387219383322855998971577 4790414537492141999228683)
                ·
                  refine ⟨7185621806238212998843025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4790414537492141999228683 7185621806238212998843025)
                  ·
                    refine ⟨5389216354678659749132269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7185621806238212998843025 5389216354678659749132269)
                    ·
                      refine ⟨2020956133004497405924601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5389216354678659749132269 2020956133004497405924601)
                      ·
                        rfl

theorem cell23_3935798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 1, 2, 1, 2, 3].length) (baseStart_3935798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3935798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3935798 prefixEnd_3935798 := by exact prefixLift 3935798
  have htrace : WordTrace (prefixWord ++ tailWord_3935798) baseStart_3935798 baseEnd_3935798 := by
    simpa [prefixWord, tailWord_3935798, baseEnd_3935798] using wordTrace_append hprefix tailTrace_3935798
  have hstable : (prefixWord ++ tailWord_3935798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3935798).length < 2 ^ (prefixWord ++ tailWord_3935798).sum := by decide
  have hdescent : baseEnd_3935798 < baseStart_3935798 := by decide
  rcases family_descends (prefixWord ++ tailWord_3935798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3935834 : List Nat := [3, 1, 1, 2, 1, 1, 1, 5, 4, 2, 2]
def baseStart_3935834 : Nat := 118140960795 + 3935834 * 2 ^ 59
def prefixEnd_3935834 : Nat := 4983230072969 + 3 ^ 40 * 3935834 * 2
def baseEnd_3935834 : Nat := 2020974618308059265074435

theorem tailTrace_3935834 : CollatzResearch.WordTrace tailWord_3935834 prefixEnd_3935834 2020974618308059265074435 := by
  unfold tailWord_3935834
  simp only [CollatzResearch.WordTrace]
  refine ⟨35887914805788269944193639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95701106148768719851183037 35887914805788269944193639)
  ·
    refine ⟨53831872208682404916290459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35887914805788269944193639 53831872208682404916290459)
    ·
      refine ⟨80747808313023607374435689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53831872208682404916290459 80747808313023607374435689)
      ·
        refine ⟨60560856234767705530826767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80747808313023607374435689 60560856234767705530826767)
        ·
          refine ⟨90841284352151558296240151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60560856234767705530826767 90841284352151558296240151)
          ·
            refine ⟨136261926528227337444360227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90841284352151558296240151 136261926528227337444360227)
            ·
              refine ⟨204392889792341006166540341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136261926528227337444360227 204392889792341006166540341)
              ·
                refine ⟨19161833418031969328113157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 204392889792341006166540341 19161833418031969328113157)
                ·
                  refine ⟨3592843765880994249021217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19161833418031969328113157 3592843765880994249021217)
                  ·
                    refine ⟨2694632824410745686765913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3592843765880994249021217 2694632824410745686765913)
                    ·
                      refine ⟨2020974618308059265074435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2694632824410745686765913 2020974618308059265074435)
                      ·
                        rfl

theorem cell23_3935834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 5, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 5, 4, 2, 2].length) (baseStart_3935834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3935834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3935834 prefixEnd_3935834 := by exact prefixLift 3935834
  have htrace : WordTrace (prefixWord ++ tailWord_3935834) baseStart_3935834 baseEnd_3935834 := by
    simpa [prefixWord, tailWord_3935834, baseEnd_3935834] using wordTrace_append hprefix tailTrace_3935834
  have hstable : (prefixWord ++ tailWord_3935834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3935834).length < 2 ^ (prefixWord ++ tailWord_3935834).sum := by decide
  have hdescent : baseEnd_3935834 < baseStart_3935834 := by decide
  rcases family_descends (prefixWord ++ tailWord_3935834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3935840 : List Nat := [2, 1, 1, 3, 2, 1, 1, 5, 7]
def baseStart_3935840 : Nat := 118140960795 + 3935840 * 2 ^ 59
def prefixEnd_3935840 : Nat := 4983230072969 + 3 ^ 40 * 3935840 * 2
def baseEnd_3935840 : Nat := 224553077687998471288823

theorem tailTrace_3935840 : CollatzResearch.WordTrace tailWord_3935840 prefixEnd_3935840 224553077687998471288823 := by
  unfold tailWord_3935840
  simp only [CollatzResearch.WordTrace]
  refine ⟨71775939030565671400746487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95701252040754228534328649 71775939030565671400746487)
  ·
    refine ⟨107663908545848507101119731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71775939030565671400746487 107663908545848507101119731)
    ·
      refine ⟨161495862818772760651679597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107663908545848507101119731 161495862818772760651679597)
      ·
        refine ⟨60560948557039785244379849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 161495862818772760651679597 60560948557039785244379849)
        ·
          refine ⟨45420711417779838933284887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60560948557039785244379849 45420711417779838933284887)
          ·
            refine ⟨68131067126669758399927331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45420711417779838933284887 68131067126669758399927331)
            ·
              refine ⟨102196600690004637599890997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68131067126669758399927331 102196600690004637599890997)
              ·
                refine ⟨9580931314687934774989781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 102196600690004637599890997 9580931314687934774989781)
                ·
                  refine ⟨224553077687998471288823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9580931314687934774989781 224553077687998471288823)
                  ·
                    rfl

theorem cell23_3935840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 5, 7].length) (baseStart_3935840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3935840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3935840 prefixEnd_3935840 := by exact prefixLift 3935840
  have htrace : WordTrace (prefixWord ++ tailWord_3935840) baseStart_3935840 baseEnd_3935840 := by
    simpa [prefixWord, tailWord_3935840, baseEnd_3935840] using wordTrace_append hprefix tailTrace_3935840
  have hstable : (prefixWord ++ tailWord_3935840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3935840).length < 2 ^ (prefixWord ++ tailWord_3935840).sum := by decide
  have hdescent : baseEnd_3935840 < baseStart_3935840 := by decide
  rcases family_descends (prefixWord ++ tailWord_3935840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3935917 : List Nat := [1, 5, 2, 1, 1, 1, 1, 1, 2, 8]
def baseStart_3935917 : Nat := 118140960795 + 3935917 * 2 ^ 59
def prefixEnd_3935917 : Nat := 4983230072969 + 3 ^ 40 * 3935917 * 2
def baseEnd_3935917 : Nat := 673672412400794146778851

theorem tailTrace_3935917 : CollatzResearch.WordTrace tailWord_3935917 prefixEnd_3935917 673672412400794146778851 := by
  unfold tailWord_3935917
  simp only [CollatzResearch.WordTrace]
  refine ⟨143554686481852384952046005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95703124321234923301364003 143554686481852384952046005)
  ·
    refine ⟨13458251857673661089254313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 143554686481852384952046005 13458251857673661089254313)
    ·
      refine ⟨10093688893255245816940735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13458251857673661089254313 10093688893255245816940735)
      ·
        refine ⟨15140533339882868725411103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10093688893255245816940735 15140533339882868725411103)
        ·
          refine ⟨22710800009824303088116655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15140533339882868725411103 22710800009824303088116655)
          ·
            refine ⟨34066200014736454632174983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22710800009824303088116655 34066200014736454632174983)
            ·
              refine ⟨51099300022104681948262475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34066200014736454632174983 51099300022104681948262475)
              ·
                refine ⟨76648950033157022922393713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51099300022104681948262475 76648950033157022922393713)
                ·
                  refine ⟨57486712524867767191795285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76648950033157022922393713 57486712524867767191795285)
                  ·
                    refine ⟨673672412400794146778851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 57486712524867767191795285 673672412400794146778851)
                    ·
                      rfl

theorem cell23_3935917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 1, 2, 8].length) (baseStart_3935917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3935917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3935917 prefixEnd_3935917 := by exact prefixLift 3935917
  have htrace : WordTrace (prefixWord ++ tailWord_3935917) baseStart_3935917 baseEnd_3935917 := by
    simpa [prefixWord, tailWord_3935917, baseEnd_3935917] using wordTrace_append hprefix tailTrace_3935917
  have hstable : (prefixWord ++ tailWord_3935917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3935917).length < 2 ^ (prefixWord ++ tailWord_3935917).sum := by decide
  have hdescent : baseEnd_3935917 < baseStart_3935917 := by decide
  rcases family_descends (prefixWord ++ tailWord_3935917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3935944 : List Nat := [2, 1, 3, 1, 2, 2, 3, 2, 2, 2, 3]
def baseStart_3935944 : Nat := 118140960795 + 3935944 * 2 ^ 59
def prefixEnd_3935944 : Nat := 4983230072969 + 3 ^ 40 * 3935944 * 2
def baseEnd_3935944 : Nat := 2021031101180053834698929

theorem tailTrace_3935944 : CollatzResearch.WordTrace tailWord_3935944 prefixEnd_3935944 2021031101180053834698929 := by
  unfold tailWord_3935944
  simp only [CollatzResearch.WordTrace]
  refine ⟨71777835626377284281639443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95703780835169712375519257 71777835626377284281639443)
  ·
    refine ⟨107666753439565926422459165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71777835626377284281639443 107666753439565926422459165)
    ·
      refine ⟨40375032539837222408422187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107666753439565926422459165 40375032539837222408422187)
      ·
        refine ⟨60562548809755833612633281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40375032539837222408422187 60562548809755833612633281)
        ·
          refine ⟨45421911607316875209474961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60562548809755833612633281 45421911607316875209474961)
          ·
            refine ⟨34066433705487656407106221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45421911607316875209474961 34066433705487656407106221)
            ·
              refine ⟨12774912639557871152664833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34066433705487656407106221 12774912639557871152664833)
              ·
                refine ⟨9581184479668403364498625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12774912639557871152664833 9581184479668403364498625)
                ·
                  refine ⟨7185888359751302523373969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9581184479668403364498625 7185888359751302523373969)
                  ·
                    refine ⟨5389416269813476892530477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7185888359751302523373969 5389416269813476892530477)
                    ·
                      refine ⟨2021031101180053834698929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5389416269813476892530477 2021031101180053834698929)
                      ·
                        rfl

theorem cell23_3935944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3, 2, 2, 2, 3].length) (baseStart_3935944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3935944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3935944 prefixEnd_3935944 := by exact prefixLift 3935944
  have htrace : WordTrace (prefixWord ++ tailWord_3935944) baseStart_3935944 baseEnd_3935944 := by
    simpa [prefixWord, tailWord_3935944, baseEnd_3935944] using wordTrace_append hprefix tailTrace_3935944
  have hstable : (prefixWord ++ tailWord_3935944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3935944).length < 2 ^ (prefixWord ++ tailWord_3935944).sum := by decide
  have hdescent : baseEnd_3935944 < baseStart_3935944 := by decide
  rcases family_descends (prefixWord ++ tailWord_3935944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3936001 : List Nat := [1, 2, 4, 1, 1, 1, 4, 2, 2, 3, 2]
def baseStart_3936001 : Nat := 118140960795 + 3936001 * 2 ^ 59
def prefixEnd_3936001 : Nat := 4983230072969 + 3 ^ 40 * 3936001 * 2
def baseEnd_3936001 : Nat := 2021060369577360111686167

theorem tailTrace_3936001 : CollatzResearch.WordTrace tailWord_3936001 prefixEnd_3936001 2021060369577360111686167 := by
  unfold tailWord_3936001
  simp only [CollatzResearch.WordTrace]
  refine ⟨143557750213548067298103857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95705166809032044865402571 143557750213548067298103857)
  ·
    refine ⟨107668312660161050473577893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143557750213548067298103857 107668312660161050473577893)
    ·
      refine ⟨20187808623780196963795855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 107668312660161050473577893 20187808623780196963795855)
      ·
        refine ⟨30281712935670295445693783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20187808623780196963795855 30281712935670295445693783)
        ·
          refine ⟨45422569403505443168540675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30281712935670295445693783 45422569403505443168540675)
          ·
            refine ⟨68133854105258164752811013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45422569403505443168540675 68133854105258164752811013)
            ·
              refine ⟨12775097644735905891152065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68133854105258164752811013 12775097644735905891152065)
              ·
                refine ⟨9581323233551929418364049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12775097644735905891152065 9581323233551929418364049)
                ·
                  refine ⟨7185992425163947063773037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9581323233551929418364049 7185992425163947063773037)
                  ·
                    refine ⟨2694747159436480148914889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7185992425163947063773037 2694747159436480148914889)
                    ·
                      refine ⟨2021060369577360111686167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2694747159436480148914889 2021060369577360111686167)
                      ·
                        rfl

theorem cell23_3936001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 4, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 4, 2, 2, 3, 2].length) (baseStart_3936001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3936001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3936001 prefixEnd_3936001 := by exact prefixLift 3936001
  have htrace : WordTrace (prefixWord ++ tailWord_3936001) baseStart_3936001 baseEnd_3936001 := by
    simpa [prefixWord, tailWord_3936001, baseEnd_3936001] using wordTrace_append hprefix tailTrace_3936001
  have hstable : (prefixWord ++ tailWord_3936001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3936001).length < 2 ^ (prefixWord ++ tailWord_3936001).sum := by decide
  have hdescent : baseEnd_3936001 < baseStart_3936001 := by decide
  rcases family_descends (prefixWord ++ tailWord_3936001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3936008 : List Nat := [2, 1, 3, 2, 2, 1, 3, 4, 1, 1, 3]
def baseStart_3936008 : Nat := 118140960795 + 3936008 * 2 ^ 59
def prefixEnd_3936008 : Nat := 4983230072969 + 3 ^ 40 * 3936008 * 2
def baseEnd_3936008 : Nat := 2021063963941941584298635

theorem tailTrace_3936008 : CollatzResearch.WordTrace tailWord_3936008 prefixEnd_3936008 2021063963941941584298635 := by
  unfold tailWord_3936008
  simp only [CollatzResearch.WordTrace]
  refine ⟨71779002762261353746804339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95705337016348471662405785 71779002762261353746804339)
  ·
    refine ⟨107668504143392030620206509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71779002762261353746804339 107668504143392030620206509)
    ·
      refine ⟨40375689053772011482577441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107668504143392030620206509 40375689053772011482577441)
      ·
        refine ⟨30281766790329008611933081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40375689053772011482577441 30281766790329008611933081)
        ·
          refine ⟨22711325092746756458949811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30281766790329008611933081 22711325092746756458949811)
          ·
            refine ⟨34066987639120134688424717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22711325092746756458949811 34066987639120134688424717)
            ·
              refine ⟨12775120364670050508159269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34066987639120134688424717 12775120364670050508159269)
              ·
                refine ⟨2395335068375634470279863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12775120364670050508159269 2395335068375634470279863)
                ·
                  refine ⟨3593002602563451705419795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2395335068375634470279863 3593002602563451705419795)
                  ·
                    refine ⟨5389503903845177558129693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3593002602563451705419795 5389503903845177558129693)
                    ·
                      refine ⟨2021063963941941584298635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5389503903845177558129693 2021063963941941584298635)
                      ·
                        rfl

theorem cell23_3936008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 3, 4, 1, 1, 3].length) (baseStart_3936008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3936008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3936008 prefixEnd_3936008 := by exact prefixLift 3936008
  have htrace : WordTrace (prefixWord ++ tailWord_3936008) baseStart_3936008 baseEnd_3936008 := by
    simpa [prefixWord, tailWord_3936008, baseEnd_3936008] using wordTrace_append hprefix tailTrace_3936008
  have hstable : (prefixWord ++ tailWord_3936008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3936008).length < 2 ^ (prefixWord ++ tailWord_3936008).sum := by decide
  have hdescent : baseEnd_3936008 < baseStart_3936008 := by decide
  rcases family_descends (prefixWord ++ tailWord_3936008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3936014 : List Nat := [4, 1, 1, 2, 1, 1, 3, 2, 3, 1, 4]
def baseStart_3936014 : Nat := 118140960795 + 3936014 * 2 ^ 59
def prefixEnd_3936014 : Nat := 4983230072969 + 3 ^ 40 * 3936014 * 2
def baseEnd_3936014 : Nat := 2021067044825868560823607

theorem tailTrace_3936014 : CollatzResearch.WordTrace tailWord_3936014 prefixEnd_3936014 2021067044825868560823607 := by
  unfold tailWord_3936014
  simp only [CollatzResearch.WordTrace]
  refine ⟨17944778045312621314790887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95705482908333980345551397 17944778045312621314790887)
  ·
    refine ⟨26917167067968931972186331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17944778045312621314790887 26917167067968931972186331)
    ·
      refine ⟨40375750601953397958279497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26917167067968931972186331 40375750601953397958279497)
      ·
        refine ⟨30281812951465048468709623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40375750601953397958279497 30281812951465048468709623)
        ·
          refine ⟨45422719427197572703064435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30281812951465048468709623 45422719427197572703064435)
          ·
            refine ⟨68134079140796359054596653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45422719427197572703064435 68134079140796359054596653)
            ·
              refine ⟨25550279677798634645473745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68134079140796359054596653 25550279677798634645473745)
              ·
                refine ⟨19162709758348975984105309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25550279677798634645473745 19162709758348975984105309)
                ·
                  refine ⟨7186016159380865994039491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19162709758348975984105309 7186016159380865994039491)
                  ·
                    refine ⟨10779024239071298991059237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7186016159380865994039491 10779024239071298991059237)
                    ·
                      refine ⟨2021067044825868560823607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10779024239071298991059237 2021067044825868560823607)
                      ·
                        rfl

theorem cell23_3936014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 2, 3, 1, 4].length) (baseStart_3936014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3936014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3936014 prefixEnd_3936014 := by exact prefixLift 3936014
  have htrace : WordTrace (prefixWord ++ tailWord_3936014) baseStart_3936014 baseEnd_3936014 := by
    simpa [prefixWord, tailWord_3936014, baseEnd_3936014] using wordTrace_append hprefix tailTrace_3936014
  have hstable : (prefixWord ++ tailWord_3936014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3936014).length < 2 ^ (prefixWord ++ tailWord_3936014).sum := by decide
  have hdescent : baseEnd_3936014 < baseStart_3936014 := by decide
  rcases family_descends (prefixWord ++ tailWord_3936014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3936017 : List Nat := [1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 5]
def baseStart_3936017 : Nat := 118140960795 + 3936017 * 2 ^ 59
def prefixEnd_3936017 : Nat := 4983230072969 + 3 ^ 40 * 3936017 * 2
def baseEnd_3936017 : Nat := 2021068585267832049086093

theorem tailTrace_3936017 : CollatzResearch.WordTrace tailWord_3936017 prefixEnd_3936017 2021068585267832049086093 := by
  unfold tailWord_3936017
  simp only [CollatzResearch.WordTrace]
  refine ⟨143558333781490102030686305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95705555854326734687124203 143558333781490102030686305)
  ·
    refine ⟨107668750336117576523014729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143558333781490102030686305 107668750336117576523014729)
    ·
      refine ⟨80751562752088182392261047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107668750336117576523014729 80751562752088182392261047)
      ·
        refine ⟨121127344128132273588391571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80751562752088182392261047 121127344128132273588391571)
        ·
          refine ⟨181691016192198410382587357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121127344128132273588391571 181691016192198410382587357)
          ·
            refine ⟨68134131072074403893470259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 181691016192198410382587357 68134131072074403893470259)
            ·
              refine ⟨102201196608111605840205389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68134131072074403893470259 102201196608111605840205389)
              ·
                refine ⟨38325448728041852190077021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 102201196608111605840205389 38325448728041852190077021)
                ·
                  refine ⟨14372043273015694571278883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38325448728041852190077021 14372043273015694571278883)
                  ·
                    refine ⟨21558064909523541856918325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14372043273015694571278883 21558064909523541856918325)
                    ·
                      refine ⟨2021068585267832049086093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21558064909523541856918325 2021068585267832049086093)
                      ·
                        rfl

theorem cell23_3936017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 5].length) (baseStart_3936017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3936017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3936017 prefixEnd_3936017 := by exact prefixLift 3936017
  have htrace : WordTrace (prefixWord ++ tailWord_3936017) baseStart_3936017 baseEnd_3936017 := by
    simpa [prefixWord, tailWord_3936017, baseEnd_3936017] using wordTrace_append hprefix tailTrace_3936017
  have hstable : (prefixWord ++ tailWord_3936017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3936017).length < 2 ^ (prefixWord ++ tailWord_3936017).sum := by decide
  have hdescent : baseEnd_3936017 < baseStart_3936017 := by decide
  rcases family_descends (prefixWord ++ tailWord_3936017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3936027 : List Nat := [1, 1, 1, 1, 1, 1, 4, 2, 5, 2, 4]
def baseStart_3936027 : Nat := 118140960795 + 3936027 * 2 ^ 59
def prefixEnd_3936027 : Nat := 4983230072969 + 3 ^ 40 * 3936027 * 2
def baseEnd_3936027 : Nat := 2021073720074377009961047

theorem tailTrace_3936027 : CollatzResearch.WordTrace tailWord_3936027 prefixEnd_3936027 2021073720074377009961047 := by
  unfold tailWord_3936027
  simp only [CollatzResearch.WordTrace]
  refine ⟨143558698511453873738550335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95705799007635915825700223 143558698511453873738550335)
  ·
    refine ⟨215338047767180810607825503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143558698511453873738550335 215338047767180810607825503)
    ·
      refine ⟨323007071650771215911738255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215338047767180810607825503 323007071650771215911738255)
      ·
        refine ⟨484510607476156823867607383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 323007071650771215911738255 484510607476156823867607383)
        ·
          refine ⟨726765911214235235801411075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 484510607476156823867607383 726765911214235235801411075)
          ·
            refine ⟨1090148866821352853702116613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 726765911214235235801411075 1090148866821352853702116613)
            ·
              refine ⟨204402912529003660069146865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1090148866821352853702116613 204402912529003660069146865)
              ·
                refine ⟨153302184396752745051860149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 204402912529003660069146865 153302184396752745051860149)
                ·
                  refine ⟨14372079787195569848611889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 153302184396752745051860149 14372079787195569848611889)
                  ·
                    refine ⟨10779059840396677386458917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14372079787195569848611889 10779059840396677386458917)
                    ·
                      refine ⟨2021073720074377009961047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10779059840396677386458917 2021073720074377009961047)
                      ·
                        rfl

theorem cell23_3936027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2, 5, 2, 4].length) (baseStart_3936027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3936027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3936027 prefixEnd_3936027 := by exact prefixLift 3936027
  have htrace : WordTrace (prefixWord ++ tailWord_3936027) baseStart_3936027 baseEnd_3936027 := by
    simpa [prefixWord, tailWord_3936027, baseEnd_3936027] using wordTrace_append hprefix tailTrace_3936027
  have hstable : (prefixWord ++ tailWord_3936027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3936027).length < 2 ^ (prefixWord ++ tailWord_3936027).sum := by decide
  have hdescent : baseEnd_3936027 < baseStart_3936027 := by decide
  rcases family_descends (prefixWord ++ tailWord_3936027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3936044 : List Nat := [2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 4]
def baseStart_3936044 : Nat := 118140960795 + 3936044 * 2 ^ 59
def prefixEnd_3936044 : Nat := 4983230072969 + 3 ^ 40 * 3936044 * 2
def baseEnd_3936044 : Nat := 2021082449245503443448469

theorem tailTrace_3936044 : CollatzResearch.WordTrace tailWord_3936044 prefixEnd_3936044 2021082449245503443448469 := by
  unfold tailWord_3936044
  simp only [CollatzResearch.WordTrace]
  refine ⟨71779659276196142820959593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95706212368261523761279457 71779659276196142820959593)
  ·
    refine ⟨53834744457147107115719695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71779659276196142820959593 53834744457147107115719695)
    ·
      refine ⟨80752116685720660673579543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53834744457147107115719695 80752116685720660673579543)
      ·
        refine ⟨121128175028580991010369315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80752116685720660673579543 121128175028580991010369315)
        ·
          refine ⟨181692262542871486515553973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121128175028580991010369315 181692262542871486515553973)
          ·
            refine ⟨17033649613394201860833185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 181692262542871486515553973 17033649613394201860833185)
            ·
              refine ⟨12775237210045651395624889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17033649613394201860833185 12775237210045651395624889)
              ·
                refine ⟨9581427907534238546718667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12775237210045651395624889 9581427907534238546718667)
                ·
                  refine ⟨14372141861301357820078001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9581427907534238546718667 14372141861301357820078001)
                  ·
                    refine ⟨10779106395976018365058501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14372141861301357820078001 10779106395976018365058501)
                    ·
                      refine ⟨2021082449245503443448469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10779106395976018365058501 2021082449245503443448469)
                      ·
                        rfl

theorem cell23_3936044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 4].length) (baseStart_3936044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3936044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3936044 prefixEnd_3936044 := by exact prefixLift 3936044
  have htrace : WordTrace (prefixWord ++ tailWord_3936044) baseStart_3936044 baseEnd_3936044 := by
    simpa [prefixWord, tailWord_3936044, baseEnd_3936044] using wordTrace_append hprefix tailTrace_3936044
  have hstable : (prefixWord ++ tailWord_3936044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3936044).length < 2 ^ (prefixWord ++ tailWord_3936044).sum := by decide
  have hdescent : baseEnd_3936044 < baseStart_3936044 := by decide
  rcases family_descends (prefixWord ++ tailWord_3936044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3936058 : List Nat := [3, 1, 1, 1, 5, 3, 1, 2, 2, 4]
def baseStart_3936058 : Nat := 118140960795 + 3936058 * 2 ^ 59
def prefixEnd_3936058 : Nat := 4983230072969 + 3 ^ 40 * 3936058 * 2
def baseEnd_3936058 : Nat := 673696545991555462891135

theorem tailTrace_3936058 : CollatzResearch.WordTrace tailWord_3936058 prefixEnd_3936058 673696545991555462891135 := by
  unfold tailWord_3936058
  simp only [CollatzResearch.WordTrace]
  refine ⟨35889957293585391508232207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95706552782894377355285885 35889957293585391508232207)
  ·
    refine ⟨53834935940378087262348311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35889957293585391508232207 53834935940378087262348311)
    ·
      refine ⟨80752403910567130893522467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53834935940378087262348311 80752403910567130893522467)
      ·
        refine ⟨121128605865850696340283701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80752403910567130893522467 121128605865850696340283701)
        ·
          refine ⟨11355806799923502781901597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 121128605865850696340283701 11355806799923502781901597)
          ·
            refine ⟨4258427549971313543213099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11355806799923502781901597 4258427549971313543213099)
            ·
              refine ⟨6387641324956970314819649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4258427549971313543213099 6387641324956970314819649)
              ·
                refine ⟨4790730993717727736114737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6387641324956970314819649 4790730993717727736114737)
                ·
                  refine ⟨3593048245288295802086053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4790730993717727736114737 3593048245288295802086053)
                  ·
                    refine ⟨673696545991555462891135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3593048245288295802086053 673696545991555462891135)
                    ·
                      rfl

theorem cell23_3936058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 1, 2, 2, 4].length) (baseStart_3936058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3936058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3936058 prefixEnd_3936058 := by exact prefixLift 3936058
  have htrace : WordTrace (prefixWord ++ tailWord_3936058) baseStart_3936058 baseEnd_3936058 := by
    simpa [prefixWord, tailWord_3936058, baseEnd_3936058] using wordTrace_append hprefix tailTrace_3936058
  have hstable : (prefixWord ++ tailWord_3936058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3936058).length < 2 ^ (prefixWord ++ tailWord_3936058).sum := by decide
  have hdescent : baseEnd_3936058 < baseStart_3936058 := by decide
  rcases family_descends (prefixWord ++ tailWord_3936058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3936081 : List Nat := [1, 2, 2, 1, 5, 1, 3, 1, 1, 3, 3]
def baseStart_3936081 : Nat := 118140960795 + 3936081 * 2 ^ 59
def prefixEnd_3936081 : Nat := 4983230072969 + 3 ^ 40 * 3936081 * 2
def baseEnd_3936081 : Nat := 2021101448029719798685799

theorem tailTrace_3936081 : CollatzResearch.WordTrace tailWord_3936081 prefixEnd_3936081 2021101448029719798685799 := by
  unfold tailWord_3936081
  simp only [CollatzResearch.WordTrace]
  refine ⟨143560668053258240961016097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95707112035505493974010731 143560668053258240961016097)
  ·
    refine ⟨107670501039943680720762073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143560668053258240961016097 107670501039943680720762073)
    ·
      refine ⟨80752875779957760540571555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107670501039943680720762073 80752875779957760540571555)
      ·
        refine ⟨121129313669936640810857333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80752875779957760540571555 121129313669936640810857333)
        ·
          refine ⟨11355873156556560076017875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 121129313669936640810857333 11355873156556560076017875)
          ·
            refine ⟨17033809734834840114026813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11355873156556560076017875 17033809734834840114026813)
            ·
              refine ⟨6387678650563065042760055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17033809734834840114026813 6387678650563065042760055)
              ·
                refine ⟨9581517975844597564140083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6387678650563065042760055 9581517975844597564140083)
                ·
                  refine ⟨14372276963766896346210125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9581517975844597564140083 14372276963766896346210125)
                  ·
                    refine ⟨5389603861412586129828797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14372276963766896346210125 5389603861412586129828797)
                    ·
                      refine ⟨2021101448029719798685799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5389603861412586129828797 2021101448029719798685799)
                      ·
                        rfl

theorem cell23_3936081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 3, 1, 1, 3, 3].length) (baseStart_3936081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3936081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3936081 prefixEnd_3936081 := by exact prefixLift 3936081
  have htrace : WordTrace (prefixWord ++ tailWord_3936081) baseStart_3936081 baseEnd_3936081 := by
    simpa [prefixWord, tailWord_3936081, baseEnd_3936081] using wordTrace_append hprefix tailTrace_3936081
  have hstable : (prefixWord ++ tailWord_3936081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3936081).length < 2 ^ (prefixWord ++ tailWord_3936081).sum := by decide
  have hdescent : baseEnd_3936081 < baseStart_3936081 := by decide
  rcases family_descends (prefixWord ++ tailWord_3936081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3936098 : List Nat := [3, 3, 2, 1, 2, 1, 1, 2, 4, 1, 3]
def baseStart_3936098 : Nat := 118140960795 + 3936098 * 2 ^ 59
def prefixEnd_3936098 : Nat := 4983230072969 + 3 ^ 40 * 3936098 * 2
def baseEnd_3936098 : Nat := 2021110177200846232173221

theorem tailTrace_3936098 : CollatzResearch.WordTrace tailWord_3936098 prefixEnd_3936098 2021110177200846232173221 := by
  unfold tailWord_3936098
  simp only [CollatzResearch.WordTrace]
  refine ⟨35890322023549163216096237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95707525396131101909589965 35890322023549163216096237)
  ·
    refine ⟨13458870758830936206036089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35890322023549163216096237 13458870758830936206036089)
    ·
      refine ⟨10094153069123202154527067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13458870758830936206036089 10094153069123202154527067)
      ·
        refine ⟨15141229603684803231790601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10094153069123202154527067 15141229603684803231790601)
        ·
          refine ⟨11355922202763602423842951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15141229603684803231790601 11355922202763602423842951)
          ·
            refine ⟨17033883304145403635764427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11355922202763602423842951 17033883304145403635764427)
            ·
              refine ⟨25550824956218105453646641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17033883304145403635764427 25550824956218105453646641)
              ·
                refine ⟨19163118717163579090234981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25550824956218105453646641 19163118717163579090234981)
                ·
                  refine ⟨3593084759468171079419059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19163118717163579090234981 3593084759468171079419059)
                  ·
                    refine ⟨5389627139202256619128589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3593084759468171079419059 5389627139202256619128589)
                    ·
                      refine ⟨2021110177200846232173221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5389627139202256619128589 2021110177200846232173221)
                      ·
                        rfl

theorem cell23_3936098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 2, 4, 1, 3].length) (baseStart_3936098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3936098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3936098 prefixEnd_3936098 := by exact prefixLift 3936098
  have htrace : WordTrace (prefixWord ++ tailWord_3936098) baseStart_3936098 baseEnd_3936098 := by
    simpa [prefixWord, tailWord_3936098, baseEnd_3936098] using wordTrace_append hprefix tailTrace_3936098
  have hstable : (prefixWord ++ tailWord_3936098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3936098).length < 2 ^ (prefixWord ++ tailWord_3936098).sum := by decide
  have hdescent : baseEnd_3936098 < baseStart_3936098 := by decide
  rcases family_descends (prefixWord ++ tailWord_3936098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3936099 : List Nat := [1, 1, 1, 5, 5, 1, 1, 3, 1, 2, 2]
def baseStart_3936099 : Nat := 118140960795 + 3936099 * 2 ^ 59
def prefixEnd_3936099 : Nat := 4983230072969 + 3 ^ 40 * 3936099 * 2
def baseEnd_3936099 : Nat := 2021110690681500728260717

theorem tailTrace_3936099 : CollatzResearch.WordTrace tailWord_3936099 prefixEnd_3936099 2021110690681500728260717 := by
  unfold tailWord_3936099
  simp only [CollatzResearch.WordTrace]
  refine ⟨143561324567193030035171351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95707549711462020023447567 143561324567193030035171351)
  ·
    refine ⟨215341986850789545052757027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143561324567193030035171351 215341986850789545052757027)
    ·
      refine ⟨323012980276184317579135541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215341986850789545052757027 323012980276184317579135541)
      ·
        refine ⟨30282466900892279773043957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 323012980276184317579135541 30282466900892279773043957)
        ·
          refine ⟨2838981271958651228722871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30282466900892279773043957 2838981271958651228722871)
          ·
            refine ⟨4258471907937976843084307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2838981271958651228722871 4258471907937976843084307)
            ·
              refine ⟨6387707861906965264626461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4258471907937976843084307 6387707861906965264626461)
              ·
                refine ⟨2395390448215111974234923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6387707861906965264626461 2395390448215111974234923)
                ·
                  refine ⟨3593085672322667961352385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2395390448215111974234923 3593085672322667961352385)
                  ·
                    refine ⟨2694814254242000971014289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3593085672322667961352385 2694814254242000971014289)
                    ·
                      refine ⟨2021110690681500728260717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2694814254242000971014289 2021110690681500728260717)
                      ·
                        rfl

theorem cell23_3936099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 1, 3, 1, 2, 2].length) (baseStart_3936099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3936099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3936099 prefixEnd_3936099 := by exact prefixLift 3936099
  have htrace : WordTrace (prefixWord ++ tailWord_3936099) baseStart_3936099 baseEnd_3936099 := by
    simpa [prefixWord, tailWord_3936099, baseEnd_3936099] using wordTrace_append hprefix tailTrace_3936099
  have hstable : (prefixWord ++ tailWord_3936099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3936099).length < 2 ^ (prefixWord ++ tailWord_3936099).sum := by decide
  have hdescent : baseEnd_3936099 < baseStart_3936099 := by decide
  rcases family_descends (prefixWord ++ tailWord_3936099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3936108 : List Nat := [2, 2, 1, 1, 4, 2, 2, 3, 1, 3, 2]
def baseStart_3936108 : Nat := 118140960795 + 3936108 * 2 ^ 59
def prefixEnd_3936108 : Nat := 4983230072969 + 3 ^ 40 * 3936108 * 2
def baseEnd_3936108 : Nat := 2021115312007391193048175

theorem tailTrace_3936108 : CollatzResearch.WordTrace tailWord_3936108 prefixEnd_3936108 2021115312007391193048175 := by
  unfold tailWord_3936108
  simp only [CollatzResearch.WordTrace]
  refine ⟨71780826412080212286124489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95707768549440283048165985 71780826412080212286124489)
  ·
    refine ⟨53835619809060159214593367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71780826412080212286124489 53835619809060159214593367)
    ·
      refine ⟨80753429713590238821890051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53835619809060159214593367 80753429713590238821890051)
      ·
        refine ⟨121130144570385358232835077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80753429713590238821890051 121130144570385358232835077)
        ·
          refine ⟨22711902106947254668656577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 121130144570385358232835077 22711902106947254668656577)
          ·
            refine ⟨17033926580210441001492433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22711902106947254668656577 17033926580210441001492433)
            ·
              refine ⟨12775444935157830751119325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17033926580210441001492433 12775444935157830751119325)
              ·
                refine ⟨4790791850684186531669747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12775444935157830751119325 4790791850684186531669747)
                ·
                  refine ⟨7186187776026279797504621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4790791850684186531669747 7186187776026279797504621)
                  ·
                    refine ⟨2694820416009854924064233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7186187776026279797504621 2694820416009854924064233)
                    ·
                      refine ⟨2021115312007391193048175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2694820416009854924064233 2021115312007391193048175)
                      ·
                        rfl

theorem cell23_3936108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 3, 2].length) (baseStart_3936108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3936108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3936108 prefixEnd_3936108 := by exact prefixLift 3936108
  have htrace : WordTrace (prefixWord ++ tailWord_3936108) baseStart_3936108 baseEnd_3936108 := by
    simpa [prefixWord, tailWord_3936108, baseEnd_3936108] using wordTrace_append hprefix tailTrace_3936108
  have hstable : (prefixWord ++ tailWord_3936108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3936108).length < 2 ^ (prefixWord ++ tailWord_3936108).sum := by decide
  have hdescent : baseEnd_3936108 < baseStart_3936108 := by decide
  rcases family_descends (prefixWord ++ tailWord_3936108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3936184 : List Nat := [2, 1, 2, 1, 2, 3, 1, 3, 1, 2, 5]
def baseStart_3936184 : Nat := 118140960795 + 3936184 * 2 ^ 59
def prefixEnd_3936184 : Nat := 4983230072969 + 3 ^ 40 * 3936184 * 2
def baseEnd_3936184 : Nat := 2021154336537132895697825

theorem tailTrace_3936184 : CollatzResearch.WordTrace tailWord_3936184 prefixEnd_3936184 2021154336537132895697825 := by
  unfold tailWord_3936184
  simp only [CollatzResearch.WordTrace]
  refine ⟨71782212385942544776007803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95709616514590059701343737 71782212385942544776007803)
  ·
    refine ⟨107673318578913817164011705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71782212385942544776007803 107673318578913817164011705)
    ·
      refine ⟨80754988934185362873008779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107673318578913817164011705 80754988934185362873008779)
      ·
        refine ⟨121132483401278044309513169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80754988934185362873008779 121132483401278044309513169)
        ·
          refine ⟨90849362550958533232134877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121132483401278044309513169 90849362550958533232134877)
          ·
            refine ⟨34068510956609449962050579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90849362550958533232134877 34068510956609449962050579)
            ·
              refine ⟨51102766434914174943075869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34068510956609449962050579 51102766434914174943075869)
              ·
                refine ⟨19163537413092815603653451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51102766434914174943075869 19163537413092815603653451)
                ·
                  refine ⟨28745306119639223405480177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19163537413092815603653451 28745306119639223405480177)
                  ·
                    refine ⟨21558979589729417554110133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28745306119639223405480177 21558979589729417554110133)
                    ·
                      refine ⟨2021154336537132895697825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21558979589729417554110133 2021154336537132895697825)
                      ·
                        rfl

theorem cell23_3936184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 3, 1, 2, 5].length) (baseStart_3936184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3936184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3936184 prefixEnd_3936184 := by exact prefixLift 3936184
  have htrace : WordTrace (prefixWord ++ tailWord_3936184) baseStart_3936184 baseEnd_3936184 := by
    simpa [prefixWord, tailWord_3936184, baseEnd_3936184] using wordTrace_append hprefix tailTrace_3936184
  have hstable : (prefixWord ++ tailWord_3936184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3936184).length < 2 ^ (prefixWord ++ tailWord_3936184).sum := by decide
  have hdescent : baseEnd_3936184 < baseStart_3936184 := by decide
  rcases family_descends (prefixWord ++ tailWord_3936184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3936224 : List Nat := [2, 1, 1, 3, 1, 1, 1, 2, 1, 6, 4]
def baseStart_3936224 : Nat := 118140960795 + 3936224 * 2 ^ 59
def prefixEnd_3936224 : Nat := 4983230072969 + 3 ^ 40 * 3936224 * 2
def baseEnd_3936224 : Nat := 2021174875763312739197641

theorem tailTrace_3936224 : CollatzResearch.WordTrace tailWord_3936224 prefixEnd_3936224 2021174875763312739197641 := by
  unfold tailWord_3936224
  simp only [CollatzResearch.WordTrace]
  refine ⟨71782941845870088191735863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95710589127826784255647817 71782941845870088191735863)
  ·
    refine ⟨107674412768805132287603795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71782941845870088191735863 107674412768805132287603795)
    ·
      refine ⟨161511619153207698431405693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107674412768805132287603795 161511619153207698431405693)
      ·
        refine ⟨60566857182452886911777135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 161511619153207698431405693 60566857182452886911777135)
        ·
          refine ⟨90850285773679330367665703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60566857182452886911777135 90850285773679330367665703)
          ·
            refine ⟨136275428660518995551498555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90850285773679330367665703 136275428660518995551498555)
            ·
              refine ⟨204413142990778493327247833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136275428660518995551498555 204413142990778493327247833)
              ·
                refine ⟨153309857243083869995435875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 204413142990778493327247833 153309857243083869995435875)
                ·
                  refine ⟨229964785864625804993153813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 153309857243083869995435875 229964785864625804993153813)
                  ·
                    refine ⟨10779599337404334609054085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 229964785864625804993153813 10779599337404334609054085)
                    ·
                      refine ⟨2021174875763312739197641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10779599337404334609054085 2021174875763312739197641)
                      ·
                        rfl

theorem cell23_3936224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 1, 6, 4].length) (baseStart_3936224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3936224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3936224 prefixEnd_3936224 := by exact prefixLift 3936224
  have htrace : WordTrace (prefixWord ++ tailWord_3936224) baseStart_3936224 baseEnd_3936224 := by
    simpa [prefixWord, tailWord_3936224, baseEnd_3936224] using wordTrace_append hprefix tailTrace_3936224
  have hstable : (prefixWord ++ tailWord_3936224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3936224).length < 2 ^ (prefixWord ++ tailWord_3936224).sum := by decide
  have hdescent : baseEnd_3936224 < baseStart_3936224 := by decide
  rcases family_descends (prefixWord ++ tailWord_3936224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3936238 : List Nat := [4, 1, 2, 1, 3, 1, 1, 3, 3, 4]
def baseStart_3936238 : Nat := 118140960795 + 3936238 * 2 ^ 59
def prefixEnd_3936238 : Nat := 4983230072969 + 3 ^ 40 * 3936238 * 2
def baseEnd_3936238 : Nat := 673727354830825228140859

theorem tailTrace_3936238 : CollatzResearch.WordTrace tailWord_3936238 prefixEnd_3936238 673727354830825228140859 := by
  unfold tailWord_3936238
  simp only [CollatzResearch.WordTrace]
  refine ⟨17945799289211182096810171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95710929542459637849654245 17945799289211182096810171)
  ·
    refine ⟨26918698933816773145215257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17945799289211182096810171 26918698933816773145215257)
    ·
      refine ⟨20189024200362579858911443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26918698933816773145215257 20189024200362579858911443)
      ·
        refine ⟨30283536300543869788367165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20189024200362579858911443 30283536300543869788367165)
        ·
          refine ⟨11356326112703951170637687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30283536300543869788367165 11356326112703951170637687)
          ·
            refine ⟨17034489169055926755956531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11356326112703951170637687 17034489169055926755956531)
            ·
              refine ⟨25551733753583890133934797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17034489169055926755956531 25551733753583890133934797)
              ·
                refine ⟨9581900157593958800225549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25551733753583890133934797 9581900157593958800225549)
                ·
                  refine ⟨3593212559097734550084581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9581900157593958800225549 3593212559097734550084581)
                  ·
                    refine ⟨673727354830825228140859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3593212559097734550084581 673727354830825228140859)
                    ·
                      rfl

theorem cell23_3936238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 3, 3, 4].length) (baseStart_3936238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3936238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3936238 prefixEnd_3936238 := by exact prefixLift 3936238
  have htrace : WordTrace (prefixWord ++ tailWord_3936238) baseStart_3936238 baseEnd_3936238 := by
    simpa [prefixWord, tailWord_3936238, baseEnd_3936238] using wordTrace_append hprefix tailTrace_3936238
  have hstable : (prefixWord ++ tailWord_3936238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3936238).length < 2 ^ (prefixWord ++ tailWord_3936238).sum := by decide
  have hdescent : baseEnd_3936238 < baseStart_3936238 := by decide
  rcases family_descends (prefixWord ++ tailWord_3936238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3936331 : List Nat := [1, 1, 1, 1, 3, 1, 2, 6, 1, 2, 4]
def baseStart_3936331 : Nat := 118140960795 + 3936331 * 2 ^ 59
def prefixEnd_3936331 : Nat := 4983230072969 + 3 ^ 40 * 3936331 * 2
def baseEnd_3936331 : Nat := 2021229818193343820559649

theorem tailTrace_3936331 : CollatzResearch.WordTrace tailWord_3936331 prefixEnd_3936331 2021229818193343820559649 := by
  unfold tailWord_3936331
  simp only [CollatzResearch.WordTrace]
  refine ⟨143569786302352533657616847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95713190868235022438411231 143569786302352533657616847)
  ·
    refine ⟨215354679453528800486425271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143569786302352533657616847 215354679453528800486425271)
    ·
      refine ⟨323032019180293200729637907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215354679453528800486425271 323032019180293200729637907)
      ·
        refine ⟨484548028770439801094456861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 323032019180293200729637907 484548028770439801094456861)
        ·
          refine ⟨181705510788914925410421323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 484548028770439801094456861 181705510788914925410421323)
          ·
            refine ⟨272558266183372388115631985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181705510788914925410421323 272558266183372388115631985)
            ·
              refine ⟨204418699637529291086723989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 272558266183372388115631985 204418699637529291086723989)
              ·
                refine ⟨9582126545509185519690187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 204418699637529291086723989 9582126545509185519690187)
                ·
                  refine ⟨14373189818263778279535281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9582126545509185519690187 14373189818263778279535281)
                  ·
                    refine ⟨10779892363697833709651461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14373189818263778279535281 10779892363697833709651461)
                    ·
                      refine ⟨2021229818193343820559649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10779892363697833709651461 2021229818193343820559649)
                      ·
                        rfl

theorem cell23_3936331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 6, 1, 2, 4].length) (baseStart_3936331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3936331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3936331 prefixEnd_3936331 := by exact prefixLift 3936331
  have htrace : WordTrace (prefixWord ++ tailWord_3936331) baseStart_3936331 baseEnd_3936331 := by
    simpa [prefixWord, tailWord_3936331, baseEnd_3936331] using wordTrace_append hprefix tailTrace_3936331
  have hstable : (prefixWord ++ tailWord_3936331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3936331).length < 2 ^ (prefixWord ++ tailWord_3936331).sum := by decide
  have hdescent : baseEnd_3936331 < baseStart_3936331 := by decide
  rcases family_descends (prefixWord ++ tailWord_3936331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3936368 : List Nat := [2, 1, 1, 1, 5, 2, 1, 3, 1, 3, 3]
def baseStart_3936368 : Nat := 118140960795 + 3936368 * 2 ^ 59
def prefixEnd_3936368 : Nat := 4983230072969 + 3 ^ 40 * 3936368 * 2
def baseEnd_3936368 : Nat := 2021248816977560175796979

theorem tailTrace_3936368 : CollatzResearch.WordTrace tailWord_3936368 prefixEnd_3936368 2021248816977560175796979 := by
  unfold tailWord_3936368
  simp only [CollatzResearch.WordTrace]
  refine ⟨71785567901609244488356879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95714090535478992651142505 71785567901609244488356879)
  ·
    refine ⟨107678351852413866732535319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71785567901609244488356879 107678351852413866732535319)
    ·
      refine ⟨161517527778620800098802979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107678351852413866732535319 161517527778620800098802979)
      ·
        refine ⟨242276291667931200148204469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161517527778620800098802979 242276291667931200148204469)
        ·
          refine ⟨22713402343868550013894169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 242276291667931200148204469 22713402343868550013894169)
          ·
            refine ⟨17035051757901412510420627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22713402343868550013894169 17035051757901412510420627)
            ·
              refine ⟨25552577636852118765630941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17035051757901412510420627 25552577636852118765630941)
              ·
                refine ⟨9582216613819544537111603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25552577636852118765630941 9582216613819544537111603)
                ·
                  refine ⟨14373324920729316805667405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9582216613819544537111603 14373324920729316805667405)
                  ·
                    refine ⟨5389996845273493802125277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14373324920729316805667405 5389996845273493802125277)
                    ·
                      refine ⟨2021248816977560175796979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5389996845273493802125277 2021248816977560175796979)
                      ·
                        rfl

theorem cell23_3936368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 3, 1, 3, 3].length) (baseStart_3936368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3936368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3936368 prefixEnd_3936368 := by exact prefixLift 3936368
  have htrace : WordTrace (prefixWord ++ tailWord_3936368) baseStart_3936368 baseEnd_3936368 := by
    simpa [prefixWord, tailWord_3936368, baseEnd_3936368] using wordTrace_append hprefix tailTrace_3936368
  have hstable : (prefixWord ++ tailWord_3936368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3936368).length < 2 ^ (prefixWord ++ tailWord_3936368).sum := by decide
  have hdescent : baseEnd_3936368 < baseStart_3936368 := by decide
  rcases family_descends (prefixWord ++ tailWord_3936368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3936406 : List Nat := [5, 3, 2, 1, 1, 1, 1, 2, 1, 1, 5]
def baseStart_3936406 : Nat := 118140960795 + 3936406 * 2 ^ 59
def prefixEnd_3936406 : Nat := 4983230072969 + 3 ^ 40 * 3936406 * 2
def baseEnd_3936406 : Nat := 2021268329242431027121805

theorem tailTrace_3936406 : CollatzResearch.WordTrace tailWord_3936406 prefixEnd_3936406 2021268329242431027121805 := by
  unfold tailWord_3936406
  simp only [CollatzResearch.WordTrace]
  refine ⟨8973282611067551341662317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 95715014518053880977731381 8973282611067551341662317)
  ·
    refine ⟨3364980979150331753123369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8973282611067551341662317 3364980979150331753123369)
    ·
      refine ⟨2523735734362748814842527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3364980979150331753123369 2523735734362748814842527)
      ·
        refine ⟨3785603601544123222263791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2523735734362748814842527 3785603601544123222263791)
        ·
          refine ⟨5678405402316184833395687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3785603601544123222263791 5678405402316184833395687)
          ·
            refine ⟨8517608103474277250093531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5678405402316184833395687 8517608103474277250093531)
            ·
              refine ⟨12776412155211415875140297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8517608103474277250093531 12776412155211415875140297)
              ·
                refine ⟨9582309116408561906355223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12776412155211415875140297 9582309116408561906355223)
                ·
                  refine ⟨14373463674612842859532835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9582309116408561906355223 14373463674612842859532835)
                  ·
                    refine ⟨21560195511919264289299253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14373463674612842859532835 21560195511919264289299253)
                    ·
                      refine ⟨2021268329242431027121805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21560195511919264289299253 2021268329242431027121805)
                      ·
                        rfl

theorem cell23_3936406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 1, 2, 1, 1, 5].length) (baseStart_3936406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3936406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3936406 prefixEnd_3936406 := by exact prefixLift 3936406
  have htrace : WordTrace (prefixWord ++ tailWord_3936406) baseStart_3936406 baseEnd_3936406 := by
    simpa [prefixWord, tailWord_3936406, baseEnd_3936406] using wordTrace_append hprefix tailTrace_3936406
  have hstable : (prefixWord ++ tailWord_3936406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3936406).length < 2 ^ (prefixWord ++ tailWord_3936406).sum := by decide
  have hdescent : baseEnd_3936406 < baseStart_3936406 := by decide
  rcases family_descends (prefixWord ++ tailWord_3936406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3936429 : List Nat := [1, 5, 2, 1, 2, 2, 2, 2, 1, 3, 2]
def baseStart_3936429 : Nat := 118140960795 + 3936429 * 2 ^ 59
def prefixEnd_3936429 : Nat := 4983230072969 + 3 ^ 40 * 3936429 * 2
def baseEnd_3936429 : Nat := 2021280139297484437134199

theorem tailTrace_3936429 : CollatzResearch.WordTrace tailWord_3936429 prefixEnd_3936429 2021280139297484437134199 := by
  unfold tailWord_3936429
  simp only [CollatzResearch.WordTrace]
  refine ⟨143573360655997496394684341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95715573770664997596456227 143573360655997496394684341)
  ·
    refine ⟨13460002561499765287001657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 143573360655997496394684341 13460002561499765287001657)
    ·
      refine ⟨10095001921124823965251243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13460002561499765287001657 10095001921124823965251243)
      ·
        refine ⟨15142502881687235947876865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10095001921124823965251243 15142502881687235947876865)
        ·
          refine ⟨11356877161265426960907649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15142502881687235947876865 11356877161265426960907649)
          ·
            refine ⟨8517657870949070220680737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11356877161265426960907649 8517657870949070220680737)
            ·
              refine ⟨6388243403211802665510553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8517657870949070220680737 6388243403211802665510553)
              ·
                refine ⟨4791182552408851999132915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6388243403211802665510553 4791182552408851999132915)
                ·
                  refine ⟨7186773828613277998699373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4791182552408851999132915 7186773828613277998699373)
                  ·
                    refine ⟨2695040185729979249512265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7186773828613277998699373 2695040185729979249512265)
                    ·
                      refine ⟨2021280139297484437134199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2695040185729979249512265 2021280139297484437134199)
                      ·
                        rfl

theorem cell23_3936429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 2, 2, 1, 3, 2].length) (baseStart_3936429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3936429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3936429 prefixEnd_3936429 := by exact prefixLift 3936429
  have htrace : WordTrace (prefixWord ++ tailWord_3936429) baseStart_3936429 baseEnd_3936429 := by
    simpa [prefixWord, tailWord_3936429, baseEnd_3936429] using wordTrace_append hprefix tailTrace_3936429
  have hstable : (prefixWord ++ tailWord_3936429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3936429).length < 2 ^ (prefixWord ++ tailWord_3936429).sum := by decide
  have hdescent : baseEnd_3936429 < baseStart_3936429 := by decide
  rcases family_descends (prefixWord ++ tailWord_3936429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3936495 : List Nat := [1, 1, 2, 1, 6, 2, 2, 1, 2, 5]
def baseStart_3936495 : Nat := 118140960795 + 3936495 * 2 ^ 59
def prefixEnd_3936495 : Nat := 4983230072969 + 3 ^ 40 * 3936495 * 2
def baseEnd_3936495 : Nat := 673771343006893726302965

theorem tailTrace_3936495 : CollatzResearch.WordTrace tailWord_3936495 prefixEnd_3936495 673771343006893726302965 := by
  unfold tailWord_3936495
  simp only [CollatzResearch.WordTrace]
  refine ⟨143575767873758389666586939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95717178582505593111057959 143575767873758389666586939)
  ·
    refine ⟨215363651810637584499880409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143575767873758389666586939 215363651810637584499880409)
    ·
      refine ⟨161522738857978188374910307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215363651810637584499880409 161522738857978188374910307)
      ·
        refine ⟨242284108286967282562365461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161522738857978188374910307 242284108286967282562365461)
        ·
          refine ⟨11357067575951591370110881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 242284108286967282562365461 11357067575951591370110881)
          ·
            refine ⟨8517800681963693527583161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11357067575951591370110881 8517800681963693527583161)
            ·
              refine ⟨6388350511472770145687371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8517800681963693527583161 6388350511472770145687371)
              ·
                refine ⟨9582525767209155218531057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6388350511472770145687371 9582525767209155218531057)
                ·
                  refine ⟨7186894325406866413898293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9582525767209155218531057 7186894325406866413898293)
                  ·
                    refine ⟨673771343006893726302965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7186894325406866413898293 673771343006893726302965)
                    ·
                      rfl

theorem cell23_3936495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 2, 1, 2, 5].length) (baseStart_3936495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3936495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3936495 prefixEnd_3936495 := by exact prefixLift 3936495
  have htrace : WordTrace (prefixWord ++ tailWord_3936495) baseStart_3936495 baseEnd_3936495 := by
    simpa [prefixWord, tailWord_3936495, baseEnd_3936495] using wordTrace_append hprefix tailTrace_3936495
  have hstable : (prefixWord ++ tailWord_3936495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3936495).length < 2 ^ (prefixWord ++ tailWord_3936495).sum := by decide
  have hdescent : baseEnd_3936495 < baseStart_3936495 := by decide
  rcases family_descends (prefixWord ++ tailWord_3936495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3936515 : List Nat := [1, 1, 1, 3, 2, 3, 2, 2, 2, 4, 2]
def baseStart_3936515 : Nat := 118140960795 + 3936515 * 2 ^ 59
def prefixEnd_3936515 : Nat := 4983230072969 + 3 ^ 40 * 3936515 * 2
def baseEnd_3936515 : Nat := 2021324298633771100658803

theorem tailTrace_3936515 : CollatzResearch.WordTrace tailWord_3936515 prefixEnd_3936515 2021324298633771100658803 := by
  unfold tailWord_3936515
  simp only [CollatzResearch.WordTrace]
  refine ⟨143576497333685933082314999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95717664889123955388209999 143576497333685933082314999)
  ·
    refine ⟨215364746000528899623472499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143576497333685933082314999 215364746000528899623472499)
    ·
      refine ⟨323047119000793349435208749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215364746000528899623472499 323047119000793349435208749)
      ·
        refine ⟨121142669625297506038203281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 323047119000793349435208749 121142669625297506038203281)
        ·
          refine ⟨90857002218973129528652461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121142669625297506038203281 90857002218973129528652461)
          ·
            refine ⟨34071375832114923573244673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90857002218973129528652461 34071375832114923573244673)
            ·
              refine ⟨25553531874086192679933505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34071375832114923573244673 25553531874086192679933505)
              ·
                refine ⟨19165148905564644509950129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25553531874086192679933505 19165148905564644509950129)
                ·
                  refine ⟨14373861679173483382462597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19165148905564644509950129 14373861679173483382462597)
                  ·
                    refine ⟨2695099064845028134211737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14373861679173483382462597 2695099064845028134211737)
                    ·
                      refine ⟨2021324298633771100658803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2695099064845028134211737 2021324298633771100658803)
                      ·
                        rfl

theorem cell23_3936515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 2, 2, 4, 2].length) (baseStart_3936515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3936515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3936515 prefixEnd_3936515 := by exact prefixLift 3936515
  have htrace : WordTrace (prefixWord ++ tailWord_3936515) baseStart_3936515 baseEnd_3936515 := by
    simpa [prefixWord, tailWord_3936515, baseEnd_3936515] using wordTrace_append hprefix tailTrace_3936515
  have hstable : (prefixWord ++ tailWord_3936515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3936515).length < 2 ^ (prefixWord ++ tailWord_3936515).sum := by decide
  have hdescent : baseEnd_3936515 < baseStart_3936515 := by decide
  rcases family_descends (prefixWord ++ tailWord_3936515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3936516 : List Nat := [2, 3, 2, 2, 4, 1, 2, 2, 5]
def baseStart_3936516 : Nat := 118140960795 + 3936516 * 2 ^ 59
def prefixEnd_3936516 : Nat := 4983230072969 + 3 ^ 40 * 3936516 * 2
def baseEnd_3936516 : Nat := 224591645790491732971811

theorem tailTrace_3936516 : CollatzResearch.WordTrace tailWord_3936516 prefixEnd_3936516 224591645790491732971811 := by
  unfold tailWord_3936516
  simp only [CollatzResearch.WordTrace]
  refine ⟨71788266903341155126550701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95717689204454873502067601 71788266903341155126550701)
  ·
    refine ⟨26920600088752933172456513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71788266903341155126550701 26920600088752933172456513)
    ·
      refine ⟨20190450066564699879342385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26920600088752933172456513 20190450066564699879342385)
      ·
        refine ⟨15142837549923524909506789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20190450066564699879342385 15142837549923524909506789)
        ·
          refine ⟨2839282040610660920532523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15142837549923524909506789 2839282040610660920532523)
          ·
            refine ⟨4258923060915991380798785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2839282040610660920532523 4258923060915991380798785)
            ·
              refine ⟨3194192295686993535599089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4258923060915991380798785 3194192295686993535599089)
              ·
                refine ⟨2395644221765245151699317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3194192295686993535599089 2395644221765245151699317)
                ·
                  refine ⟨224591645790491732971811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2395644221765245151699317 224591645790491732971811)
                  ·
                    rfl

theorem cell23_3936516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 2, 2, 5].length) (baseStart_3936516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3936516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3936516 prefixEnd_3936516 := by exact prefixLift 3936516
  have htrace : WordTrace (prefixWord ++ tailWord_3936516) baseStart_3936516 baseEnd_3936516 := by
    simpa [prefixWord, tailWord_3936516, baseEnd_3936516] using wordTrace_append hprefix tailTrace_3936516
  have hstable : (prefixWord ++ tailWord_3936516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3936516).length < 2 ^ (prefixWord ++ tailWord_3936516).sum := by decide
  have hdescent : baseEnd_3936516 < baseStart_3936516 := by decide
  rcases family_descends (prefixWord ++ tailWord_3936516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3936549 : List Nat := [1, 3, 1, 2, 6, 1, 1, 1, 2, 1, 4]
def baseStart_3936549 : Nat := 118140960795 + 3936549 * 2 ^ 59
def prefixEnd_3936549 : Nat := 4983230072969 + 3 ^ 40 * 3936549 * 2
def baseEnd_3936549 : Nat := 2021341756976023967633647

theorem tailTrace_3936549 : CollatzResearch.WordTrace tailWord_3936549 prefixEnd_3936549 2021341756976023967633647 := by
  unfold tailWord_3936549
  simp only [CollatzResearch.WordTrace]
  refine ⟨143577737415562756889052701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95718491610375171259368467 143577737415562756889052701)
  ·
    refine ⟨53841651530836033833394763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143577737415562756889052701 53841651530836033833394763)
    ·
      refine ⟨80762477296254050750092145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53841651530836033833394763 80762477296254050750092145)
      ·
        refine ⟨60571857972190538062569109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80762477296254050750092145 60571857972190538062569109)
        ·
          refine ⟨2839305842446431471682927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 60571857972190538062569109 2839305842446431471682927)
          ·
            refine ⟨4258958763669647207524391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2839305842446431471682927 4258958763669647207524391)
            ·
              refine ⟨6388438145504470811286587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4258958763669647207524391 6388438145504470811286587)
              ·
                refine ⟨9582657218256706216929881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6388438145504470811286587 9582657218256706216929881)
                ·
                  refine ⟨7186992913692529662697411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9582657218256706216929881 7186992913692529662697411)
                  ·
                    refine ⟨10780489370538794494046117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7186992913692529662697411 10780489370538794494046117)
                    ·
                      refine ⟨2021341756976023967633647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10780489370538794494046117 2021341756976023967633647)
                      ·
                        rfl

theorem cell23_3936549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 1, 1, 2, 1, 4].length) (baseStart_3936549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3936549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3936549 prefixEnd_3936549 := by exact prefixLift 3936549
  have htrace : WordTrace (prefixWord ++ tailWord_3936549) baseStart_3936549 baseEnd_3936549 := by
    simpa [prefixWord, tailWord_3936549, baseEnd_3936549] using wordTrace_append hprefix tailTrace_3936549
  have hstable : (prefixWord ++ tailWord_3936549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3936549).length < 2 ^ (prefixWord ++ tailWord_3936549).sum := by decide
  have hdescent : baseEnd_3936549 < baseStart_3936549 := by decide
  rcases family_descends (prefixWord ++ tailWord_3936549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3936552 : List Nat := [2, 1, 5, 1, 3, 1, 1, 1, 1, 4, 3]
def baseStart_3936552 : Nat := 118140960795 + 3936552 * 2 ^ 59
def prefixEnd_3936552 : Nat := 4983230072969 + 3 ^ 40 * 3936552 * 2
def baseEnd_3936552 : Nat := 2021343297417987455896133

theorem tailTrace_3936552 : CollatzResearch.WordTrace tailWord_3936552 prefixEnd_3936552 2021343297417987455896133 := by
  unfold tailWord_3936552
  simp only [CollatzResearch.WordTrace]
  refine ⟨71788923417275944200705955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95718564556367925600941273 71788923417275944200705955)
  ·
    refine ⟨107683385125913916301058933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71788923417275944200705955 107683385125913916301058933)
    ·
      refine ⟨10095317355554429653224275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 107683385125913916301058933 10095317355554429653224275)
      ·
        refine ⟨15142976033331644479836413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10095317355554429653224275 15142976033331644479836413)
        ·
          refine ⟨5678616012499366679938655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15142976033331644479836413 5678616012499366679938655)
          ·
            refine ⟨8517924018749050019907983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5678616012499366679938655 8517924018749050019907983)
            ·
              refine ⟨12776886028123575029861975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8517924018749050019907983 12776886028123575029861975)
              ·
                refine ⟨19165329042185362544792963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12776886028123575029861975 19165329042185362544792963)
                ·
                  refine ⟨28747993563278043817189445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19165329042185362544792963 28747993563278043817189445)
                  ·
                    refine ⟨5390248793114633215723021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28747993563278043817189445 5390248793114633215723021)
                    ·
                      refine ⟨2021343297417987455896133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5390248793114633215723021 2021343297417987455896133)
                      ·
                        rfl

theorem cell23_3936552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 1, 1, 1, 4, 3].length) (baseStart_3936552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3936552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3936552 prefixEnd_3936552 := by exact prefixLift 3936552
  have htrace : WordTrace (prefixWord ++ tailWord_3936552) baseStart_3936552 baseEnd_3936552 := by
    simpa [prefixWord, tailWord_3936552, baseEnd_3936552] using wordTrace_append hprefix tailTrace_3936552
  have hstable : (prefixWord ++ tailWord_3936552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3936552).length < 2 ^ (prefixWord ++ tailWord_3936552).sum := by decide
  have hdescent : baseEnd_3936552 < baseStart_3936552 := by decide
  rcases family_descends (prefixWord ++ tailWord_3936552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3936616 : List Nat := [2, 1, 4, 2, 2, 1, 3, 3, 1, 1, 3]
def baseStart_3936616 : Nat := 118140960795 + 3936616 * 2 ^ 59
def prefixEnd_3936616 : Nat := 4983230072969 + 3 ^ 40 * 3936616 * 2
def baseEnd_3936616 : Nat := 2021376160179875205495839

theorem tailTrace_3936616 : CollatzResearch.WordTrace tailWord_3936616 prefixEnd_3936616 2021376160179875205495839 := by
  unfold tailWord_3936616
  simp only [CollatzResearch.WordTrace]
  refine ⟨71790090553160013665870851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95720120737546684887827801 71790090553160013665870851)
  ·
    refine ⟨107685135829740020498806277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71790090553160013665870851 107685135829740020498806277)
    ·
      refine ⟨20190962968076253843526177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 107685135829740020498806277 20190962968076253843526177)
      ·
        refine ⟨15143222226057190382644633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20190962968076253843526177 15143222226057190382644633)
        ·
          refine ⟨11357416669542892786983475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15143222226057190382644633 11357416669542892786983475)
          ·
            refine ⟨17036125004314339180475213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11357416669542892786983475 17036125004314339180475213)
            ·
              refine ⟨6388546876617877192678205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17036125004314339180475213 6388546876617877192678205)
              ·
                refine ⟨2395705078731703947254327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6388546876617877192678205 2395705078731703947254327)
                ·
                  refine ⟨3593557618097555920881491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2395705078731703947254327 3593557618097555920881491)
                  ·
                    refine ⟨5390336427146333881322237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3593557618097555920881491 5390336427146333881322237)
                    ·
                      refine ⟨2021376160179875205495839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5390336427146333881322237 2021376160179875205495839)
                      ·
                        rfl

theorem cell23_3936616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 3, 3, 1, 1, 3].length) (baseStart_3936616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3936616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3936616 prefixEnd_3936616 := by exact prefixLift 3936616
  have htrace : WordTrace (prefixWord ++ tailWord_3936616) baseStart_3936616 baseEnd_3936616 := by
    simpa [prefixWord, tailWord_3936616, baseEnd_3936616] using wordTrace_append hprefix tailTrace_3936616
  have hstable : (prefixWord ++ tailWord_3936616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3936616).length < 2 ^ (prefixWord ++ tailWord_3936616).sum := by decide
  have hdescent : baseEnd_3936616 < baseStart_3936616 := by decide
  rcases family_descends (prefixWord ++ tailWord_3936616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3936625 : List Nat := [1, 2, 2, 2, 1, 2, 1, 2, 5, 2, 3]
def baseStart_3936625 : Nat := 118140960795 + 3936625 * 2 ^ 59
def prefixEnd_3936625 : Nat := 4983230072969 + 3 ^ 40 * 3936625 * 2
def baseEnd_3936625 : Nat := 2021380781505765670283297

theorem tailTrace_3936625 : CollatzResearch.WordTrace tailWord_3936625 prefixEnd_3936625 2021380781505765670283297 := by
  unfold tailWord_3936625
  simp only [CollatzResearch.WordTrace]
  refine ⟨143580509363287421868819329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95720339575524947912546219 143580509363287421868819329)
  ·
    refine ⟨107685382022465566401614497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143580509363287421868819329 107685382022465566401614497)
    ·
      refine ⟨80764036516849174801210873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107685382022465566401614497 80764036516849174801210873)
      ·
        refine ⟨60573027387636881100908155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80764036516849174801210873 60573027387636881100908155)
        ·
          refine ⟨90859541081455321651362233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60573027387636881100908155 90859541081455321651362233)
          ·
            refine ⟨68144655811091491238521675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90859541081455321651362233 68144655811091491238521675)
            ·
              refine ⟨102216983716637236857782513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68144655811091491238521675 102216983716637236857782513)
              ·
                refine ⟨76662737787477927643336885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102216983716637236857782513 76662737787477927643336885)
                ·
                  refine ⟨7187131667576055716562833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 76662737787477927643336885 7187131667576055716562833)
                  ·
                    refine ⟨5390348750682041787422125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7187131667576055716562833 5390348750682041787422125)
                    ·
                      refine ⟨2021380781505765670283297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5390348750682041787422125 2021380781505765670283297)
                      ·
                        rfl

theorem cell23_3936625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 2, 5, 2, 3].length) (baseStart_3936625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3936625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3936625 prefixEnd_3936625 := by exact prefixLift 3936625
  have htrace : WordTrace (prefixWord ++ tailWord_3936625) baseStart_3936625 baseEnd_3936625 := by
    simpa [prefixWord, tailWord_3936625, baseEnd_3936625] using wordTrace_append hprefix tailTrace_3936625
  have hstable : (prefixWord ++ tailWord_3936625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3936625).length < 2 ^ (prefixWord ++ tailWord_3936625).sum := by decide
  have hdescent : baseEnd_3936625 < baseStart_3936625 := by decide
  rcases family_descends (prefixWord ++ tailWord_3936625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3936649 : List Nat := [1, 2, 1, 1, 6, 1, 4, 1, 2, 4]
def baseStart_3936649 : Nat := 118140960795 + 3936649 * 2 ^ 59
def prefixEnd_3936649 : Nat := 4983230072969 + 3 ^ 40 * 3936649 * 2
def baseEnd_3936649 : Nat := 673797701680491192127729

theorem tailTrace_3936649 : CollatzResearch.WordTrace tailWord_3936649 prefixEnd_3936649 673797701680491192127729 := by
  unfold tailWord_3936649
  simp only [CollatzResearch.WordTrace]
  refine ⟨143581384715200473967693001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95720923143466982645128667 143581384715200473967693001)
  ·
    refine ⟨107686038536400355475769751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143581384715200473967693001 107686038536400355475769751)
    ·
      refine ⟨161529057804600533213654627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107686038536400355475769751 161529057804600533213654627)
      ·
        refine ⟨242293586706900799820481941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161529057804600533213654627 242293586706900799820481941)
        ·
          refine ⟨11357511876885974991585091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 242293586706900799820481941 11357511876885974991585091)
          ·
            refine ⟨17036267815328962487377637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11357511876885974991585091 17036267815328962487377637)
            ·
              refine ⟨3194300215374180466383307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17036267815328962487377637 3194300215374180466383307)
              ·
                refine ⟨4791450323061270699574961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3194300215374180466383307 4791450323061270699574961)
                ·
                  refine ⟨3593587742295953024681221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4791450323061270699574961 3593587742295953024681221)
                  ·
                    refine ⟨673797701680491192127729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3593587742295953024681221 673797701680491192127729)
                    ·
                      rfl

theorem cell23_3936649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 4, 1, 2, 4].length) (baseStart_3936649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3936649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3936649 prefixEnd_3936649 := by exact prefixLift 3936649
  have htrace : WordTrace (prefixWord ++ tailWord_3936649) baseStart_3936649 baseEnd_3936649 := by
    simpa [prefixWord, tailWord_3936649, baseEnd_3936649] using wordTrace_append hprefix tailTrace_3936649
  have hstable : (prefixWord ++ tailWord_3936649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3936649).length < 2 ^ (prefixWord ++ tailWord_3936649).sum := by decide
  have hdescent : baseEnd_3936649 < baseStart_3936649 := by decide
  rcases family_descends (prefixWord ++ tailWord_3936649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3936672 : List Nat := [2, 1, 1, 4, 1, 4, 1, 2, 1, 3, 3]
def baseStart_3936672 : Nat := 118140960795 + 3936672 * 2 ^ 59
def prefixEnd_3936672 : Nat := 4983230072969 + 3 ^ 40 * 3936672 * 2
def baseEnd_3936672 : Nat := 2021404915096526986395581

theorem tailTrace_3936672 : CollatzResearch.WordTrace tailWord_3936672 prefixEnd_3936672 2021404915096526986395581 := by
  unfold tailWord_3936672
  simp only [CollatzResearch.WordTrace]
  refine ⟨71791111797058574447890135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95721482396078099263853513 71791111797058574447890135)
  ·
    refine ⟨107686667695587861671835203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71791111797058574447890135 107686667695587861671835203)
    ·
      refine ⟨161530001543381792507752805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107686667695587861671835203 161530001543381792507752805)
      ·
        refine ⟨30286875289384086095203651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 161530001543381792507752805 30286875289384086095203651)
        ·
          refine ⟨45430312934076129142805477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30286875289384086095203651 45430312934076129142805477)
          ·
            refine ⟨8518183675139274214276027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45430312934076129142805477 8518183675139274214276027)
            ·
              refine ⟨12777275512708911321414041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8518183675139274214276027 12777275512708911321414041)
              ·
                refine ⟨9582956634531683491060531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12777275512708911321414041 9582956634531683491060531)
                ·
                  refine ⟨14374434951797525236590797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9582956634531683491060531 14374434951797525236590797)
                  ·
                    refine ⟨5390413106924071963721549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14374434951797525236590797 5390413106924071963721549)
                    ·
                      refine ⟨2021404915096526986395581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5390413106924071963721549 2021404915096526986395581)
                      ·
                        rfl

theorem cell23_3936672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 1, 2, 1, 3, 3].length) (baseStart_3936672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3936672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3936672 prefixEnd_3936672 := by exact prefixLift 3936672
  have htrace : WordTrace (prefixWord ++ tailWord_3936672) baseStart_3936672 baseEnd_3936672 := by
    simpa [prefixWord, tailWord_3936672, baseEnd_3936672] using wordTrace_append hprefix tailTrace_3936672
  have hstable : (prefixWord ++ tailWord_3936672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3936672).length < 2 ^ (prefixWord ++ tailWord_3936672).sum := by decide
  have hdescent : baseEnd_3936672 < baseStart_3936672 := by decide
  rcases family_descends (prefixWord ++ tailWord_3936672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3936689 : List Nat := [1, 2, 2, 4, 1, 2, 1, 4, 2, 1, 3]
def baseStart_3936689 : Nat := 118140960795 + 3936689 * 2 ^ 59
def prefixEnd_3936689 : Nat := 4983230072969 + 3 ^ 40 * 3936689 * 2
def baseEnd_3936689 : Nat := 2021413644267653419883003

theorem tailTrace_3936689 : CollatzResearch.WordTrace tailWord_3936689 prefixEnd_3936689 2021413644267653419883003 := by
  unfold tailWord_3936689
  simp only [CollatzResearch.WordTrace]
  refine ⟨143582843635055560799149121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95721895756703707199432747 143582843635055560799149121)
  ·
    refine ⟨107687132726291670599361841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143582843635055560799149121 107687132726291670599361841)
    ·
      refine ⟨80765349544718752949521381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107687132726291670599361841 80765349544718752949521381)
      ·
        refine ⟨15143503039634766178035259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80765349544718752949521381 15143503039634766178035259)
        ·
          refine ⟨22715254559452149267052889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15143503039634766178035259 22715254559452149267052889)
          ·
            refine ⟨17036440919589111950289667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22715254559452149267052889 17036440919589111950289667)
            ·
              refine ⟨25554661379383667925434501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17036440919589111950289667 25554661379383667925434501)
              ·
                refine ⟨4791499008634437736018969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25554661379383667925434501 4791499008634437736018969)
                ·
                  refine ⟨3593624256475828302014227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4791499008634437736018969 3593624256475828302014227)
                  ·
                    refine ⟨5390436384713742453021341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3593624256475828302014227 5390436384713742453021341)
                    ·
                      refine ⟨2021413644267653419883003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5390436384713742453021341 2021413644267653419883003)
                      ·
                        rfl

theorem cell23_3936689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 4, 2, 1, 3].length) (baseStart_3936689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3936689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3936689 prefixEnd_3936689 := by exact prefixLift 3936689
  have htrace : WordTrace (prefixWord ++ tailWord_3936689) baseStart_3936689 baseEnd_3936689 := by
    simpa [prefixWord, tailWord_3936689, baseEnd_3936689] using wordTrace_append hprefix tailTrace_3936689
  have hstable : (prefixWord ++ tailWord_3936689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3936689).length < 2 ^ (prefixWord ++ tailWord_3936689).sum := by decide
  have hdescent : baseEnd_3936689 < baseStart_3936689 := by decide
  rcases family_descends (prefixWord ++ tailWord_3936689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3936695 : List Nat := [1, 1, 3, 1, 3, 3, 1, 1, 2, 3, 4]
def baseStart_3936695 : Nat := 118140960795 + 3936695 * 2 ^ 59
def prefixEnd_3936695 : Nat := 4983230072969 + 3 ^ 40 * 3936695 * 2
def baseEnd_3936695 : Nat := 2021416725151580396407975

theorem tailTrace_3936695 : CollatzResearch.WordTrace tailWord_3936695 prefixEnd_3936695 2021416725151580396407975 := by
  unfold tailWord_3936695
  simp only [CollatzResearch.WordTrace]
  refine ⟨143583062473033823823867539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95722041648689215882578359 143583062473033823823867539)
  ·
    refine ⟨215374593709550735735801309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143583062473033823823867539 215374593709550735735801309)
    ·
      refine ⟨80765472641081525900925491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 215374593709550735735801309 80765472641081525900925491)
      ·
        refine ⟨121148208961622288851388237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80765472641081525900925491 121148208961622288851388237)
        ·
          refine ⟨45430578360608358319270589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121148208961622288851388237 45430578360608358319270589)
          ·
            refine ⟨17036466885228134369726471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45430578360608358319270589 17036466885228134369726471)
            ·
              refine ⟨25554700327842201554589707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17036466885228134369726471 25554700327842201554589707)
              ·
                refine ⟨38332050491763302331884561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25554700327842201554589707 38332050491763302331884561)
                ·
                  refine ⟨28749037868822476748913421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38332050491763302331884561 28749037868822476748913421)
                  ·
                    refine ⟨10780889200808428780842533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28749037868822476748913421 10780889200808428780842533)
                    ·
                      refine ⟨2021416725151580396407975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10780889200808428780842533 2021416725151580396407975)
                      ·
                        rfl

theorem cell23_3936695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 1, 2, 3, 4].length) (baseStart_3936695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3936695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3936695 prefixEnd_3936695 := by exact prefixLift 3936695
  have htrace : WordTrace (prefixWord ++ tailWord_3936695) baseStart_3936695 baseEnd_3936695 := by
    simpa [prefixWord, tailWord_3936695, baseEnd_3936695] using wordTrace_append hprefix tailTrace_3936695
  have hstable : (prefixWord ++ tailWord_3936695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3936695).length < 2 ^ (prefixWord ++ tailWord_3936695).sum := by decide
  have hdescent : baseEnd_3936695 < baseStart_3936695 := by decide
  rcases family_descends (prefixWord ++ tailWord_3936695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3936715 : List Nat := [1, 1, 1, 1, 3, 3, 1, 1, 4, 4, 3]
def baseStart_3936715 : Nat := 118140960795 + 3936715 * 2 ^ 59
def prefixEnd_3936715 : Nat := 4983230072969 + 3 ^ 40 * 3936715 * 2
def baseEnd_3936715 : Nat := 2021426994764670318157883

theorem tailTrace_3936715 : CollatzResearch.WordTrace tailWord_3936715 prefixEnd_3936715 2021426994764670318157883 := by
  unfold tailWord_3936715
  simp only [CollatzResearch.WordTrace]
  refine ⟨143583791932961367239595599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95722527955307578159730399 143583791932961367239595599)
  ·
    refine ⟨215375687899442050859393399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143583791932961367239595599 215375687899442050859393399)
    ·
      refine ⟨323063531849163076289090099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215375687899442050859393399 323063531849163076289090099)
      ·
        refine ⟨484595297773744614433635149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 323063531849163076289090099 484595297773744614433635149)
        ·
          refine ⟨181723236665154230412613181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 484595297773744614433635149 181723236665154230412613181)
          ·
            refine ⟨68146213749432836404729943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 181723236665154230412613181 68146213749432836404729943)
            ·
              refine ⟨102219320624149254607094915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68146213749432836404729943 102219320624149254607094915)
              ·
                refine ⟨153328980936223881910642373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102219320624149254607094915 153328980936223881910642373)
                ·
                  refine ⟨28749183925541977858245445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 153328980936223881910642373 28749183925541977858245445)
                  ·
                    refine ⟨5390471986039120848421021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28749183925541977858245445 5390471986039120848421021)
                    ·
                      refine ⟨2021426994764670318157883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5390471986039120848421021 2021426994764670318157883)
                      ·
                        rfl

theorem cell23_3936715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 1, 4, 4, 3].length) (baseStart_3936715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3936715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3936715 prefixEnd_3936715 := by exact prefixLift 3936715
  have htrace : WordTrace (prefixWord ++ tailWord_3936715) baseStart_3936715 baseEnd_3936715 := by
    simpa [prefixWord, tailWord_3936715, baseEnd_3936715] using wordTrace_append hprefix tailTrace_3936715
  have hstable : (prefixWord ++ tailWord_3936715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3936715).length < 2 ^ (prefixWord ++ tailWord_3936715).sum := by decide
  have hdescent : baseEnd_3936715 < baseStart_3936715 := by decide
  rcases family_descends (prefixWord ++ tailWord_3936715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3936729 : List Nat := [1, 2, 1, 2, 4, 1, 2, 2, 4, 2, 2]
def baseStart_3936729 : Nat := 118140960795 + 3936729 * 2 ^ 59
def prefixEnd_3936729 : Nat := 4983230072969 + 3 ^ 40 * 3936729 * 2
def baseEnd_3936729 : Nat := 2021434183493833263382819

theorem tailTrace_3936729 : CollatzResearch.WordTrace tailWord_3936729 prefixEnd_3936729 2021434183493833263382819 := by
  unfold tailWord_3936729
  simp only [CollatzResearch.WordTrace]
  refine ⟨143584302554910647630605241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95722868369940431753736827 143584302554910647630605241)
  ·
    refine ⟨107688226916182985722953931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143584302554910647630605241 107688226916182985722953931)
    ·
      refine ⟨161532340374274478584430897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107688226916182985722953931 161532340374274478584430897)
      ·
        refine ⟨121149255280705858938323173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161532340374274478584430897 121149255280705858938323173)
        ·
          refine ⟨22715485365132348550935595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 121149255280705858938323173 22715485365132348550935595)
          ·
            refine ⟨34073228047698522826403393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22715485365132348550935595 34073228047698522826403393)
            ·
              refine ⟨25554921035773892119802545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34073228047698522826403393 25554921035773892119802545)
              ·
                refine ⟨19166190776830419089851909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25554921035773892119802545 19166190776830419089851909)
                ·
                  refine ⟨3593660770655703579347233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19166190776830419089851909 3593660770655703579347233)
                  ·
                    refine ⟨2695245577991777684510425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3593660770655703579347233 2695245577991777684510425)
                    ·
                      refine ⟨2021434183493833263382819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2695245577991777684510425 2021434183493833263382819)
                      ·
                        rfl

theorem cell23_3936729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 2, 4, 2, 2].length) (baseStart_3936729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3936729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3936729 prefixEnd_3936729 := by exact prefixLift 3936729
  have htrace : WordTrace (prefixWord ++ tailWord_3936729) baseStart_3936729 baseEnd_3936729 := by
    simpa [prefixWord, tailWord_3936729, baseEnd_3936729] using wordTrace_append hprefix tailTrace_3936729
  have hstable : (prefixWord ++ tailWord_3936729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3936729).length < 2 ^ (prefixWord ++ tailWord_3936729).sum := by decide
  have hdescent : baseEnd_3936729 < baseStart_3936729 := by decide
  rcases family_descends (prefixWord ++ tailWord_3936729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3936746 : List Nat := [3, 1, 3, 1, 3, 2, 1, 1, 4, 2, 2]
def baseStart_3936746 : Nat := 118140960795 + 3936746 * 2 ^ 59
def prefixEnd_3936746 : Nat := 4983230072969 + 3 ^ 40 * 3936746 * 2
def baseEnd_3936746 : Nat := 2021442912664959696870241

theorem tailTrace_3936746 : CollatzResearch.WordTrace tailWord_3936746 prefixEnd_3936746 2021442912664959696870241 := by
  unfold tailWord_3936746
  simp only [CollatzResearch.WordTrace]
  refine ⟨35896230648962264883493523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95723281730566039689316061 35896230648962264883493523)
  ·
    refine ⟨53844345973443397325240285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35896230648962264883493523 53844345973443397325240285)
    ·
      refine ⟨20191629740041273996965107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53844345973443397325240285 20191629740041273996965107)
      ·
        refine ⟨30287444610061910995447661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20191629740041273996965107 30287444610061910995447661)
        ·
          refine ⟨11357791728773216623292873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30287444610061910995447661 11357791728773216623292873)
          ·
            refine ⟨8518343796579912467469655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11357791728773216623292873 8518343796579912467469655)
            ·
              refine ⟨12777515694869868701204483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8518343796579912467469655 12777515694869868701204483)
              ·
                refine ⟨19166273542304803051806725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12777515694869868701204483 19166273542304803051806725)
                ·
                  refine ⟨3593676289182150572213761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19166273542304803051806725 3593676289182150572213761)
                  ·
                    refine ⟨2695257216886612929160321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3593676289182150572213761 2695257216886612929160321)
                    ·
                      refine ⟨2021442912664959696870241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2695257216886612929160321 2021442912664959696870241)
                      ·
                        rfl

theorem cell23_3936746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 1, 1, 4, 2, 2].length) (baseStart_3936746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3936746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3936746 prefixEnd_3936746 := by exact prefixLift 3936746
  have htrace : WordTrace (prefixWord ++ tailWord_3936746) baseStart_3936746 baseEnd_3936746 := by
    simpa [prefixWord, tailWord_3936746, baseEnd_3936746] using wordTrace_append hprefix tailTrace_3936746
  have hstable : (prefixWord ++ tailWord_3936746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3936746).length < 2 ^ (prefixWord ++ tailWord_3936746).sum := by decide
  have hdescent : baseEnd_3936746 < baseStart_3936746 := by decide
  rcases family_descends (prefixWord ++ tailWord_3936746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3936752 : List Nat := [2, 1, 1, 1, 3, 3, 1, 6, 5]
def baseStart_3936752 : Nat := 118140960795 + 3936752 * 2 ^ 59
def prefixEnd_3936752 : Nat := 4983230072969 + 3 ^ 40 * 3936752 * 2
def baseEnd_3936752 : Nat := 224605110394320741488357

theorem tailTrace_3936752 : CollatzResearch.WordTrace tailWord_3936752 prefixEnd_3936752 224605110394320741488357 := by
  unfold tailWord_3936752
  simp only [CollatzResearch.WordTrace]
  refine ⟨71792570716913661279346255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95723427622551548372461673 71792570716913661279346255)
  ·
    refine ⟨107688856075370491919019383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71792570716913661279346255 107688856075370491919019383)
    ·
      refine ⟨161533284113055737878529075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107688856075370491919019383 161533284113055737878529075)
      ·
        refine ⟨242299926169583606817793613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161533284113055737878529075 242299926169583606817793613)
        ·
          refine ⟨90862472313593852556672605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 242299926169583606817793613 90862472313593852556672605)
          ·
            refine ⟨34073427117597694708752227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90862472313593852556672605 34073427117597694708752227)
            ·
              refine ⟨51110140676396542063128341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34073427117597694708752227 51110140676396542063128341)
              ·
                refine ⟨2395787844206087909209141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 51110140676396542063128341 2395787844206087909209141)
                ·
                  refine ⟨224605110394320741488357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2395787844206087909209141 224605110394320741488357)
                  ·
                    rfl

theorem cell23_3936752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 6, 5].length) (baseStart_3936752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3936752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3936752 prefixEnd_3936752 := by exact prefixLift 3936752
  have htrace : WordTrace (prefixWord ++ tailWord_3936752) baseStart_3936752 baseEnd_3936752 := by
    simpa [prefixWord, tailWord_3936752, baseEnd_3936752] using wordTrace_append hprefix tailTrace_3936752
  have hstable : (prefixWord ++ tailWord_3936752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3936752).length < 2 ^ (prefixWord ++ tailWord_3936752).sum := by decide
  have hdescent : baseEnd_3936752 < baseStart_3936752 := by decide
  rcases family_descends (prefixWord ++ tailWord_3936752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3936765 : List Nat := [1, 4, 1, 1, 1, 3, 1, 1, 3, 7]
def baseStart_3936765 : Nat := 118140960795 + 3936765 * 2 ^ 59
def prefixEnd_3936765 : Nat := 4983230072969 + 3 ^ 40 * 3936765 * 2
def baseEnd_3936765 : Nat := 673817556265798374177551

theorem tailTrace_3936765 : CollatzResearch.WordTrace tailWord_3936765 prefixEnd_3936765 673817556265798374177551 := by
  unfold tailWord_3936765
  simp only [CollatzResearch.WordTrace]
  refine ⟨143585615582780225778915749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95723743721853483852610499 143585615582780225778915749)
  ·
    refine ⟨26922302921771292333546703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 143585615582780225778915749 26922302921771292333546703)
    ·
      refine ⟨40383454382656938500320055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26922302921771292333546703 40383454382656938500320055)
      ·
        refine ⟨60575181573985407750480083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40383454382656938500320055 60575181573985407750480083)
        ·
          refine ⟨90862772360978111625720125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60575181573985407750480083 90862772360978111625720125)
          ·
            refine ⟨34073539635366791859645047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90862772360978111625720125 34073539635366791859645047)
            ·
              refine ⟨51110309453050187789467571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34073539635366791859645047 51110309453050187789467571)
              ·
                refine ⟨76665464179575281684201357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51110309453050187789467571 76665464179575281684201357)
                ·
                  refine ⟨28749549067340730631575509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76665464179575281684201357 28749549067340730631575509)
                  ·
                    refine ⟨673817556265798374177551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28749549067340730631575509 673817556265798374177551)
                    ·
                      rfl

theorem cell23_3936765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 1, 3, 7].length) (baseStart_3936765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3936765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3936765 prefixEnd_3936765 := by exact prefixLift 3936765
  have htrace : WordTrace (prefixWord ++ tailWord_3936765) baseStart_3936765 baseEnd_3936765 := by
    simpa [prefixWord, tailWord_3936765, baseEnd_3936765] using wordTrace_append hprefix tailTrace_3936765
  have hstable : (prefixWord ++ tailWord_3936765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3936765).length < 2 ^ (prefixWord ++ tailWord_3936765).sum := by decide
  have hdescent : baseEnd_3936765 < baseStart_3936765 := by decide
  rcases family_descends (prefixWord ++ tailWord_3936765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3936782 : List Nat := [4, 1, 1, 2, 3, 1, 2, 1, 1, 7]
def baseStart_3936782 : Nat := 118140960795 + 3936782 * 2 ^ 59
def prefixEnd_3936782 : Nat := 4983230072969 + 3 ^ 40 * 3936782 * 2
def baseEnd_3936782 : Nat := 673820465989507185340025

theorem tailTrace_3936782 : CollatzResearch.WordTrace tailWord_3936782 prefixEnd_3936782 673820465989507185340025 := by
  unfold tailWord_3936782
  simp only [CollatzResearch.WordTrace]
  refine ⟨17948279452964829710285575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95724157082479091788189733 17948279452964829710285575)
  ·
    refine ⟨26922419179447244565428363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17948279452964829710285575 26922419179447244565428363)
    ·
      refine ⟨40383628769170866848142545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26922419179447244565428363 40383628769170866848142545)
      ·
        refine ⟨30287721576878150136106909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40383628769170866848142545 30287721576878150136106909)
        ·
          refine ⟨11357895591329306301040091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30287721576878150136106909 11357895591329306301040091)
          ·
            refine ⟨17036843386993959451560137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11357895591329306301040091 17036843386993959451560137)
            ·
              refine ⟨12777632540245469588670103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17036843386993959451560137 12777632540245469588670103)
              ·
                refine ⟨19166448810368204383005155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12777632540245469588670103 19166448810368204383005155)
                ·
                  refine ⟨28749673215552306574507733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19166448810368204383005155 28749673215552306574507733)
                  ·
                    refine ⟨673820465989507185340025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28749673215552306574507733 673820465989507185340025)
                    ·
                      rfl

theorem cell23_3936782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 2, 1, 1, 7].length) (baseStart_3936782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3936782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3936782 prefixEnd_3936782 := by exact prefixLift 3936782
  have htrace : WordTrace (prefixWord ++ tailWord_3936782) baseStart_3936782 baseEnd_3936782 := by
    simpa [prefixWord, tailWord_3936782, baseEnd_3936782] using wordTrace_append hprefix tailTrace_3936782
  have hstable : (prefixWord ++ tailWord_3936782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3936782).length < 2 ^ (prefixWord ++ tailWord_3936782).sum := by decide
  have hdescent : baseEnd_3936782 < baseStart_3936782 := by decide
  rcases family_descends (prefixWord ++ tailWord_3936782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3936839 : List Nat := [1, 1, 4, 1, 4, 1, 1, 3, 2, 2, 3]
def baseStart_3936839 : Nat := 118140960795 + 3936839 * 2 ^ 59
def prefixEnd_3936839 : Nat := 4983230072969 + 3 ^ 40 * 3936839 * 2
def baseEnd_3936839 : Nat := 2021490666365827833007313

theorem tailTrace_3936839 : CollatzResearch.WordTrace tailWord_3936839 prefixEnd_3936839 2021490666365827833007313 := by
  unfold tailWord_3936839
  simp only [CollatzResearch.WordTrace]
  refine ⟨143588314584512136417109571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95725543056341424278073047 143588314584512136417109571)
  ·
    refine ⟨215382471876768204625664357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143588314584512136417109571 215382471876768204625664357)
    ·
      refine ⟨40384213476894038367312067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 215382471876768204625664357 40384213476894038367312067)
      ·
        refine ⟨60576320215341057550968101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40384213476894038367312067 60576320215341057550968101)
        ·
          refine ⟨11358060040376448290806519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60576320215341057550968101 11358060040376448290806519)
          ·
            refine ⟨17037090060564672436209779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11358060040376448290806519 17037090060564672436209779)
            ·
              refine ⟨25555635090847008654314669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17037090060564672436209779 25555635090847008654314669)
              ·
                refine ⟨9583363159067628245368001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25555635090847008654314669 9583363159067628245368001)
                ·
                  refine ⟨7187522369300721184026001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9583363159067628245368001 7187522369300721184026001)
                  ·
                    refine ⟨5390641776975540888019501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7187522369300721184026001 5390641776975540888019501)
                    ·
                      refine ⟨2021490666365827833007313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5390641776975540888019501 2021490666365827833007313)
                      ·
                        rfl

theorem cell23_3936839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 3, 2, 2, 3].length) (baseStart_3936839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3936839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3936839 prefixEnd_3936839 := by exact prefixLift 3936839
  have htrace : WordTrace (prefixWord ++ tailWord_3936839) baseStart_3936839 baseEnd_3936839 := by
    simpa [prefixWord, tailWord_3936839, baseEnd_3936839] using wordTrace_append hprefix tailTrace_3936839
  have hstable : (prefixWord ++ tailWord_3936839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3936839).length < 2 ^ (prefixWord ++ tailWord_3936839).sum := by decide
  have hdescent : baseEnd_3936839 < baseStart_3936839 := by decide
  rcases family_descends (prefixWord ++ tailWord_3936839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3936879 : List Nat := [1, 1, 2, 1, 3, 2, 2, 2, 4, 3, 2]
def baseStart_3936879 : Nat := 118140960795 + 3936879 * 2 ^ 59
def prefixEnd_3936879 : Nat := 4983230072969 + 3 ^ 40 * 3936879 * 2
def baseEnd_3936879 : Nat := 2021511205592007676507129

theorem tailTrace_3936879 : CollatzResearch.WordTrace tailWord_3936879 prefixEnd_3936879 2021511205592007676507129 := by
  unfold tailWord_3936879
  simp only [CollatzResearch.WordTrace]
  refine ⟨143589773504367223248565691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95726515669578148832377127 143589773504367223248565691)
  ·
    refine ⟨215384660256550834872848537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143589773504367223248565691 215384660256550834872848537)
    ·
      refine ⟨161538495192413126154636403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215384660256550834872848537 161538495192413126154636403)
      ·
        refine ⟨242307742788619689231954605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161538495192413126154636403 242307742788619689231954605)
        ·
          refine ⟨90865403545732383461982977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 242307742788619689231954605 90865403545732383461982977)
          ·
            refine ⟨68149052659299287596487233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90865403545732383461982977 68149052659299287596487233)
            ·
              refine ⟨51111789494474465697365425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68149052659299287596487233 51111789494474465697365425)
              ·
                refine ⟨38333842120855849273024069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51111789494474465697365425 38333842120855849273024069)
                ·
                  refine ⟨7187595397660471738692013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38333842120855849273024069 7187595397660471738692013)
                  ·
                    refine ⟨2695348274122676902009505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7187595397660471738692013 2695348274122676902009505)
                    ·
                      refine ⟨2021511205592007676507129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2695348274122676902009505 2021511205592007676507129)
                      ·
                        rfl

theorem cell23_3936879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 2, 4, 3, 2].length) (baseStart_3936879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3936879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3936879 prefixEnd_3936879 := by exact prefixLift 3936879
  have htrace : WordTrace (prefixWord ++ tailWord_3936879) baseStart_3936879 baseEnd_3936879 := by
    simpa [prefixWord, tailWord_3936879, baseEnd_3936879] using wordTrace_append hprefix tailTrace_3936879
  have hstable : (prefixWord ++ tailWord_3936879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3936879).length < 2 ^ (prefixWord ++ tailWord_3936879).sum := by decide
  have hdescent : baseEnd_3936879 < baseStart_3936879 := by decide
  rcases family_descends (prefixWord ++ tailWord_3936879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3936896 : List Nat := [2, 1, 1, 2, 1, 5, 3, 1, 2, 3, 2]
def baseStart_3936896 : Nat := 118140960795 + 3936896 * 2 ^ 59
def prefixEnd_3936896 : Nat := 4983230072969 + 3 ^ 40 * 3936896 * 2
def baseEnd_3936896 : Nat := 2021519934763134109994551

theorem tailTrace_3936896 : CollatzResearch.WordTrace tailWord_3936896 prefixEnd_3936896 2021519934763134109994551 := by
  unfold tailWord_3936896
  simp only [CollatzResearch.WordTrace]
  refine ⟨71795196772652817575967271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95726929030203756767956361 71795196772652817575967271)
  ·
    refine ⟨107692795158979226363950907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71795196772652817575967271 107692795158979226363950907)
    ·
      refine ⟨161539192738468839545926361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107692795158979226363950907 161539192738468839545926361)
      ·
        refine ⟨121154394553851629659444771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161539192738468839545926361 121154394553851629659444771)
        ·
          refine ⟨181731591830777444489167157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121154394553851629659444771 181731591830777444489167157)
          ·
            refine ⟨17037336734135385420859421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 181731591830777444489167157 17037336734135385420859421)
            ·
              refine ⟨6389001275300769532822283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17037336734135385420859421 6389001275300769532822283)
              ·
                refine ⟨9583501912951154299233425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6389001275300769532822283 9583501912951154299233425)
                ·
                  refine ⟨7187626434713365724425069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9583501912951154299233425 7187626434713365724425069)
                  ·
                    refine ⟨2695359913017512146659401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7187626434713365724425069 2695359913017512146659401)
                    ·
                      refine ⟨2021519934763134109994551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2695359913017512146659401 2021519934763134109994551)
                      ·
                        rfl

theorem cell23_3936896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 3, 1, 2, 3, 2].length) (baseStart_3936896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3936896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3936896 prefixEnd_3936896 := by exact prefixLift 3936896
  have htrace : WordTrace (prefixWord ++ tailWord_3936896) baseStart_3936896 baseEnd_3936896 := by
    simpa [prefixWord, tailWord_3936896, baseEnd_3936896] using wordTrace_append hprefix tailTrace_3936896
  have hstable : (prefixWord ++ tailWord_3936896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3936896).length < 2 ^ (prefixWord ++ tailWord_3936896).sum := by decide
  have hdescent : baseEnd_3936896 < baseStart_3936896 := by decide
  rcases family_descends (prefixWord ++ tailWord_3936896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3936903 : List Nat := [1, 1, 4, 2, 1, 2, 4, 3, 1, 1, 3]
def baseStart_3936903 : Nat := 118140960795 + 3936903 * 2 ^ 59
def prefixEnd_3936903 : Nat := 4983230072969 + 3 ^ 40 * 3936903 * 2
def baseEnd_3936903 : Nat := 2021523529127715582607019

theorem tailTrace_3936903 : CollatzResearch.WordTrace tailWord_3936903 prefixEnd_3936903 2021523529127715582607019 := by
  unfold tailWord_3936903
  simp only [CollatzResearch.WordTrace]
  refine ⟨143590648856280275347439363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95727099237520183564959575 143590648856280275347439363)
  ·
    refine ⟨215385973284420413021159045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143590648856280275347439363 215385973284420413021159045)
    ·
      refine ⟨40384869990828827441467321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 215385973284420413021159045 40384869990828827441467321)
      ·
        refine ⟨30288652493121620581100491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40384869990828827441467321 30288652493121620581100491)
        ·
          refine ⟨45432978739682430871650737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30288652493121620581100491 45432978739682430871650737)
          ·
            refine ⟨34074734054761823153738053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45432978739682430871650737 34074734054761823153738053)
            ·
              refine ⟨6389012635267841841325885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34074734054761823153738053 6389012635267841841325885)
              ·
                refine ⟨2395879738225440690497207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6389012635267841841325885 2395879738225440690497207)
                ·
                  refine ⟨3593819607338161035745811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2395879738225440690497207 3593819607338161035745811)
                  ·
                    refine ⟨5390729411007241553618717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3593819607338161035745811 5390729411007241553618717)
                    ·
                      refine ⟨2021523529127715582607019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5390729411007241553618717 2021523529127715582607019)
                      ·
                        rfl

theorem cell23_3936903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 4, 3, 1, 1, 3].length) (baseStart_3936903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3936903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3936903 prefixEnd_3936903 := by exact prefixLift 3936903
  have htrace : WordTrace (prefixWord ++ tailWord_3936903) baseStart_3936903 baseEnd_3936903 := by
    simpa [prefixWord, tailWord_3936903, baseEnd_3936903] using wordTrace_append hprefix tailTrace_3936903
  have hstable : (prefixWord ++ tailWord_3936903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3936903).length < 2 ^ (prefixWord ++ tailWord_3936903).sum := by decide
  have hdescent : baseEnd_3936903 < baseStart_3936903 := by decide
  rcases family_descends (prefixWord ++ tailWord_3936903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3936906 : List Nat := [3, 1, 2, 3, 3, 1, 1, 3, 1, 5]
def baseStart_3936906 : Nat := 118140960795 + 3936906 * 2 ^ 59
def prefixEnd_3936906 : Nat := 4983230072969 + 3 ^ 40 * 3936906 * 2
def baseEnd_3936906 : Nat := 673841689856559690289835

theorem tailTrace_3936906 : CollatzResearch.WordTrace tailWord_3936906 prefixEnd_3936906 673841689856559690289835 := by
  unfold tailWord_3936906
  simp only [CollatzResearch.WordTrace]
  refine ⟨35897689568817351714949643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95727172183512937906532381 35897689568817351714949643)
  ·
    refine ⟨53846534353226027572424465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35897689568817351714949643 53846534353226027572424465)
    ·
      refine ⟨40384900764919520679318349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53846534353226027572424465 40384900764919520679318349)
      ·
        refine ⟨15144337786844820254744381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40384900764919520679318349 15144337786844820254744381)
        ·
          refine ⟨5679126670066807595529143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15144337786844820254744381 5679126670066807595529143)
          ·
            refine ⟨8518690005100211393293715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5679126670066807595529143 8518690005100211393293715)
            ·
              refine ⟨12778035007650317089940573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8518690005100211393293715 12778035007650317089940573)
              ·
                refine ⟨4791763127868868908727715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12778035007650317089940573 4791763127868868908727715)
                ·
                  refine ⟨7187644691803303363091573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4791763127868868908727715 7187644691803303363091573)
                  ·
                    refine ⟨673841689856559690289835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7187644691803303363091573 673841689856559690289835)
                    ·
                      rfl

theorem cell23_3936906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 1, 3, 1, 5].length) (baseStart_3936906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3936906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3936906 prefixEnd_3936906 := by exact prefixLift 3936906
  have htrace : WordTrace (prefixWord ++ tailWord_3936906) baseStart_3936906 baseEnd_3936906 := by
    simpa [prefixWord, tailWord_3936906, baseEnd_3936906] using wordTrace_append hprefix tailTrace_3936906
  have hstable : (prefixWord ++ tailWord_3936906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3936906).length < 2 ^ (prefixWord ++ tailWord_3936906).sum := by decide
  have hdescent : baseEnd_3936906 < baseStart_3936906 := by decide
  rcases family_descends (prefixWord ++ tailWord_3936906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3936919 : List Nat := [1, 1, 3, 3, 2, 1, 3, 1, 4, 4]
def baseStart_3936919 : Nat := 118140960795 + 3936919 * 2 ^ 59
def prefixEnd_3936919 : Nat := 4983230072969 + 3 ^ 40 * 3936919 * 2
def baseEnd_3936919 : Nat := 673843914939395840002315

theorem tailTrace_3936919 : CollatzResearch.WordTrace tailWord_3936919 prefixEnd_3936919 673843914939395840002315 := by
  unfold tailWord_3936919
  simp only [CollatzResearch.WordTrace]
  refine ⟨143591232424222310080021811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95727488282814873386681207 143591232424222310080021811)
  ·
    refine ⟨215386848636333465120032717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143591232424222310080021811 215386848636333465120032717)
    ·
      refine ⟨80770068238625049420012269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 215386848636333465120032717 80770068238625049420012269)
      ·
        refine ⟨30288775589484393532504601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80770068238625049420012269 30288775589484393532504601)
        ·
          refine ⟨22716581692113295149378451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30288775589484393532504601 22716581692113295149378451)
          ·
            refine ⟨34074872538169942724067677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22716581692113295149378451 34074872538169942724067677)
            ·
              refine ⟨12778077201813728521525379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34074872538169942724067677 12778077201813728521525379)
              ·
                refine ⟨19167115802720592782288069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12778077201813728521525379 19167115802720592782288069)
                ·
                  refine ⟨3593834213010111146679013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19167115802720592782288069 3593834213010111146679013)
                  ·
                    refine ⟨673843914939395840002315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3593834213010111146679013 673843914939395840002315)
                    ·
                      rfl

theorem cell23_3936919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 3, 1, 4, 4].length) (baseStart_3936919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3936919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3936919 prefixEnd_3936919 := by exact prefixLift 3936919
  have htrace : WordTrace (prefixWord ++ tailWord_3936919) baseStart_3936919 baseEnd_3936919 := by
    simpa [prefixWord, tailWord_3936919, baseEnd_3936919] using wordTrace_append hprefix tailTrace_3936919
  have hstable : (prefixWord ++ tailWord_3936919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3936919).length < 2 ^ (prefixWord ++ tailWord_3936919).sum := by decide
  have hdescent : baseEnd_3936919 < baseStart_3936919 := by decide
  rcases family_descends (prefixWord ++ tailWord_3936919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3936932 : List Nat := [2, 3, 1, 2, 2, 1, 2, 10]
def baseStart_3936932 : Nat := 118140960795 + 3936932 * 2 ^ 59
def prefixEnd_3936932 : Nat := 4983230072969 + 3 ^ 40 * 3936932 * 2
def baseEnd_3936932 : Nat := 74871793335803554412755

theorem tailTrace_3936932 : CollatzResearch.WordTrace tailWord_3936932 prefixEnd_3936932 74871793335803554412755 := by
  unfold tailWord_3936932
  simp only [CollatzResearch.WordTrace]
  refine ⟨71795853286587606650122525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95727804382116808866830033 71795853286587606650122525)
  ·
    refine ⟨26923444982470352493795947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71795853286587606650122525 26923444982470352493795947)
    ·
      refine ⟨40385167473705528740693921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26923444982470352493795947 40385167473705528740693921)
      ·
        refine ⟨30288875605279146555520441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40385167473705528740693921 30288875605279146555520441)
        ·
          refine ⟨22716656703959359916640331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30288875605279146555520441 22716656703959359916640331)
          ·
            refine ⟨34074985055939039874960497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22716656703959359916640331 34074985055939039874960497)
            ·
              refine ⟨25556238791954279906220373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34074985055939039874960497 25556238791954279906220373)
              ·
                refine ⟨74871793335803554412755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 25556238791954279906220373 74871793335803554412755)
                ·
                  rfl

theorem cell23_3936932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 10].length) (baseStart_3936932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3936932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3936932 prefixEnd_3936932 := by exact prefixLift 3936932
  have htrace : WordTrace (prefixWord ++ tailWord_3936932) baseStart_3936932 baseEnd_3936932 := by
    simpa [prefixWord, tailWord_3936932, baseEnd_3936932] using wordTrace_append hprefix tailTrace_3936932
  have hstable : (prefixWord ++ tailWord_3936932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3936932).length < 2 ^ (prefixWord ++ tailWord_3936932).sum := by decide
  have hdescent : baseEnd_3936932 < baseStart_3936932 := by decide
  rcases family_descends (prefixWord ++ tailWord_3936932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3936949 : List Nat := [1, 3, 3, 3, 1, 2, 1, 9]
def baseStart_3936949 : Nat := 118140960795 + 3936949 * 2 ^ 59
def prefixEnd_3936949 : Nat := 4983230072969 + 3 ^ 40 * 3936949 * 2
def baseEnd_3936949 : Nat := 74872116638437866764141

theorem tailTrace_3936949 : CollatzResearch.WordTrace tailWord_3936949 prefixEnd_3936949 74872116638437866764141 := by
  unfold tailWord_3936949
  simp only [CollatzResearch.WordTrace]
  refine ⟨143592326614113625203613901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95728217742742416802409267 143592326614113625203613901)
  ·
    refine ⟨53847122480292609451355213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143592326614113625203613901 53847122480292609451355213)
    ·
      refine ⟨20192670930109728544258205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53847122480292609451355213 20192670930109728544258205)
      ·
        refine ⟨7572251598791148204096827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20192670930109728544258205 7572251598791148204096827)
        ·
          refine ⟨11358377398186722306145241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7572251598791148204096827 11358377398186722306145241)
          ·
            refine ⟨8518783048640041729608931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11358377398186722306145241 8518783048640041729608931)
            ·
              refine ⟨12778174572960062594413397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8518783048640041729608931 12778174572960062594413397)
              ·
                refine ⟨74872116638437866764141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 12778174572960062594413397 74872116638437866764141)
                ·
                  rfl

theorem cell23_3936949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 1, 9].length) (baseStart_3936949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3936949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3936949 prefixEnd_3936949 := by exact prefixLift 3936949
  have htrace : WordTrace (prefixWord ++ tailWord_3936949) baseStart_3936949 baseEnd_3936949 := by
    simpa [prefixWord, tailWord_3936949, baseEnd_3936949] using wordTrace_append hprefix tailTrace_3936949
  have hstable : (prefixWord ++ tailWord_3936949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3936949).length < 2 ^ (prefixWord ++ tailWord_3936949).sum := by decide
  have hdescent : baseEnd_3936949 < baseStart_3936949 := by decide
  rcases family_descends (prefixWord ++ tailWord_3936949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3936960 : List Nat := [2, 1, 1, 2, 4, 2, 3, 3, 1, 2, 2]
def baseStart_3936960 : Nat := 118140960795 + 3936960 * 2 ^ 59
def prefixEnd_3936960 : Nat := 4983230072969 + 3 ^ 40 * 3936960 * 2
def baseEnd_3936960 : Nat := 2021552797525021859594257

theorem tailTrace_3936960 : CollatzResearch.WordTrace tailWord_3936960 prefixEnd_3936960 2021552797525021859594257 := by
  unfold tailWord_3936960
  simp only [CollatzResearch.WordTrace]
  refine ⟨71796363908536887041132167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95728485211382516054842889 71796363908536887041132167)
  ·
    refine ⟨107694545862805330561698251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71796363908536887041132167 107694545862805330561698251)
    ·
      refine ⟨161541818794207995842547377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107694545862805330561698251 161541818794207995842547377)
      ·
        refine ⟨121156364095655996881910533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161541818794207995842547377 121156364095655996881910533)
        ·
          refine ⟨22716818267935499415358225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 121156364095655996881910533 22716818267935499415358225)
          ·
            refine ⟨17037613700951624561518669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22716818267935499415358225 17037613700951624561518669)
            ·
              refine ⟨6389105137856859210569501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17037613700951624561518669 6389105137856859210569501)
              ·
                refine ⟨2395914426696322203963563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6389105137856859210569501 2395914426696322203963563)
                ·
                  refine ⟨3593871640044483305945345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2395914426696322203963563 3593871640044483305945345)
                  ·
                    refine ⟨2695403730033362479459009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3593871640044483305945345 2695403730033362479459009)
                    ·
                      refine ⟨2021552797525021859594257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2695403730033362479459009 2021552797525021859594257)
                      ·
                        rfl

theorem cell23_3936960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 3, 3, 1, 2, 2].length) (baseStart_3936960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3936960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3936960 prefixEnd_3936960 := by exact prefixLift 3936960
  have htrace : WordTrace (prefixWord ++ tailWord_3936960) baseStart_3936960 baseEnd_3936960 := by
    simpa [prefixWord, tailWord_3936960, baseEnd_3936960] using wordTrace_append hprefix tailTrace_3936960
  have hstable : (prefixWord ++ tailWord_3936960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3936960).length < 2 ^ (prefixWord ++ tailWord_3936960).sum := by decide
  have hdescent : baseEnd_3936960 < baseStart_3936960 := by decide
  rcases family_descends (prefixWord ++ tailWord_3936960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3936986 : List Nat := [3, 1, 1, 2, 2, 2, 2, 2, 3, 3, 2]
def baseStart_3936986 : Nat := 118140960795 + 3936986 * 2 ^ 59
def prefixEnd_3936986 : Nat := 4983230072969 + 3 ^ 40 * 3936986 * 2
def baseEnd_3936986 : Nat := 2021566148022038757869137

theorem tailTrace_3936986 : CollatzResearch.WordTrace tailWord_3936986 prefixEnd_3936986 2021566148022038757869137 := by
  unfold tailWord_3936986
  simp only [CollatzResearch.WordTrace]
  refine ⟨35898419028744895130677703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95729117409986387015140541 35898419028744895130677703)
  ·
    refine ⟨53847628543117342696016555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35898419028744895130677703 53847628543117342696016555)
    ·
      refine ⟨80771442814676014044024833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53847628543117342696016555 80771442814676014044024833)
      ·
        refine ⟨60578582111007010533018625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80771442814676014044024833 60578582111007010533018625)
        ·
          refine ⟨45433936583255257899763969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60578582111007010533018625 45433936583255257899763969)
          ·
            refine ⟨34075452437441443424822977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45433936583255257899763969 34075452437441443424822977)
            ·
              refine ⟨25556589328081082568617233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34075452437441443424822977 25556589328081082568617233)
              ·
                refine ⟨19167441996060811926462925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25556589328081082568617233 19167441996060811926462925)
                ·
                  refine ⟨7187790748522804472423597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19167441996060811926462925 7187790748522804472423597)
                  ·
                    refine ⟨2695421530696051677158849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7187790748522804472423597 2695421530696051677158849)
                    ·
                      refine ⟨2021566148022038757869137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2695421530696051677158849 2021566148022038757869137)
                      ·
                        rfl

theorem cell23_3936986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 2, 3, 3, 2].length) (baseStart_3936986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3936986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3936986 prefixEnd_3936986 := by exact prefixLift 3936986
  have htrace : WordTrace (prefixWord ++ tailWord_3936986) baseStart_3936986 baseEnd_3936986 := by
    simpa [prefixWord, tailWord_3936986, baseEnd_3936986] using wordTrace_append hprefix tailTrace_3936986
  have hstable : (prefixWord ++ tailWord_3936986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3936986).length < 2 ^ (prefixWord ++ tailWord_3936986).sum := by decide
  have hdescent : baseEnd_3936986 < baseStart_3936986 := by decide
  rcases family_descends (prefixWord ++ tailWord_3936986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3936992 : List Nat := [2, 1, 1, 3, 1, 2, 1, 3, 1, 8]
def baseStart_3936992 : Nat := 118140960795 + 3936992 * 2 ^ 59
def prefixEnd_3936992 : Nat := 4983230072969 + 3 ^ 40 * 3936992 * 2
def baseEnd_3936992 : Nat := 673856409635321911464703

theorem tailTrace_3936992 : CollatzResearch.WordTrace tailWord_3936992 prefixEnd_3936992 673856409635321911464703 := by
  unfold tailWord_3936992
  simp only [CollatzResearch.WordTrace]
  refine ⟨71796947476478921773714615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95729263301971895698286153 71796947476478921773714615)
  ·
    refine ⟨107695421214718382660571923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71796947476478921773714615 107695421214718382660571923)
    ·
      refine ⟨161543131822077573990857885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107695421214718382660571923 161543131822077573990857885)
      ·
        refine ⟨60578674433279090246571707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 161543131822077573990857885 60578674433279090246571707)
        ·
          refine ⟨90868011649918635369857561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60578674433279090246571707 90868011649918635369857561)
          ·
            refine ⟨68151008737438976527393171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90868011649918635369857561 68151008737438976527393171)
            ·
              refine ⟨102226513106158464791089757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68151008737438976527393171 102226513106158464791089757)
              ·
                refine ⟨38334942414809424296658659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 102226513106158464791089757 38334942414809424296658659)
                ·
                  refine ⟨57502413622214136444987989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38334942414809424296658659 57502413622214136444987989)
                  ·
                    refine ⟨673856409635321911464703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 57502413622214136444987989 673856409635321911464703)
                    ·
                      rfl

theorem cell23_3936992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 3, 1, 8].length) (baseStart_3936992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3936992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3936992 prefixEnd_3936992 := by exact prefixLift 3936992
  have htrace : WordTrace (prefixWord ++ tailWord_3936992) baseStart_3936992 baseEnd_3936992 := by
    simpa [prefixWord, tailWord_3936992, baseEnd_3936992] using wordTrace_append hprefix tailTrace_3936992
  have hstable : (prefixWord ++ tailWord_3936992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3936992).length < 2 ^ (prefixWord ++ tailWord_3936992).sum := by decide
  have hdescent : baseEnd_3936992 < baseStart_3936992 := by decide
  rcases family_descends (prefixWord ++ tailWord_3936992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3936993 : List Nat := [1, 2, 3, 1, 4, 2, 1, 3, 2, 1, 3]
def baseStart_3936993 : Nat := 118140960795 + 3936993 * 2 ^ 59
def prefixEnd_3936993 : Nat := 4983230072969 + 3 ^ 40 * 3936993 * 2
def baseEnd_3936993 : Nat := 2021569742386620230481605

theorem tailTrace_3936993 : CollatzResearch.WordTrace tailWord_3936993 prefixEnd_3936993 2021569742386620230481605 := by
  unfold tailWord_3936993
  simp only [CollatzResearch.WordTrace]
  refine ⟨143593931425954220718215633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95729287617302813812143755 143593931425954220718215633)
  ·
    refine ⟨107695448569465665538661725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143593931425954220718215633 107695448569465665538661725)
    ·
      refine ⟨40385793213549624576998147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107695448569465665538661725 40385793213549624576998147)
      ·
        refine ⟨60578689820324436865497221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40385793213549624576998147 60578689820324436865497221)
        ·
          refine ⟨11358504341310831912280729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60578689820324436865497221 11358504341310831912280729)
          ·
            refine ⟨8518878255983123934210547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11358504341310831912280729 8518878255983123934210547)
            ·
              refine ⟨12778317383974685901315821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8518878255983123934210547 12778317383974685901315821)
              ·
                refine ⟨4791869018990507212993433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12778317383974685901315821 4791869018990507212993433)
                ·
                  refine ⟨3593901764242880409745075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4791869018990507212993433 3593901764242880409745075)
                  ·
                    refine ⟨5390852646364320614617613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3593901764242880409745075 5390852646364320614617613)
                    ·
                      refine ⟨2021569742386620230481605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5390852646364320614617613 2021569742386620230481605)
                      ·
                        rfl

theorem cell23_3936993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 1, 3, 2, 1, 3].length) (baseStart_3936993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3936993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3936993 prefixEnd_3936993 := by exact prefixLift 3936993
  have htrace : WordTrace (prefixWord ++ tailWord_3936993) baseStart_3936993 baseEnd_3936993 := by
    simpa [prefixWord, tailWord_3936993, baseEnd_3936993] using wordTrace_append hprefix tailTrace_3936993
  have hstable : (prefixWord ++ tailWord_3936993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3936993).length < 2 ^ (prefixWord ++ tailWord_3936993).sum := by decide
  have hdescent : baseEnd_3936993 < baseStart_3936993 := by decide
  rcases family_descends (prefixWord ++ tailWord_3936993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3937016 : List Nat := [2, 1, 2, 1, 1, 2, 5, 2, 1, 4, 2]
def baseStart_3937016 : Nat := 118140960795 + 3937016 * 2 ^ 59
def prefixEnd_3937016 : Nat := 4983230072969 + 3 ^ 40 * 3937016 * 2
def baseEnd_3937016 : Nat := 2021581552441673640493999

theorem tailTrace_3937016 : CollatzResearch.WordTrace tailWord_3937016 prefixEnd_3937016 2021581552441673640493999 := by
  unfold tailWord_3937016
  simp only [CollatzResearch.WordTrace]
  refine ⟨71797385152435447823151451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95729846869913930430868601 71797385152435447823151451)
  ·
    refine ⟨107696077728653171734727177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71797385152435447823151451 107696077728653171734727177)
    ·
      refine ⟨80772058296489878801045383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107696077728653171734727177 80772058296489878801045383)
      ·
        refine ⟨121158087444734818201568075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80772058296489878801045383 121158087444734818201568075)
        ·
          refine ⟨181737131167102227302352113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121158087444734818201568075 181737131167102227302352113)
          ·
            refine ⟨136302848375326670476764085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 181737131167102227302352113 136302848375326670476764085)
            ·
              refine ⟨12778392035186875357196633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 136302848375326670476764085 12778392035186875357196633)
              ·
                refine ⟨9583794026390156517897475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12778392035186875357196633 9583794026390156517897475)
                ·
                  refine ⟨14375691039585234776846213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9583794026390156517897475 14375691039585234776846213)
                  ·
                    refine ⟨2695442069922231520658665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14375691039585234776846213 2695442069922231520658665)
                    ·
                      refine ⟨2021581552441673640493999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2695442069922231520658665 2021581552441673640493999)
                      ·
                        rfl

theorem cell23_3937016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5, 2, 1, 4, 2].length) (baseStart_3937016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3937016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3937016 prefixEnd_3937016 := by exact prefixLift 3937016
  have htrace : WordTrace (prefixWord ++ tailWord_3937016) baseStart_3937016 baseEnd_3937016 := by
    simpa [prefixWord, tailWord_3937016, baseEnd_3937016] using wordTrace_append hprefix tailTrace_3937016
  have hstable : (prefixWord ++ tailWord_3937016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3937016).length < 2 ^ (prefixWord ++ tailWord_3937016).sum := by decide
  have hdescent : baseEnd_3937016 < baseStart_3937016 := by decide
  rcases family_descends (prefixWord ++ tailWord_3937016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3937020 : List Nat := [2, 2, 2, 1, 3, 3, 3, 1, 1, 3, 2]
def baseStart_3937020 : Nat := 118140960795 + 3937020 * 2 ^ 59
def prefixEnd_3937020 : Nat := 4983230072969 + 3 ^ 40 * 3937020 * 2
def baseEnd_3937020 : Nat := 2021583606364291624843981

theorem tailTrace_3937020 : CollatzResearch.WordTrace tailWord_3937020 prefixEnd_3937020 2021583606364291624843981 := by
  unfold tailWord_3937020
  simp only [CollatzResearch.WordTrace]
  refine ⟨71797458098428202164724257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95729944131237602886299009 71797458098428202164724257)
  ·
    refine ⟨53848093573821151623543193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71797458098428202164724257 53848093573821151623543193)
    ·
      refine ⟨40386070180365863717657395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53848093573821151623543193 40386070180365863717657395)
      ·
        refine ⟨60579105270548795576486093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40386070180365863717657395 60579105270548795576486093)
        ·
          refine ⟨22717164476455798341182285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60579105270548795576486093 22717164476455798341182285)
          ·
            refine ⟨8518936678670924377943357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22717164476455798341182285 8518936678670924377943357)
            ·
              refine ⟨3194601254501596641728759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8518936678670924377943357 3194601254501596641728759)
              ·
                refine ⟨4791901881752394962593139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3194601254501596641728759 4791901881752394962593139)
                ·
                  refine ⟨7187852822628592443889709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4791901881752394962593139 7187852822628592443889709)
                  ·
                    refine ⟨2695444808485722166458641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7187852822628592443889709 2695444808485722166458641)
                    ·
                      refine ⟨2021583606364291624843981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2695444808485722166458641 2021583606364291624843981)
                      ·
                        rfl

theorem cell23_3937020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 3, 1, 1, 3, 2].length) (baseStart_3937020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3937020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3937020 prefixEnd_3937020 := by exact prefixLift 3937020
  have htrace : WordTrace (prefixWord ++ tailWord_3937020) baseStart_3937020 baseEnd_3937020 := by
    simpa [prefixWord, tailWord_3937020, baseEnd_3937020] using wordTrace_append hprefix tailTrace_3937020
  have hstable : (prefixWord ++ tailWord_3937020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3937020).length < 2 ^ (prefixWord ++ tailWord_3937020).sum := by decide
  have hdescent : baseEnd_3937020 < baseStart_3937020 := by decide
  rcases family_descends (prefixWord ++ tailWord_3937020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3937033 : List Nat := [1, 2, 1, 1, 3, 2, 3, 4, 2, 2, 2]
def baseStart_3937033 : Nat := 118140960795 + 3937033 * 2 ^ 59
def prefixEnd_3937033 : Nat := 4983230072969 + 3 ^ 40 * 3937033 * 2
def baseEnd_3937033 : Nat := 2021590281612800073981421

theorem tailTrace_3937033 : CollatzResearch.WordTrace tailWord_3937033 prefixEnd_3937033 2021590281612800073981421 := by
  unfold tailWord_3937033
  simp only [CollatzResearch.WordTrace]
  refine ⟨143595390345809307549671753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95730260230539538366447835 143595390345809307549671753)
  ·
    refine ⟨107696542759356980662253815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143595390345809307549671753 107696542759356980662253815)
    ·
      refine ⟨161544814139035470993380723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107696542759356980662253815 161544814139035470993380723)
      ·
        refine ⟨242317221208553206490071085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161544814139035470993380723 242317221208553206490071085)
        ·
          refine ⟨90868957953207452433776657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 242317221208553206490071085 90868957953207452433776657)
          ·
            refine ⟨68151718464905589325332493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90868957953207452433776657 68151718464905589325332493)
            ·
              refine ⟨25556894424339595996999685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68151718464905589325332493 25556894424339595996999685)
              ·
                refine ⟨4791917704563674249437441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25556894424339595996999685 4791917704563674249437441)
                ·
                  refine ⟨3593938278422755687078081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4791917704563674249437441 3593938278422755687078081)
                  ·
                    refine ⟨2695453708817066765308561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3593938278422755687078081 2695453708817066765308561)
                    ·
                      refine ⟨2021590281612800073981421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2695453708817066765308561 2021590281612800073981421)
                      ·
                        rfl

theorem cell23_3937033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 4, 2, 2, 2].length) (baseStart_3937033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3937033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3937033 prefixEnd_3937033 := by exact prefixLift 3937033
  have htrace : WordTrace (prefixWord ++ tailWord_3937033) baseStart_3937033 baseEnd_3937033 := by
    simpa [prefixWord, tailWord_3937033, baseEnd_3937033] using wordTrace_append hprefix tailTrace_3937033
  have hstable : (prefixWord ++ tailWord_3937033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3937033).length < 2 ^ (prefixWord ++ tailWord_3937033).sum := by decide
  have hdescent : baseEnd_3937033 < baseStart_3937033 := by decide
  rcases family_descends (prefixWord ++ tailWord_3937033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3937119 : List Nat := [1, 1, 2, 3, 1, 3, 1, 1, 2, 4, 4]
def baseStart_3937119 : Nat := 118140960795 + 3937119 * 2 ^ 59
def prefixEnd_3937119 : Nat := 4983230072969 + 3 ^ 40 * 3937119 * 2
def baseEnd_3937119 : Nat := 2021634440949086737506025

theorem tailTrace_3937119 : CollatzResearch.WordTrace tailWord_3937119 prefixEnd_3937119 2021634440949086737506025 := by
  unfold tailWord_3937119
  simp only [CollatzResearch.WordTrace]
  refine ⟨143598527023497744237302411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95732351348998496158201607 143598527023497744237302411)
  ·
    refine ⟨215397790535246616355953617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143598527023497744237302411 215397790535246616355953617)
    ·
      refine ⟨161548342901434962266965213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215397790535246616355953617 161548342901434962266965213)
      ·
        refine ⟨60580628588038110850111955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 161548342901434962266965213 60580628588038110850111955)
        ·
          refine ⟨90870942882057166275167933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60580628588038110850111955 90870942882057166275167933)
          ·
            refine ⟨34076603580771437353187975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90870942882057166275167933 34076603580771437353187975)
            ·
              refine ⟨51114905371157156029781963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34076603580771437353187975 51114905371157156029781963)
              ·
                refine ⟨76672358056735734044672945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51114905371157156029781963 76672358056735734044672945)
                ·
                  refine ⟨57504268542551800533504709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76672358056735734044672945 57504268542551800533504709)
                  ·
                    refine ⟨10782050351728462600032133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 57504268542551800533504709 10782050351728462600032133)
                    ·
                      refine ⟨2021634440949086737506025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10782050351728462600032133 2021634440949086737506025)
                      ·
                        rfl

theorem cell23_3937119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 1, 2, 4, 4].length) (baseStart_3937119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3937119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3937119 prefixEnd_3937119 := by exact prefixLift 3937119
  have htrace : WordTrace (prefixWord ++ tailWord_3937119) baseStart_3937119 baseEnd_3937119 := by
    simpa [prefixWord, tailWord_3937119, baseEnd_3937119] using wordTrace_append hprefix tailTrace_3937119
  have hstable : (prefixWord ++ tailWord_3937119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3937119).length < 2 ^ (prefixWord ++ tailWord_3937119).sum := by decide
  have hdescent : baseEnd_3937119 < baseStart_3937119 := by decide
  rcases family_descends (prefixWord ++ tailWord_3937119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3937149 : List Nat := [1, 4, 1, 1, 2, 1, 2, 1, 1, 1, 8]
def baseStart_3937149 : Nat := 118140960795 + 3937149 * 2 ^ 59
def prefixEnd_3937149 : Nat := 4983230072969 + 3 ^ 40 * 3937149 * 2
def baseEnd_3937149 : Nat := 2021649845368721620130887

theorem tailTrace_3937149 : CollatzResearch.WordTrace tailWord_3937149 prefixEnd_3937149 2021649845368721620130887 := by
  unfold tailWord_3937149
  simp only [CollatzResearch.WordTrace]
  refine ⟨143599621213389059360894501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95733080808926039573929667 143599621213389059360894501)
  ·
    refine ⟨26924928977510448630167719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 143599621213389059360894501 26924928977510448630167719)
    ·
      refine ⟨40387393466265672945251579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26924928977510448630167719 40387393466265672945251579)
      ·
        refine ⟨60581090199398509417877369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40387393466265672945251579 60581090199398509417877369)
        ·
          refine ⟨45435817649548882063408027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60581090199398509417877369 45435817649548882063408027)
          ·
            refine ⟨68153726474323323095112041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45435817649548882063408027 68153726474323323095112041)
            ·
              refine ⟨51115294855742492321334031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68153726474323323095112041 51115294855742492321334031)
              ·
                refine ⟨76672942283613738482001047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51115294855742492321334031 76672942283613738482001047)
                ·
                  refine ⟨115009413425420607723001571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76672942283613738482001047 115009413425420607723001571)
                  ·
                    refine ⟨172514120138130911584502357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 115009413425420607723001571 172514120138130911584502357)
                    ·
                      refine ⟨2021649845368721620130887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 172514120138130911584502357 2021649845368721620130887)
                      ·
                        rfl

theorem cell23_3937149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 1, 1, 1, 8].length) (baseStart_3937149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3937149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3937149 prefixEnd_3937149 := by exact prefixLift 3937149
  have htrace : WordTrace (prefixWord ++ tailWord_3937149) baseStart_3937149 baseEnd_3937149 := by
    simpa [prefixWord, tailWord_3937149, baseEnd_3937149] using wordTrace_append hprefix tailTrace_3937149
  have hstable : (prefixWord ++ tailWord_3937149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3937149).length < 2 ^ (prefixWord ++ tailWord_3937149).sum := by decide
  have hdescent : baseEnd_3937149 < baseStart_3937149 := by decide
  rcases family_descends (prefixWord ++ tailWord_3937149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3937193 : List Nat := [1, 2, 1, 1, 1, 1, 9, 1, 1, 5]
def baseStart_3937193 : Nat := 118140960795 + 3937193 * 2 ^ 59
def prefixEnd_3937193 : Nat := 4983230072969 + 3 ^ 40 * 3937193 * 2
def baseEnd_3937193 : Nat := 673890812839173149326895

theorem tailTrace_3937193 : CollatzResearch.WordTrace tailWord_3937193 prefixEnd_3937193 673890812839173149326895 := by
  unfold tailWord_3937193
  simp only [CollatzResearch.WordTrace]
  refine ⟨143601226025229654875496233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95734150683486436583664155 143601226025229654875496233)
  ·
    refine ⟨107700919518922241156622175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143601226025229654875496233 107700919518922241156622175)
    ·
      refine ⟨161551379278383361734933263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107700919518922241156622175 161551379278383361734933263)
      ·
        refine ⟨242327068917575042602399895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161551379278383361734933263 242327068917575042602399895)
        ·
          refine ⟨363490603376362563903599843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242327068917575042602399895 363490603376362563903599843)
          ·
            refine ⟨545235905064543845855399765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 363490603376362563903599843 545235905064543845855399765)
            ·
              refine ⟨3194741631237561596808983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 545235905064543845855399765 3194741631237561596808983)
              ·
                refine ⟨4792112446856342395213475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3194741631237561596808983 4792112446856342395213475)
                ·
                  refine ⟨7188168670284513592820213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4792112446856342395213475 7188168670284513592820213)
                  ·
                    refine ⟨673890812839173149326895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7188168670284513592820213 673890812839173149326895)
                    ·
                      rfl

theorem cell23_3937193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 9, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 9, 1, 1, 5].length) (baseStart_3937193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3937193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3937193 prefixEnd_3937193 := by exact prefixLift 3937193
  have htrace : WordTrace (prefixWord ++ tailWord_3937193) baseStart_3937193 baseEnd_3937193 := by
    simpa [prefixWord, tailWord_3937193, baseEnd_3937193] using wordTrace_append hprefix tailTrace_3937193
  have hstable : (prefixWord ++ tailWord_3937193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3937193).length < 2 ^ (prefixWord ++ tailWord_3937193).sum := by decide
  have hdescent : baseEnd_3937193 < baseStart_3937193 := by decide
  rcases family_descends (prefixWord ++ tailWord_3937193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3937207 : List Nat := [1, 1, 3, 1, 3, 1, 6, 2, 1, 1, 3]
def baseStart_3937207 : Nat := 118140960795 + 3937207 * 2 ^ 59
def prefixEnd_3937207 : Nat := 4983230072969 + 3 ^ 40 * 3937207 * 2
def baseEnd_3937207 : Nat := 2021679627246682393205621

theorem tailTrace_3937207 : CollatzResearch.WordTrace tailWord_3937207 prefixEnd_3937207 2021679627246682393205621 := by
  unfold tailWord_3937207
  simp only [CollatzResearch.WordTrace]
  refine ⟨143601736647178935266505875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95734491098119290177670583 143601736647178935266505875)
  ·
    refine ⟨215402604970768402899758813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143601736647178935266505875 215402604970768402899758813)
    ·
      refine ⟨80775976864038151087409555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 215402604970768402899758813 80775976864038151087409555)
      ·
        refine ⟨121163965296057226631114333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80775976864038151087409555 121163965296057226631114333)
        ·
          refine ⟨45436486986021459986667875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121163965296057226631114333 45436486986021459986667875)
          ·
            refine ⟨68154730479032189980001813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45436486986021459986667875 68154730479032189980001813)
            ·
              refine ⟨3194752991204633905312585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 68154730479032189980001813 3194752991204633905312585)
              ·
                refine ⟨2396064743403475428984439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3194752991204633905312585 2396064743403475428984439)
                ·
                  refine ⟨3594097115105213143476659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2396064743403475428984439 3594097115105213143476659)
                  ·
                    refine ⟨5391145672657819715214989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3594097115105213143476659 5391145672657819715214989)
                    ·
                      refine ⟨2021679627246682393205621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5391145672657819715214989 2021679627246682393205621)
                      ·
                        rfl

theorem cell23_3937207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 6, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 6, 2, 1, 1, 3].length) (baseStart_3937207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3937207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3937207 prefixEnd_3937207 := by exact prefixLift 3937207
  have htrace : WordTrace (prefixWord ++ tailWord_3937207) baseStart_3937207 baseEnd_3937207 := by
    simpa [prefixWord, tailWord_3937207, baseEnd_3937207] using wordTrace_append hprefix tailTrace_3937207
  have hstable : (prefixWord ++ tailWord_3937207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3937207).length < 2 ^ (prefixWord ++ tailWord_3937207).sum := by decide
  have hdescent : baseEnd_3937207 < baseStart_3937207 := by decide
  rcases family_descends (prefixWord ++ tailWord_3937207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3937223 : List Nat := [1, 1, 4, 1, 1, 2, 4, 3, 2, 4]
def baseStart_3937223 : Nat := 118140960795 + 3937223 * 2 ^ 59
def prefixEnd_3937223 : Nat := 4983230072969 + 3 ^ 40 * 3937223 * 2
def baseEnd_3937223 : Nat := 673895947645718110201849

theorem tailTrace_3937223 : CollatzResearch.WordTrace tailWord_3937223 prefixEnd_3937223 673895947645718110201849 := by
  unfold tailWord_3937223
  simp only [CollatzResearch.WordTrace]
  refine ⟨143602320215120969999088323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95734880143413979999392215 143602320215120969999088323)
  ·
    refine ⟨215403480322681454998632485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143602320215120969999088323 215403480322681454998632485)
    ·
      refine ⟨40388152560502772812243591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 215403480322681454998632485 40388152560502772812243591)
      ·
        refine ⟨60582228840754159218365387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40388152560502772812243591 60582228840754159218365387)
        ·
          refine ⟨90873343261131238827548081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60582228840754159218365387 90873343261131238827548081)
          ·
            refine ⟨68155007445848429120661061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90873343261131238827548081 68155007445848429120661061)
            ·
              refine ⟨12779063896096580460123949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68155007445848429120661061 12779063896096580460123949)
              ·
                refine ⟨4792148961036217672546481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12779063896096580460123949 4792148961036217672546481)
                ·
                  refine ⟨3594111720777163254409861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4792148961036217672546481 3594111720777163254409861)
                  ·
                    refine ⟨673895947645718110201849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3594111720777163254409861 673895947645718110201849)
                    ·
                      rfl

theorem cell23_3937223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4, 3, 2, 4].length) (baseStart_3937223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3937223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3937223 prefixEnd_3937223 := by exact prefixLift 3937223
  have htrace : WordTrace (prefixWord ++ tailWord_3937223) baseStart_3937223 baseEnd_3937223 := by
    simpa [prefixWord, tailWord_3937223, baseEnd_3937223] using wordTrace_append hprefix tailTrace_3937223
  have hstable : (prefixWord ++ tailWord_3937223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3937223).length < 2 ^ (prefixWord ++ tailWord_3937223).sum := by decide
  have hdescent : baseEnd_3937223 < baseStart_3937223 := by decide
  rcases family_descends (prefixWord ++ tailWord_3937223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3937230 : List Nat := [4, 1, 1, 1, 2, 3, 1, 1, 5, 2, 2]
def baseStart_3937230 : Nat := 118140960795 + 3937230 * 2 ^ 59
def prefixEnd_3937230 : Nat := 4983230072969 + 3 ^ 40 * 3937230 * 2
def baseEnd_3937230 : Nat := 2021691437301735803218015

theorem tailTrace_3937230 : CollatzResearch.WordTrace tailWord_3937230 prefixEnd_3937230 2021691437301735803218015 := by
  unfold tailWord_3937230
  simp only [CollatzResearch.WordTrace]
  refine ⟨17950321940761951274324143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95735050350730406796395429 17950321940761951274324143)
  ·
    refine ⟨26925482911142926911486215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17950321940761951274324143 26925482911142926911486215)
    ·
      refine ⟨40388224366714390367229323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26925482911142926911486215 40388224366714390367229323)
      ·
        refine ⟨60582336550071585550843985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40388224366714390367229323 60582336550071585550843985)
        ·
          refine ⟨45436752412553689163132989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60582336550071585550843985 45436752412553689163132989)
          ·
            refine ⟨17038782154707633436174871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45436752412553689163132989 17038782154707633436174871)
            ·
              refine ⟨25558173232061450154262307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17038782154707633436174871 25558173232061450154262307)
              ·
                refine ⟨38337259848092175231393461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25558173232061450154262307 38337259848092175231393461)
                ·
                  refine ⟨3594118110758641427943137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38337259848092175231393461 3594118110758641427943137)
                  ·
                    refine ⟨2695588583068981070957353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3594118110758641427943137 2695588583068981070957353)
                    ·
                      refine ⟨2021691437301735803218015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2695588583068981070957353 2021691437301735803218015)
                      ·
                        rfl

theorem cell23_3937230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 1, 5, 2, 2].length) (baseStart_3937230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3937230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3937230 prefixEnd_3937230 := by exact prefixLift 3937230
  have htrace : WordTrace (prefixWord ++ tailWord_3937230) baseStart_3937230 baseEnd_3937230 := by
    simpa [prefixWord, tailWord_3937230, baseEnd_3937230] using wordTrace_append hprefix tailTrace_3937230
  have hstable : (prefixWord ++ tailWord_3937230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3937230).length < 2 ^ (prefixWord ++ tailWord_3937230).sum := by decide
  have hdescent : baseEnd_3937230 < baseStart_3937230 := by decide
  rcases family_descends (prefixWord ++ tailWord_3937230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3937233 : List Nat := [1, 2, 2, 1, 2, 1, 4, 4, 1, 2, 3]
def baseStart_3937233 : Nat := 118140960795 + 3937233 * 2 ^ 59
def prefixEnd_3937233 : Nat := 4983230072969 + 3 ^ 40 * 3937233 * 2
def baseEnd_3937233 : Nat := 2021692977743699291480501

theorem tailTrace_3937233 : CollatzResearch.WordTrace tailWord_3937233 prefixEnd_3937233 2021692977743699291480501 := by
  unfold tailWord_3937233
  simp only [CollatzResearch.WordTrace]
  refine ⟨143602684945084741706952353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95735123296723161137968235 143602684945084741706952353)
  ·
    refine ⟨107702013708813556280214265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143602684945084741706952353 107702013708813556280214265)
    ·
      refine ⟨80776510281610167210160699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107702013708813556280214265 80776510281610167210160699)
      ·
        refine ⟨121164765422415250815241049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80776510281610167210160699 121164765422415250815241049)
        ·
          refine ⟨90873574066811438111430787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121164765422415250815241049 90873574066811438111430787)
          ·
            refine ⟨136310361100217157167146181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90873574066811438111430787 136310361100217157167146181)
            ·
              refine ⟨25558192706290716968839909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 136310361100217157167146181 25558192706290716968839909)
              ·
                refine ⟨4792161132429509431657483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25558192706290716968839909 4792161132429509431657483)
                ·
                  refine ⟨7188241698644264147486225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4792161132429509431657483 7188241698644264147486225)
                  ·
                    refine ⟨5391181273983198110614669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7188241698644264147486225 5391181273983198110614669)
                    ·
                      refine ⟨2021692977743699291480501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5391181273983198110614669 2021692977743699291480501)
                      ·
                        rfl

theorem cell23_3937233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 4, 1, 2, 3].length) (baseStart_3937233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3937233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3937233 prefixEnd_3937233 := by exact prefixLift 3937233
  have htrace : WordTrace (prefixWord ++ tailWord_3937233) baseStart_3937233 baseEnd_3937233 := by
    simpa [prefixWord, tailWord_3937233, baseEnd_3937233] using wordTrace_append hprefix tailTrace_3937233
  have hstable : (prefixWord ++ tailWord_3937233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3937233).length < 2 ^ (prefixWord ++ tailWord_3937233).sum := by decide
  have hdescent : baseEnd_3937233 < baseStart_3937233 := by decide
  rcases family_descends (prefixWord ++ tailWord_3937233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3937247 : List Nat := [1, 1, 2, 3, 5, 2, 2, 1, 1, 1, 4]
def baseStart_3937247 : Nat := 118140960795 + 3937247 * 2 ^ 59
def prefixEnd_3937247 : Nat := 4983230072969 + 3 ^ 40 * 3937247 * 2
def baseEnd_3937247 : Nat := 2021700166472862236705437

theorem tailTrace_3937247 : CollatzResearch.WordTrace tailWord_3937247 prefixEnd_3937247 2021700166472862236705437 := by
  unfold tailWord_3937247
  simp only [CollatzResearch.WordTrace]
  refine ⟨143603195567034022097961995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95735463711356014731974663 143603195567034022097961995)
  ·
    refine ⟨215404793350551033146942993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143603195567034022097961995 215404793350551033146942993)
    ·
      refine ⟨161553595012913274860207245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215404793350551033146942993 161553595012913274860207245)
      ·
        refine ⟨60582598129842478072577717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 161553595012913274860207245 60582598129842478072577717)
        ·
          refine ⟨5679618574672732319304161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 60582598129842478072577717 5679618574672732319304161)
          ·
            refine ⟨4259713931004549239478121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5679618574672732319304161 4259713931004549239478121)
            ·
              refine ⟨3194785448253411929608591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4259713931004549239478121 3194785448253411929608591)
              ·
                refine ⟨4792178172380117894412887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3194785448253411929608591 4792178172380117894412887)
                ·
                  refine ⟨7188267258570176841619331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4792178172380117894412887 7188267258570176841619331)
                  ·
                    refine ⟨10782400887855265262428997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7188267258570176841619331 10782400887855265262428997)
                    ·
                      refine ⟨2021700166472862236705437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10782400887855265262428997 2021700166472862236705437)
                      ·
                        rfl

theorem cell23_3937247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 2, 1, 1, 1, 4].length) (baseStart_3937247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3937247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3937247 prefixEnd_3937247 := by exact prefixLift 3937247
  have htrace : WordTrace (prefixWord ++ tailWord_3937247) baseStart_3937247 baseEnd_3937247 := by
    simpa [prefixWord, tailWord_3937247, baseEnd_3937247] using wordTrace_append hprefix tailTrace_3937247
  have hstable : (prefixWord ++ tailWord_3937247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3937247).length < 2 ^ (prefixWord ++ tailWord_3937247).sum := by decide
  have hdescent : baseEnd_3937247 < baseStart_3937247 := by decide
  rcases family_descends (prefixWord ++ tailWord_3937247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3937253 : List Nat := [1, 3, 1, 6, 1, 1, 10]
def baseStart_3937253 : Nat := 118140960795 + 3937253 * 2 ^ 59
def prefixEnd_3937253 : Nat := 4983230072969 + 3 ^ 40 * 3937253 * 2
def baseEnd_3937253 : Nat := 24959299350083817447289

theorem tailTrace_3937253 : CollatzResearch.WordTrace tailWord_3937253 prefixEnd_3937253 24959299350083817447289 := by
  unfold tailWord_3937253
  simp only [CollatzResearch.WordTrace]
  refine ⟨143603414405012285122680413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95735609603341523415120275 143603414405012285122680413)
  ·
    refine ⟨53851280401879606921005155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143603414405012285122680413 53851280401879606921005155)
    ·
      refine ⟨80776920602819410381507733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53851280401879606921005155 80776920602819410381507733)
      ·
        refine ⟨3786418153257159861633175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 80776920602819410381507733 3786418153257159861633175)
        ·
          refine ⟨5679627229885739792449763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3786418153257159861633175 5679627229885739792449763)
          ·
            refine ⟨8519440844828609688674645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5679627229885739792449763 8519440844828609688674645)
            ·
              refine ⟨24959299350083817447289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 8519440844828609688674645 24959299350083817447289)
              ·
                rfl

theorem cell23_3937253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 10].length) (baseStart_3937253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3937253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3937253 prefixEnd_3937253 := by exact prefixLift 3937253
  have htrace : WordTrace (prefixWord ++ tailWord_3937253) baseStart_3937253 baseEnd_3937253 := by
    simpa [prefixWord, tailWord_3937253, baseEnd_3937253] using wordTrace_append hprefix tailTrace_3937253
  have hstable : (prefixWord ++ tailWord_3937253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3937253).length < 2 ^ (prefixWord ++ tailWord_3937253).sum := by decide
  have hdescent : baseEnd_3937253 < baseStart_3937253 := by decide
  rcases family_descends (prefixWord ++ tailWord_3937253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3937363 : List Nat := [1, 1, 1, 2, 1, 1, 2, 4, 1, 7, 2]
def baseStart_3937363 : Nat := 118140960795 + 3937363 * 2 ^ 59
def prefixEnd_3937363 : Nat := 4983230072969 + 3 ^ 40 * 3937363 * 2
def baseEnd_3937363 : Nat := 2021759730228783782854903

theorem tailTrace_3937363 : CollatzResearch.WordTrace tailWord_3937363 prefixEnd_3937363 2021759730228783782854903 := by
  unfold tailWord_3937363
  simp only [CollatzResearch.WordTrace]
  refine ⟨143607426434613773909184743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95738284289742515939456495 143607426434613773909184743)
  ·
    refine ⟨215411139651920660863777115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143607426434613773909184743 215411139651920660863777115)
    ·
      refine ⟨323116709477880991295665673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215411139651920660863777115 323116709477880991295665673)
      ·
        refine ⟨242337532108410743471749255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 323116709477880991295665673 242337532108410743471749255)
        ·
          refine ⟨363506298162616115207623883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242337532108410743471749255 363506298162616115207623883)
          ·
            refine ⟨545259447243924172811435825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 363506298162616115207623883 545259447243924172811435825)
            ·
              refine ⟨408944585432943129608576869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 545259447243924172811435825 408944585432943129608576869)
              ·
                refine ⟨76677109768676836801608163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 408944585432943129608576869 76677109768676836801608163)
                ·
                  refine ⟨115015664653015255202412245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76677109768676836801608163 115015664653015255202412245)
                  ·
                    refine ⟨2695679640305045043806537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 115015664653015255202412245 2695679640305045043806537)
                    ·
                      refine ⟨2021759730228783782854903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2695679640305045043806537 2021759730228783782854903)
                      ·
                        rfl

theorem cell23_3937363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 4, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 4, 1, 7, 2].length) (baseStart_3937363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3937363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3937363 prefixEnd_3937363 := by exact prefixLift 3937363
  have htrace : WordTrace (prefixWord ++ tailWord_3937363) baseStart_3937363 baseEnd_3937363 := by
    simpa [prefixWord, tailWord_3937363, baseEnd_3937363] using wordTrace_append hprefix tailTrace_3937363
  have hstable : (prefixWord ++ tailWord_3937363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3937363).length < 2 ^ (prefixWord ++ tailWord_3937363).sum := by decide
  have hdescent : baseEnd_3937363 < baseStart_3937363 := by decide
  rcases family_descends (prefixWord ++ tailWord_3937363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3937383 : List Nat := [1, 1, 5, 1, 1, 3, 2, 1, 1, 2, 5]
def baseStart_3937383 : Nat := 118140960795 + 3937383 * 2 ^ 59
def prefixEnd_3937383 : Nat := 4983230072969 + 3 ^ 40 * 3937383 * 2
def baseEnd_3937383 : Nat := 2021769999841873704604811

theorem tailTrace_3937383 : CollatzResearch.WordTrace tailWord_3937383 prefixEnd_3937383 2021769999841873704604811 := by
  unfold tailWord_3937383
  simp only [CollatzResearch.WordTrace]
  refine ⟨143608155894541317324912803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95738770596360878216608535 143608155894541317324912803)
  ·
    refine ⟨215412233841811975987369205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143608155894541317324912803 215412233841811975987369205)
    ·
      refine ⟨20194896922669872748815863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 215412233841811975987369205 20194896922669872748815863)
      ·
        refine ⟨30292345384004809123223795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20194896922669872748815863 30292345384004809123223795)
        ·
          refine ⟨45438518076007213684835693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30292345384004809123223795 45438518076007213684835693)
          ·
            refine ⟨17039444278502705131813385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45438518076007213684835693 17039444278502705131813385)
            ·
              refine ⟨12779583208877028848860039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17039444278502705131813385 12779583208877028848860039)
              ·
                refine ⟨19169374813315543273290059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12779583208877028848860039 19169374813315543273290059)
                ·
                  refine ⟨28754062219973314909935089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19169374813315543273290059 28754062219973314909935089)
                  ·
                    refine ⟨21565546664979986182451317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28754062219973314909935089 21565546664979986182451317)
                    ·
                      refine ⟨2021769999841873704604811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21565546664979986182451317 2021769999841873704604811)
                      ·
                        rfl

theorem cell23_3937383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 2, 1, 1, 2, 5].length) (baseStart_3937383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3937383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3937383 prefixEnd_3937383 := by exact prefixLift 3937383
  have htrace : WordTrace (prefixWord ++ tailWord_3937383) baseStart_3937383 baseEnd_3937383 := by
    simpa [prefixWord, tailWord_3937383, baseEnd_3937383] using wordTrace_append hprefix tailTrace_3937383
  have hstable : (prefixWord ++ tailWord_3937383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3937383).length < 2 ^ (prefixWord ++ tailWord_3937383).sum := by decide
  have hdescent : baseEnd_3937383 < baseStart_3937383 := by decide
  rcases family_descends (prefixWord ++ tailWord_3937383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3937437 : List Nat := [1, 4, 2, 1, 1, 2, 1, 6, 1, 4]
def baseStart_3937437 : Nat := 118140960795 + 3937437 * 2 ^ 59
def prefixEnd_3937437 : Nat := 4983230072969 + 3 ^ 40 * 3937437 * 2
def baseEnd_3937437 : Nat := 673932575932405497776521

theorem tailTrace_3937437 : CollatzResearch.WordTrace tailWord_3937437 prefixEnd_3937437 673932575932405497776521 := by
  unfold tailWord_3937437
  simp only [CollatzResearch.WordTrace]
  refine ⟨143610125436345684547378565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95740083624230456364919043 143610125436345684547378565)
  ·
    refine ⟨26926898519314815852633481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 143610125436345684547378565 26926898519314815852633481)
    ·
      refine ⟨20195173889486111889475111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26926898519314815852633481 20195173889486111889475111)
      ·
        refine ⟨30292760834229167834212667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20195173889486111889475111 30292760834229167834212667)
        ·
          refine ⟨45439141251343751751319001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30292760834229167834212667 45439141251343751751319001)
          ·
            refine ⟨34079355938507813813489251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45439141251343751751319001 34079355938507813813489251)
            ·
              refine ⟨51119033907761720720233877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34079355938507813813489251 51119033907761720720233877)
              ·
                refine ⟨2396204714426330658760963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 51119033907761720720233877 2396204714426330658760963)
                ·
                  refine ⟨3594307071639495988141445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2396204714426330658760963 3594307071639495988141445)
                  ·
                    refine ⟨673932575932405497776521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3594307071639495988141445 673932575932405497776521)
                    ·
                      rfl

theorem cell23_3937437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 6, 1, 4].length) (baseStart_3937437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3937437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3937437 prefixEnd_3937437 := by exact prefixLift 3937437
  have htrace : WordTrace (prefixWord ++ tailWord_3937437) baseStart_3937437 baseEnd_3937437 := by
    simpa [prefixWord, tailWord_3937437, baseEnd_3937437] using wordTrace_append hprefix tailTrace_3937437
  have hstable : (prefixWord ++ tailWord_3937437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3937437).length < 2 ^ (prefixWord ++ tailWord_3937437).sum := by decide
  have hdescent : baseEnd_3937437 < baseStart_3937437 := by decide
  rcases family_descends (prefixWord ++ tailWord_3937437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3937480 : List Nat := [2, 1, 3, 1, 2, 1, 4, 3, 1, 5]
def baseStart_3937480 : Nat := 118140960795 + 3937480 * 2 ^ 59
def prefixEnd_3937480 : Nat := 4983230072969 + 3 ^ 40 * 3937480 * 2
def baseEnd_3937480 : Nat := 673939935821786608363955

theorem tailTrace_3937480 : CollatzResearch.WordTrace tailWord_3937480 prefixEnd_3937480 673939935821786608363955 := by
  unfold tailWord_3937480
  simp only [CollatzResearch.WordTrace]
  refine ⟨71805846887594951445596947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95741129183459935260795929 71805846887594951445596947)
  ·
    refine ⟨107708770331392427168395421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71805846887594951445596947 107708770331392427168395421)
    ·
      refine ⟨40390788874272160188148283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107708770331392427168395421 40390788874272160188148283)
      ·
        refine ⟨60586183311408240282222425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40390788874272160188148283 60586183311408240282222425)
        ·
          refine ⟨45439637483556180211666819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60586183311408240282222425 45439637483556180211666819)
          ·
            refine ⟨68159456225334270317500229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45439637483556180211666819 68159456225334270317500229)
            ·
              refine ⟨12779898042250175684531293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68159456225334270317500229 12779898042250175684531293)
              ·
                refine ⟨4792461765843815881699235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12779898042250175684531293 4792461765843815881699235)
                ·
                  refine ⟨7188692648765723822548853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4792461765843815881699235 7188692648765723822548853)
                  ·
                    refine ⟨673939935821786608363955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7188692648765723822548853 673939935821786608363955)
                    ·
                      rfl

theorem cell23_3937480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4, 3, 1, 5].length) (baseStart_3937480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3937480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3937480 prefixEnd_3937480 := by exact prefixLift 3937480
  have htrace : WordTrace (prefixWord ++ tailWord_3937480) baseStart_3937480 baseEnd_3937480 := by
    simpa [prefixWord, tailWord_3937480, baseEnd_3937480] using wordTrace_append hprefix tailTrace_3937480
  have hstable : (prefixWord ++ tailWord_3937480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3937480).length < 2 ^ (prefixWord ++ tailWord_3937480).sum := by decide
  have hdescent : baseEnd_3937480 < baseStart_3937480 := by decide
  rcases family_descends (prefixWord ++ tailWord_3937480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3937501 : List Nat := [1, 4, 3, 2, 3, 1, 2, 1, 6]
def baseStart_3937501 : Nat := 118140960795 + 3937501 * 2 ^ 59
def prefixEnd_3937501 : Nat := 4983230072969 + 3 ^ 40 * 3937501 * 2
def baseEnd_3937501 : Nat := 224647843395456026992141

theorem tailTrace_3937501 : CollatzResearch.WordTrace tailWord_3937501 prefixEnd_3937501 224647843395456026992141 := by
  unfold tailWord_3937501
  simp only [CollatzResearch.WordTrace]
  refine ⟨143612459708113823477708357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95741639805409215651805571 143612459708113823477708357)
  ·
    refine ⟨26927336195271341902070317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 143612459708113823477708357 26927336195271341902070317)
    ·
      refine ⟨10097751073226753213276369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26927336195271341902070317 10097751073226753213276369)
      ·
        refine ⟨7573313304920064909957277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10097751073226753213276369 7573313304920064909957277)
        ·
          refine ⟨2839992489345024341233979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7573313304920064909957277 2839992489345024341233979)
          ·
            refine ⟨4259988734017536511850969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2839992489345024341233979 4259988734017536511850969)
            ·
              refine ⟨3194991550513152383888227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4259988734017536511850969 3194991550513152383888227)
              ·
                refine ⟨4792487325769728575832341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3194991550513152383888227 4792487325769728575832341)
                ·
                  refine ⟨224647843395456026992141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4792487325769728575832341 224647843395456026992141)
                  ·
                    rfl

theorem cell23_3937501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 2, 1, 6].length) (baseStart_3937501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3937501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3937501 prefixEnd_3937501 := by exact prefixLift 3937501
  have htrace : WordTrace (prefixWord ++ tailWord_3937501) baseStart_3937501 baseEnd_3937501 := by
    simpa [prefixWord, tailWord_3937501, baseEnd_3937501] using wordTrace_append hprefix tailTrace_3937501
  have hstable : (prefixWord ++ tailWord_3937501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3937501).length < 2 ^ (prefixWord ++ tailWord_3937501).sum := by decide
  have hdescent : baseEnd_3937501 < baseStart_3937501 := by decide
  rcases family_descends (prefixWord ++ tailWord_3937501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3937517 : List Nat := [1, 5, 1, 2, 2, 2, 1, 1, 3, 1, 4]
def baseStart_3937517 : Nat := 118140960795 + 3937517 * 2 ^ 59
def prefixEnd_3937517 : Nat := 4983230072969 + 3 ^ 40 * 3937517 * 2
def baseEnd_3937517 : Nat := 2021838806249576180329195

theorem tailTrace_3937517 : CollatzResearch.WordTrace tailWord_3937517 prefixEnd_3937517 2021838806249576180329195 := by
  unfold tailWord_3937517
  simp only [CollatzResearch.WordTrace]
  refine ⟨143613043276055858210290805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95742028850703905473527203 143613043276055858210290805)
  ·
    refine ⟨13463722807130236707214763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 143613043276055858210290805 13463722807130236707214763)
    ·
      refine ⟨20195584210695355060822145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13463722807130236707214763 20195584210695355060822145)
      ·
        refine ⟨15146688158021516295616609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20195584210695355060822145 15146688158021516295616609)
        ·
          refine ⟨11360016118516137221712457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15146688158021516295616609 11360016118516137221712457)
          ·
            refine ⟨8520012088887102916284343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11360016118516137221712457 8520012088887102916284343)
            ·
              refine ⟨12780018133330654374426515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8520012088887102916284343 12780018133330654374426515)
              ·
                refine ⟨19170027199995981561639773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12780018133330654374426515 19170027199995981561639773)
                ·
                  refine ⟨7188760199998493085614915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19170027199995981561639773 7188760199998493085614915)
                  ·
                    refine ⟨10783140299997739628422373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7188760199998493085614915 10783140299997739628422373)
                    ·
                      refine ⟨2021838806249576180329195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10783140299997739628422373 2021838806249576180329195)
                      ·
                        rfl

theorem cell23_3937517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 1, 1, 3, 1, 4].length) (baseStart_3937517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3937517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3937517 prefixEnd_3937517 := by exact prefixLift 3937517
  have htrace : WordTrace (prefixWord ++ tailWord_3937517) baseStart_3937517 baseEnd_3937517 := by
    simpa [prefixWord, tailWord_3937517, baseEnd_3937517] using wordTrace_append hprefix tailTrace_3937517
  have hstable : (prefixWord ++ tailWord_3937517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3937517).length < 2 ^ (prefixWord ++ tailWord_3937517).sum := by decide
  have hdescent : baseEnd_3937517 < baseStart_3937517 := by decide
  rcases family_descends (prefixWord ++ tailWord_3937517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3937523 : List Nat := [1, 1, 1, 2, 2, 5, 2, 9]
def baseStart_3937523 : Nat := 118140960795 + 3937523 * 2 ^ 59
def prefixEnd_3937523 : Nat := 4983230072969 + 3 ^ 40 * 3937523 * 2
def baseEnd_3937523 : Nat := 74883032856796413216821

theorem tailTrace_3937523 : CollatzResearch.WordTrace tailWord_3937523 prefixEnd_3937523 74883032856796413216821 := by
  unfold tailWord_3937523
  simp only [CollatzResearch.WordTrace]
  refine ⟨143613262114034121235009223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95742174742689414156672815 143613262114034121235009223)
  ·
    refine ⟨215419893171051181852513835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143613262114034121235009223 215419893171051181852513835)
    ·
      refine ⟨323129839756576772778770753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215419893171051181852513835 323129839756576772778770753)
      ·
        refine ⟨242347379817432579584078065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 323129839756576772778770753 242347379817432579584078065)
        ·
          refine ⟨181760534863074434688058549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 242347379817432579584078065 181760534863074434688058549)
          ·
            refine ⟨17040050143413228252005489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 181760534863074434688058549 17040050143413228252005489)
            ·
              refine ⟨12780037607559921189004117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17040050143413228252005489 12780037607559921189004117)
              ·
                refine ⟨74883032856796413216821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 12780037607559921189004117 74883032856796413216821)
                ·
                  rfl

theorem cell23_3937523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 2, 9].length) (baseStart_3937523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3937523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3937523 prefixEnd_3937523 := by exact prefixLift 3937523
  have htrace : WordTrace (prefixWord ++ tailWord_3937523) baseStart_3937523 baseEnd_3937523 := by
    simpa [prefixWord, tailWord_3937523, baseEnd_3937523] using wordTrace_append hprefix tailTrace_3937523
  have hstable : (prefixWord ++ tailWord_3937523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3937523).length < 2 ^ (prefixWord ++ tailWord_3937523).sum := by decide
  have hdescent : baseEnd_3937523 < baseStart_3937523 := by decide
  rcases family_descends (prefixWord ++ tailWord_3937523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3937530 : List Nat := [3, 1, 1, 1, 1, 4, 3, 2, 1, 2, 4]
def baseStart_3937530 : Nat := 118140960795 + 3937530 * 2 ^ 59
def prefixEnd_3937530 : Nat := 4983230072969 + 3 ^ 40 * 3937530 * 2
def baseEnd_3937530 : Nat := 2021845481498084629466635

theorem tailTrace_3937530 : CollatzResearch.WordTrace tailWord_3937530 prefixEnd_3937530 2021845481498084629466635 := by
  unfold tailWord_3937530
  simp only [CollatzResearch.WordTrace]
  refine ⟨35903379356252190357628511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95742344950005840953676029 35903379356252190357628511)
  ·
    refine ⟨53855069034378285536442767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35903379356252190357628511 53855069034378285536442767)
    ·
      refine ⟨80782603551567428304664151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53855069034378285536442767 80782603551567428304664151)
      ·
        refine ⟨121173905327351142456996227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80782603551567428304664151 121173905327351142456996227)
        ·
          refine ⟨181760857991026713685494341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121173905327351142456996227 181760857991026713685494341)
          ·
            refine ⟨34080160873317508816030189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 181760857991026713685494341 34080160873317508816030189)
            ·
              refine ⟨12780060327494065806011321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34080160873317508816030189 12780060327494065806011321)
              ·
                refine ⟨9585045245620549354508491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12780060327494065806011321 9585045245620549354508491)
                ·
                  refine ⟨14377567868430824031762737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9585045245620549354508491 14377567868430824031762737)
                  ·
                    refine ⟨10783175901323118023822053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14377567868430824031762737 10783175901323118023822053)
                    ·
                      refine ⟨2021845481498084629466635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10783175901323118023822053 2021845481498084629466635)
                      ·
                        rfl

theorem cell23_3937530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3, 2, 1, 2, 4].length) (baseStart_3937530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3937530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3937530 prefixEnd_3937530 := by exact prefixLift 3937530
  have htrace : WordTrace (prefixWord ++ tailWord_3937530) baseStart_3937530 baseEnd_3937530 := by
    simpa [prefixWord, tailWord_3937530, baseEnd_3937530] using wordTrace_append hprefix tailTrace_3937530
  have hstable : (prefixWord ++ tailWord_3937530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3937530).length < 2 ^ (prefixWord ++ tailWord_3937530).sum := by decide
  have hdescent : baseEnd_3937530 < baseStart_3937530 := by decide
  rcases family_descends (prefixWord ++ tailWord_3937530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3937537 : List Nat := [1, 2, 4, 1, 1, 5, 1, 1, 1, 1, 5]
def baseStart_3937537 : Nat := 118140960795 + 3937537 * 2 ^ 59
def prefixEnd_3937537 : Nat := 4983230072969 + 3 ^ 40 * 3937537 * 2
def baseEnd_3937537 : Nat := 2021849075862666102079103

theorem tailTrace_3937537 : CollatzResearch.WordTrace tailWord_3937537 prefixEnd_3937537 2021849075862666102079103 := by
  unfold tailWord_3937537
  simp only [CollatzResearch.WordTrace]
  refine ⟨143613772735983401626018865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95742515157322267750679243 143613772735983401626018865)
  ·
    refine ⟨107710329551987551219514149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143613772735983401626018865 107710329551987551219514149)
    ·
      refine ⟨20195686790997665853658903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 107710329551987551219514149 20195686790997665853658903)
      ·
        refine ⟨30293530186496498780488355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20195686790997665853658903 30293530186496498780488355)
        ·
          refine ⟨45440295279744748170732533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30293530186496498780488355 45440295279744748170732533)
          ·
            refine ⟨4260027682476070141006175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 45440295279744748170732533 4260027682476070141006175)
            ·
              refine ⟨6390041523714105211509263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4260027682476070141006175 6390041523714105211509263)
              ·
                refine ⟨9585062285571157817263895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6390041523714105211509263 9585062285571157817263895)
                ·
                  refine ⟨14377593428356736725895843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9585062285571157817263895 14377593428356736725895843)
                  ·
                    refine ⟨21566390142535105088843765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14377593428356736725895843 21566390142535105088843765)
                    ·
                      refine ⟨2021849075862666102079103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21566390142535105088843765 2021849075862666102079103)
                      ·
                        rfl

theorem cell23_3937537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 1, 1, 1, 1, 5].length) (baseStart_3937537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3937537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3937537 prefixEnd_3937537 := by exact prefixLift 3937537
  have htrace : WordTrace (prefixWord ++ tailWord_3937537) baseStart_3937537 baseEnd_3937537 := by
    simpa [prefixWord, tailWord_3937537, baseEnd_3937537] using wordTrace_append hprefix tailTrace_3937537
  have hstable : (prefixWord ++ tailWord_3937537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3937537).length < 2 ^ (prefixWord ++ tailWord_3937537).sum := by decide
  have hdescent : baseEnd_3937537 < baseStart_3937537 := by decide
  rcases family_descends (prefixWord ++ tailWord_3937537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3937544 : List Nat := [2, 1, 3, 2, 4, 1, 2, 2, 2, 4]
def baseStart_3937544 : Nat := 118140960795 + 3937544 * 2 ^ 59
def prefixEnd_3937544 : Nat := 4983230072969 + 3 ^ 40 * 3937544 * 2
def baseEnd_3937544 : Nat := 673950890075749191563857

theorem tailTrace_3937544 : CollatzResearch.WordTrace tailWord_3937544 prefixEnd_3937544 673950890075749191563857 := by
  unfold tailWord_3937544
  simp only [CollatzResearch.WordTrace]
  refine ⟨71807014023479020910761843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95742685364638694547682457 71807014023479020910761843)
  ·
    refine ⟨107710521035218531366142765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71807014023479020910761843 107710521035218531366142765)
    ·
      refine ⟨40391445388206949262303537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107710521035218531366142765 40391445388206949262303537)
      ·
        refine ⟨30293584041155211946727653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40391445388206949262303537 30293584041155211946727653)
        ·
          refine ⟨5680047007716602240011435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30293584041155211946727653 5680047007716602240011435)
          ·
            refine ⟨8520070511574903360017153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5680047007716602240011435 8520070511574903360017153)
            ·
              refine ⟨6390052883681177520012865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8520070511574903360017153 6390052883681177520012865)
              ·
                refine ⟨4792539662760883140009649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6390052883681177520012865 4792539662760883140009649)
                ·
                  refine ⟨3594404747070662355007237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4792539662760883140009649 3594404747070662355007237)
                  ·
                    refine ⟨673950890075749191563857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3594404747070662355007237 673950890075749191563857)
                    ·
                      rfl

theorem cell23_3937544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 2, 2, 2, 4].length) (baseStart_3937544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3937544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3937544 prefixEnd_3937544 := by exact prefixLift 3937544
  have htrace : WordTrace (prefixWord ++ tailWord_3937544) baseStart_3937544 baseEnd_3937544 := by
    simpa [prefixWord, tailWord_3937544, baseEnd_3937544] using wordTrace_append hprefix tailTrace_3937544
  have hstable : (prefixWord ++ tailWord_3937544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3937544).length < 2 ^ (prefixWord ++ tailWord_3937544).sum := by decide
  have hdescent : baseEnd_3937544 < baseStart_3937544 := by decide
  rcases family_descends (prefixWord ++ tailWord_3937544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3937553 : List Nat := [1, 2, 2, 1, 1, 4, 1, 1, 1, 9]
def baseStart_3937553 : Nat := 118140960795 + 3937553 * 2 ^ 59
def prefixEnd_3937553 : Nat := 4983230072969 + 3 ^ 40 * 3937553 * 2
def baseEnd_3937553 : Nat := 673952430517712679826343

theorem tailTrace_3937553 : CollatzResearch.WordTrace tailWord_3937553 prefixEnd_3937553 673952430517712679826343 := by
  unfold tailWord_3937553
  simp only [CollatzResearch.WordTrace]
  refine ⟨143614356303925436358601313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95742904202616957572400875 143614356303925436358601313)
  ·
    refine ⟨107710767227944077268950985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143614356303925436358601313 107710767227944077268950985)
    ·
      refine ⟨80783075420958057951713239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107710767227944077268950985 80783075420958057951713239)
      ·
        refine ⟨121174613131437086927569859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80783075420958057951713239 121174613131437086927569859)
        ·
          refine ⟨181761919697155630391354789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121174613131437086927569859 181761919697155630391354789)
          ·
            refine ⟨34080359943216680698379023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 181761919697155630391354789 34080359943216680698379023)
            ·
              refine ⟨51120539914825021047568535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34080359943216680698379023 51120539914825021047568535)
              ·
                refine ⟨76680809872237531571352803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51120539914825021047568535 76680809872237531571352803)
                ·
                  refine ⟨115021214808356297357029205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76680809872237531571352803 115021214808356297357029205)
                  ·
                    refine ⟨673952430517712679826343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 115021214808356297357029205 673952430517712679826343)
                    ·
                      rfl

theorem cell23_3937553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 9].length) (baseStart_3937553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3937553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3937553 prefixEnd_3937553 := by exact prefixLift 3937553
  have htrace : WordTrace (prefixWord ++ tailWord_3937553) baseStart_3937553 baseEnd_3937553 := by
    simpa [prefixWord, tailWord_3937553, baseEnd_3937553] using wordTrace_append hprefix tailTrace_3937553
  have hstable : (prefixWord ++ tailWord_3937553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3937553).length < 2 ^ (prefixWord ++ tailWord_3937553).sum := by decide
  have hdescent : baseEnd_3937553 < baseStart_3937553 := by decide
  rcases family_descends (prefixWord ++ tailWord_3937553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3937563 : List Nat := [1, 1, 1, 1, 1, 1, 5, 2, 1, 4, 5]
def baseStart_3937563 : Nat := 118140960795 + 3937563 * 2 ^ 59
def prefixEnd_3937563 : Nat := 4983230072969 + 3 ^ 40 * 3937563 * 2
def baseEnd_3937563 : Nat := 2021862426359683000353983

theorem tailTrace_3937563 : CollatzResearch.WordTrace tailWord_3937563 prefixEnd_3937563 2021862426359683000353983 := by
  unfold tailWord_3937563
  simp only [CollatzResearch.WordTrace]
  refine ⟨143614721033889208066465343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95743147355926138710976895 143614721033889208066465343)
  ·
    refine ⟨215422081550833812099698015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143614721033889208066465343 215422081550833812099698015)
    ·
      refine ⟨323133122326250718149547023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215422081550833812099698015 323133122326250718149547023)
      ·
        refine ⟨484699683489376077224320535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 323133122326250718149547023 484699683489376077224320535)
        ·
          refine ⟨727049525234064115836480803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 484699683489376077224320535 727049525234064115836480803)
          ·
            refine ⟨1090574287851096173754721205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 727049525234064115836480803 1090574287851096173754721205)
            ·
              refine ⟨102241339486040266289505113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1090574287851096173754721205 102241339486040266289505113)
              ·
                refine ⟨76681004614530199717128835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102241339486040266289505113 76681004614530199717128835)
                ·
                  refine ⟨115021506921795299575693253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76681004614530199717128835 115021506921795299575693253)
                  ·
                    refine ⟨21566532547836618670442485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 115021506921795299575693253 21566532547836618670442485)
                    ·
                      refine ⟨2021862426359683000353983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21566532547836618670442485 2021862426359683000353983)
                      ·
                        rfl

theorem cell23_3937563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 2, 1, 4, 5].length) (baseStart_3937563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3937563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3937563 prefixEnd_3937563 := by exact prefixLift 3937563
  have htrace : WordTrace (prefixWord ++ tailWord_3937563) baseStart_3937563 baseEnd_3937563 := by
    simpa [prefixWord, tailWord_3937563, baseEnd_3937563] using wordTrace_append hprefix tailTrace_3937563
  have hstable : (prefixWord ++ tailWord_3937563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3937563).length < 2 ^ (prefixWord ++ tailWord_3937563).sum := by decide
  have hdescent : baseEnd_3937563 < baseStart_3937563 := by decide
  rcases family_descends (prefixWord ++ tailWord_3937563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3937583 : List Nat := [1, 1, 2, 1, 2, 1, 3, 1, 3, 8]
def baseStart_3937583 : Nat := 118140960795 + 3937583 * 2 ^ 59
def prefixEnd_3937583 : Nat := 4983230072969 + 3 ^ 40 * 3937583 * 2
def baseEnd_3937583 : Nat := 673957565324257640701297

theorem tailTrace_3937583 : CollatzResearch.WordTrace tailWord_3937583 prefixEnd_3937583 673957565324257640701297 := by
  unfold tailWord_3937583
  simp only [CollatzResearch.WordTrace]
  refine ⟨143615450493816751482193403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95743633662544500988128935 143615450493816751482193403)
  ·
    refine ⟨215423175740725127223290105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143615450493816751482193403 215423175740725127223290105)
    ·
      refine ⟨161567381805543845417467579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215423175740725127223290105 161567381805543845417467579)
      ·
        refine ⟨242351072708315768126201369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161567381805543845417467579 242351072708315768126201369)
        ·
          refine ⟨181763304531236826094651027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 242351072708315768126201369 181763304531236826094651027)
          ·
            refine ⟨272644956796855239141976541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181763304531236826094651027 272644956796855239141976541)
            ·
              refine ⟨102241858798820714678241203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 272644956796855239141976541 102241858798820714678241203)
              ·
                refine ⟨153362788198231072017361805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102241858798820714678241203 153362788198231072017361805)
                ·
                  refine ⟨57511045574336652006510677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 153362788198231072017361805 57511045574336652006510677)
                  ·
                    refine ⟨673957565324257640701297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 57511045574336652006510677 673957565324257640701297)
                    ·
                      rfl

theorem cell23_3937583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 1, 3, 8].length) (baseStart_3937583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3937583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3937583 prefixEnd_3937583 := by exact prefixLift 3937583
  have htrace : WordTrace (prefixWord ++ tailWord_3937583) baseStart_3937583 baseEnd_3937583 := by
    simpa [prefixWord, tailWord_3937583, baseEnd_3937583] using wordTrace_append hprefix tailTrace_3937583
  have hstable : (prefixWord ++ tailWord_3937583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3937583).length < 2 ^ (prefixWord ++ tailWord_3937583).sum := by decide
  have hdescent : baseEnd_3937583 < baseStart_3937583 := by decide
  rcases family_descends (prefixWord ++ tailWord_3937583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3937594 : List Nat := [3, 1, 1, 1, 4, 1, 3, 3, 1, 3, 2]
def baseStart_3937594 : Nat := 118140960795 + 3937594 * 2 ^ 59
def prefixEnd_3937594 : Nat := 4983230072969 + 3 ^ 40 * 3937594 * 2
def baseEnd_3937594 : Nat := 2021878344259972379066341

theorem tailTrace_3937594 : CollatzResearch.WordTrace tailWord_3937594 prefixEnd_3937594 2021878344259972379066341 := by
  unfold tailWord_3937594
  simp only [CollatzResearch.WordTrace]
  refine ⟨35903962924194225090210959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95743901131184600240562557 35903962924194225090210959)
  ·
    refine ⟨53855944386291337635316439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35903962924194225090210959 53855944386291337635316439)
    ·
      refine ⟨80783916579437006452974659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53855944386291337635316439 80783916579437006452974659)
      ·
        refine ⟨121175874869155509679461989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80783916579437006452974659 121175874869155509679461989)
        ·
          refine ⟨22720476537966658064899123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 121175874869155509679461989 22720476537966658064899123)
          ·
            refine ⟨34080714806949987097348685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22720476537966658064899123 34080714806949987097348685)
            ·
              refine ⟨12780268052606245161505757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34080714806949987097348685 12780268052606245161505757)
              ·
                refine ⟨4792600519727341935564659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12780268052606245161505757 4792600519727341935564659)
                ·
                  refine ⟨7188900779591012903346989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4792600519727341935564659 7188900779591012903346989)
                  ·
                    refine ⟨2695837792346629838755121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7188900779591012903346989 2695837792346629838755121)
                    ·
                      refine ⟨2021878344259972379066341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2695837792346629838755121 2021878344259972379066341)
                      ·
                        rfl

theorem cell23_3937594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 3, 3, 1, 3, 2].length) (baseStart_3937594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3937594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3937594 prefixEnd_3937594 := by exact prefixLift 3937594
  have htrace : WordTrace (prefixWord ++ tailWord_3937594) baseStart_3937594 baseEnd_3937594 := by
    simpa [prefixWord, tailWord_3937594, baseEnd_3937594] using wordTrace_append hprefix tailTrace_3937594
  have hstable : (prefixWord ++ tailWord_3937594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3937594).length < 2 ^ (prefixWord ++ tailWord_3937594).sum := by decide
  have hdescent : baseEnd_3937594 < baseStart_3937594 := by decide
  rcases family_descends (prefixWord ++ tailWord_3937594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3937601 : List Nat := [1, 2, 5, 2, 1, 1, 3, 2, 2, 1, 3]
def baseStart_3937601 : Nat := 118140960795 + 3937601 * 2 ^ 59
def prefixEnd_3937601 : Nat := 4983230072969 + 3 ^ 40 * 3937601 * 2
def baseEnd_3937601 : Nat := 2021881938624553851678809

theorem tailTrace_3937601 : CollatzResearch.WordTrace tailWord_3937601 prefixEnd_3937601 2021881938624553851678809 := by
  unfold tailWord_3937601
  simp only [CollatzResearch.WordTrace]
  refine ⟨143616107007751540556348657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95744071338501027037565771 143616107007751540556348657)
  ·
    refine ⟨107712080255813655417261493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143616107007751540556348657 107712080255813655417261493)
    ·
      refine ⟨10098007523982530195368265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 107712080255813655417261493 10098007523982530195368265)
      ·
        refine ⟨7573505642986897646526199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10098007523982530195368265 7573505642986897646526199)
        ·
          refine ⟨11360258464480346469789299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7573505642986897646526199 11360258464480346469789299)
          ·
            refine ⟨17040387696720519704683949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11360258464480346469789299 17040387696720519704683949)
            ·
              refine ⟨6390145386270194889256481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17040387696720519704683949 6390145386270194889256481)
              ·
                refine ⟨4792609039702646166942361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6390145386270194889256481 4792609039702646166942361)
                ·
                  refine ⟨3594456779776984625206771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4792609039702646166942361 3594456779776984625206771)
                  ·
                    refine ⟨5391685169665476937810157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3594456779776984625206771 5391685169665476937810157)
                    ·
                      refine ⟨2021881938624553851678809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5391685169665476937810157 2021881938624553851678809)
                      ·
                        rfl

theorem cell23_3937601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 3, 2, 2, 1, 3].length) (baseStart_3937601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3937601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3937601 prefixEnd_3937601 := by exact prefixLift 3937601
  have htrace : WordTrace (prefixWord ++ tailWord_3937601) baseStart_3937601 baseEnd_3937601 := by
    simpa [prefixWord, tailWord_3937601, baseEnd_3937601] using wordTrace_append hprefix tailTrace_3937601
  have hstable : (prefixWord ++ tailWord_3937601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3937601).length < 2 ^ (prefixWord ++ tailWord_3937601).sum := by decide
  have hdescent : baseEnd_3937601 < baseStart_3937601 := by decide
  rcases family_descends (prefixWord ++ tailWord_3937601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3937610 : List Nat := [3, 1, 2, 1, 1, 1, 1, 3, 1, 6, 3]
def baseStart_3937610 : Nat := 118140960795 + 3937610 * 2 ^ 59
def prefixEnd_3937610 : Nat := 4983230072969 + 3 ^ 40 * 3937610 * 2
def baseEnd_3937610 : Nat := 2021886559950444316466267

theorem tailTrace_3937610 : CollatzResearch.WordTrace tailWord_3937610 prefixEnd_3937610 2021886559950444316466267 := by
  unfold tailWord_3937610
  simp only [CollatzResearch.WordTrace]
  refine ⟨35904108816179733773356571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95744290176479290062284189 35904108816179733773356571)
  ·
    refine ⟨53856163224269600660034857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35904108816179733773356571 53856163224269600660034857)
    ·
      refine ⟨40392122418202200495026143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53856163224269600660034857 40392122418202200495026143)
      ·
        refine ⟨60588183627303300742539215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40392122418202200495026143 60588183627303300742539215)
        ·
          refine ⟨90882275440954951113808823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60588183627303300742539215 90882275440954951113808823)
          ·
            refine ⟨136323413161432426670713235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90882275440954951113808823 136323413161432426670713235)
            ·
              refine ⟨204485119742148640006069853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136323413161432426670713235 204485119742148640006069853)
              ·
                refine ⟨76681919903305740002276195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 204485119742148640006069853 76681919903305740002276195)
                ·
                  refine ⟨115022879854958610003414293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76681919903305740002276195 115022879854958610003414293)
                  ·
                    refine ⟨5391697493201184843910045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 115022879854958610003414293 5391697493201184843910045)
                    ·
                      refine ⟨2021886559950444316466267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5391697493201184843910045 2021886559950444316466267)
                      ·
                        rfl

theorem cell23_3937610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 3, 1, 6, 3].length) (baseStart_3937610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3937610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3937610 prefixEnd_3937610 := by exact prefixLift 3937610
  have htrace : WordTrace (prefixWord ++ tailWord_3937610) baseStart_3937610 baseEnd_3937610 := by
    simpa [prefixWord, tailWord_3937610, baseEnd_3937610] using wordTrace_append hprefix tailTrace_3937610
  have hstable : (prefixWord ++ tailWord_3937610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3937610).length < 2 ^ (prefixWord ++ tailWord_3937610).sum := by decide
  have hdescent : baseEnd_3937610 < baseStart_3937610 := by decide
  rcases family_descends (prefixWord ++ tailWord_3937610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3937720 : List Nat := [2, 1, 2, 1, 2, 2, 2, 3, 8]
def baseStart_3937720 : Nat := 118140960795 + 3937720 * 2 ^ 59
def prefixEnd_3937720 : Nat := 4983230072969 + 3 ^ 40 * 3937720 * 2
def baseEnd_3937720 : Nat := 224660338091382098454529

theorem tailTrace_3937720 : CollatzResearch.WordTrace tailWord_3937720 prefixEnd_3937720 224660338091382098454529 := by
  unfold tailWord_3937720
  simp only [CollatzResearch.WordTrace]
  refine ⟨71810223647160211939965307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95746964862880282586620409 71810223647160211939965307)
  ·
    refine ⟨107715335470740317909947961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71810223647160211939965307 107715335470740317909947961)
    ·
      refine ⟨80786501603055238432460971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107715335470740317909947961 80786501603055238432460971)
      ·
        refine ⟨121179752404582857648691457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80786501603055238432460971 121179752404582857648691457)
        ·
          refine ⟨90884814303437143236518593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121179752404582857648691457 90884814303437143236518593)
          ·
            refine ⟨68163610727577857427388945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90884814303437143236518593 68163610727577857427388945)
            ·
              refine ⟨51122708045683393070541709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68163610727577857427388945 51122708045683393070541709)
              ·
                refine ⟨19171015517131272401453141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51122708045683393070541709 19171015517131272401453141)
                ·
                  refine ⟨224660338091382098454529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19171015517131272401453141 224660338091382098454529)
                  ·
                    rfl

theorem cell23_3937720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 3, 8].length) (baseStart_3937720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3937720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3937720 prefixEnd_3937720 := by exact prefixLift 3937720
  have htrace : WordTrace (prefixWord ++ tailWord_3937720) baseStart_3937720 baseEnd_3937720 := by
    simpa [prefixWord, tailWord_3937720, baseEnd_3937720] using wordTrace_append hprefix tailTrace_3937720
  have hstable : (prefixWord ++ tailWord_3937720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3937720).length < 2 ^ (prefixWord ++ tailWord_3937720).sum := by decide
  have hdescent : baseEnd_3937720 < baseStart_3937720 := by decide
  rcases family_descends (prefixWord ++ tailWord_3937720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3937748 : List Nat := [2, 4, 1, 2, 4, 1, 1, 1, 2, 1, 4]
def baseStart_3937748 : Nat := 118140960795 + 3937748 * 2 ^ 59
def prefixEnd_3937748 : Nat := 4983230072969 + 3 ^ 40 * 3937748 * 2
def baseEnd_3937748 : Nat := 2021957420280764776540633

theorem tailTrace_3937748 : CollatzResearch.WordTrace tailWord_3937748 prefixEnd_3937748 2021957420280764776540633 := by
  unfold tailWord_3937748
  simp only [CollatzResearch.WordTrace]
  refine ⟨71810734269109492330974949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95747645692145989774633265 71810734269109492330974949)
  ·
    refine ⟨13464512675458029812057803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71810734269109492330974949 13464512675458029812057803)
    ·
      refine ⟨20196769013187044718086705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13464512675458029812057803 20196769013187044718086705)
      ·
        refine ⟨15147576759890283538565029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20196769013187044718086705 15147576759890283538565029)
        ·
          refine ⟨2840170642479428163480943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15147576759890283538565029 2840170642479428163480943)
          ·
            refine ⟨4260255963719142245221415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2840170642479428163480943 4260255963719142245221415)
            ·
              refine ⟨6390383945578713367832123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4260255963719142245221415 6390383945578713367832123)
              ·
                refine ⟨9585575918368070051748185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6390383945578713367832123 9585575918368070051748185)
                ·
                  refine ⟨7189181938776052538811139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9585575918368070051748185 7189181938776052538811139)
                  ·
                    refine ⟨10783772908164078808216709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7189181938776052538811139 10783772908164078808216709)
                    ·
                      refine ⟨2021957420280764776540633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10783772908164078808216709 2021957420280764776540633)
                      ·
                        rfl

theorem cell23_3937748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 1, 1, 2, 1, 4].length) (baseStart_3937748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3937748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3937748 prefixEnd_3937748 := by exact prefixLift 3937748
  have htrace : WordTrace (prefixWord ++ tailWord_3937748) baseStart_3937748 baseEnd_3937748 := by
    simpa [prefixWord, tailWord_3937748, baseEnd_3937748] using wordTrace_append hprefix tailTrace_3937748
  have hstable : (prefixWord ++ tailWord_3937748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3937748).length < 2 ^ (prefixWord ++ tailWord_3937748).sum := by decide
  have hdescent : baseEnd_3937748 < baseStart_3937748 := by decide
  rcases family_descends (prefixWord ++ tailWord_3937748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3937824 : List Nat := [2, 1, 1, 6, 1, 1, 1, 3, 1, 1, 5]
def baseStart_3937824 : Nat := 118140960795 + 3937824 * 2 ^ 59
def prefixEnd_3937824 : Nat := 4983230072969 + 3 ^ 40 * 3937824 * 2
def baseEnd_3937824 : Nat := 2021996444810506479190283

theorem tailTrace_3937824 : CollatzResearch.WordTrace tailWord_3937824 prefixEnd_3937824 2021996444810506479190283 := by
  unfold tailWord_3937824
  simp only [CollatzResearch.WordTrace]
  refine ⟨71812120242971824820858263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95749493657295766427811017 71812120242971824820858263)
  ·
    refine ⟨107718180364457737231287395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71812120242971824820858263 107718180364457737231287395)
    ·
      refine ⟨161577270546686605846931093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107718180364457737231287395 161577270546686605846931093)
      ·
        refine ⟨7573934556875934649074895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 161577270546686605846931093 7573934556875934649074895)
        ·
          refine ⟨11360901835313901973612343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7573934556875934649074895 11360901835313901973612343)
          ·
            refine ⟨17041352752970852960418515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11360901835313901973612343 17041352752970852960418515)
            ·
              refine ⟨25562029129456279440627773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17041352752970852960418515 25562029129456279440627773)
              ·
                refine ⟨9585760923546104790235415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25562029129456279440627773 9585760923546104790235415)
                ·
                  refine ⟨14378641385319157185353123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9585760923546104790235415 14378641385319157185353123)
                  ·
                    refine ⟨21567962077978735778029685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14378641385319157185353123 21567962077978735778029685)
                    ·
                      refine ⟨2021996444810506479190283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21567962077978735778029685 2021996444810506479190283)
                      ·
                        rfl

theorem cell23_3937824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_3937824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3937824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3937824 prefixEnd_3937824 := by exact prefixLift 3937824
  have htrace : WordTrace (prefixWord ++ tailWord_3937824) baseStart_3937824 baseEnd_3937824 := by
    simpa [prefixWord, tailWord_3937824, baseEnd_3937824] using wordTrace_append hprefix tailTrace_3937824
  have hstable : (prefixWord ++ tailWord_3937824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3937824).length < 2 ^ (prefixWord ++ tailWord_3937824).sum := by decide
  have hdescent : baseEnd_3937824 < baseStart_3937824 := by decide
  rcases family_descends (prefixWord ++ tailWord_3937824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3937832 : List Nat := [2, 1, 5, 2, 2, 1, 3, 2, 1, 1, 3]
def baseStart_3937832 : Nat := 118140960795 + 3937832 * 2 ^ 59
def prefixEnd_3937832 : Nat := 4983230072969 + 3 ^ 40 * 3937832 * 2
def baseEnd_3937832 : Nat := 2022000552655742447890247

theorem tailTrace_3937832 : CollatzResearch.WordTrace tailWord_3937832 prefixEnd_3937832 2022000552655742447890247 := by
  unfold tailWord_3937832
  simp only [CollatzResearch.WordTrace]
  refine ⟨71812266134957333504003875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95749688179943111338671833 71812266134957333504003875)
  ·
    refine ⟨107718399202436000256005813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71812266134957333504003875 107718399202436000256005813)
    ·
      refine ⟨10098599925228375024000545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 107718399202436000256005813 10098599925228375024000545)
      ·
        refine ⟨7573949943921281268000409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10098599925228375024000545 7573949943921281268000409)
        ·
          refine ⟨5680462457940960951000307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7573949943921281268000409 5680462457940960951000307)
          ·
            refine ⟨8520693686911441426500461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5680462457940960951000307 8520693686911441426500461)
            ·
              refine ⟨3195260132591790534937673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8520693686911441426500461 3195260132591790534937673)
              ·
                refine ⟨2396445099443842901203255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3195260132591790534937673 2396445099443842901203255)
                ·
                  refine ⟨3594667649165764351804883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2396445099443842901203255 3594667649165764351804883)
                  ·
                    refine ⟨5392001473748646527707325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3594667649165764351804883 5392001473748646527707325)
                    ·
                      refine ⟨2022000552655742447890247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5392001473748646527707325 2022000552655742447890247)
                      ·
                        rfl

theorem cell23_3937832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 3, 2, 1, 1, 3].length) (baseStart_3937832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3937832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3937832 prefixEnd_3937832 := by exact prefixLift 3937832
  have htrace : WordTrace (prefixWord ++ tailWord_3937832) baseStart_3937832 baseEnd_3937832 := by
    simpa [prefixWord, tailWord_3937832, baseEnd_3937832] using wordTrace_append hprefix tailTrace_3937832
  have hstable : (prefixWord ++ tailWord_3937832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3937832).length < 2 ^ (prefixWord ++ tailWord_3937832).sum := by decide
  have hdescent : baseEnd_3937832 < baseStart_3937832 := by decide
  rcases family_descends (prefixWord ++ tailWord_3937832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3937848 : List Nat := [2, 1, 2, 1, 4, 4, 2, 1, 2, 4]
def baseStart_3937848 : Nat := 118140960795 + 3937848 * 2 ^ 59
def prefixEnd_3937848 : Nat := 4983230072969 + 3 ^ 40 * 3937848 * 2
def baseEnd_3937848 : Nat := 674002922782071461763391

theorem tailTrace_3937848 : CollatzResearch.WordTrace tailWord_3937848 prefixEnd_3937848 674002922782071461763391 := by
  unfold tailWord_3937848
  simp only [CollatzResearch.WordTrace]
  refine ⟨71812557918928350870295099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95750077225237801160393465 71812557918928350870295099)
  ·
    refine ⟨107718836878392526305442649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71812557918928350870295099 107718836878392526305442649)
    ·
      refine ⟨80789127658794394729081987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107718836878392526305442649 80789127658794394729081987)
      ·
        refine ⟨121183691488191592093622981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80789127658794394729081987 121183691488191592093622981)
        ·
          refine ⟨22721942154035923517554309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 121183691488191592093622981 22721942154035923517554309)
          ·
            refine ⟨4260364153881735659541433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22721942154035923517554309 4260364153881735659541433)
            ·
              refine ⟨3195273115411301744656075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4260364153881735659541433 3195273115411301744656075)
              ·
                refine ⟨4792909673116952616984113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3195273115411301744656075 4792909673116952616984113)
                ·
                  refine ⟨3594682254837714462738085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4792909673116952616984113 3594682254837714462738085)
                  ·
                    refine ⟨674002922782071461763391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3594682254837714462738085 674002922782071461763391)
                    ·
                      rfl

theorem cell23_3937848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 2, 1, 2, 4].length) (baseStart_3937848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3937848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3937848 prefixEnd_3937848 := by exact prefixLift 3937848
  have htrace : WordTrace (prefixWord ++ tailWord_3937848) baseStart_3937848 baseEnd_3937848 := by
    simpa [prefixWord, tailWord_3937848, baseEnd_3937848] using wordTrace_append hprefix tailTrace_3937848
  have hstable : (prefixWord ++ tailWord_3937848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3937848).length < 2 ^ (prefixWord ++ tailWord_3937848).sum := by decide
  have hdescent : baseEnd_3937848 < baseStart_3937848 := by decide
  rcases family_descends (prefixWord ++ tailWord_3937848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3937878 : List Nat := [5, 2, 2, 2, 2, 10]
def baseStart_3937878 : Nat := 118140960795 + 3937878 * 2 ^ 59
def prefixEnd_3937878 : Nat := 4983230072969 + 3 ^ 40 * 3937878 * 2
def baseEnd_3937878 : Nat := 8321087130723659538745

theorem tailTrace_3937878 : CollatzResearch.WordTrace tailWord_3937878 prefixEnd_3937878 8321087130723659538745 := by
  unfold tailWord_3937878
  simp only [CollatzResearch.WordTrace]
  refine ⟨8976638126734251054011393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 95750806685165344576121525 8976638126734251054011393)
  ·
    refine ⟨6732478595050688290508545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8976638126734251054011393 6732478595050688290508545)
    ·
      refine ⟨5049358946288016217881409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6732478595050688290508545 5049358946288016217881409)
      ·
        refine ⟨3787019209716012163411057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5049358946288016217881409 3787019209716012163411057)
        ·
          refine ⟨2840264407287009122558293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3787019209716012163411057 2840264407287009122558293)
          ·
            refine ⟨8321087130723659538745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2840264407287009122558293 8321087130723659538745)
            ·
              rfl

theorem cell23_3937878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 10].length) (baseStart_3937878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3937878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3937878 prefixEnd_3937878 := by exact prefixLift 3937878
  have htrace : WordTrace (prefixWord ++ tailWord_3937878) baseStart_3937878 baseEnd_3937878 := by
    simpa [prefixWord, tailWord_3937878, baseEnd_3937878] using wordTrace_append hprefix tailTrace_3937878
  have hstable : (prefixWord ++ tailWord_3937878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3937878).length < 2 ^ (prefixWord ++ tailWord_3937878).sum := by decide
  have hdescent : baseEnd_3937878 < baseStart_3937878 := by decide
  rcases family_descends (prefixWord ++ tailWord_3937878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3937881 : List Nat := [1, 2, 1, 2, 2, 1, 1, 7, 1, 3, 2]
def baseStart_3937881 : Nat := 118140960795 + 3937881 * 2 ^ 59
def prefixEnd_3937881 : Nat := 4983230072969 + 3 ^ 40 * 3937881 * 2
def baseEnd_3937881 : Nat := 2022025713207812756177521

theorem tailTrace_3937881 : CollatzResearch.WordTrace tailWord_3937881 prefixEnd_3937881 2022025713207812756177521 := by
  unfold tailWord_3937881
  simp only [CollatzResearch.WordTrace]
  refine ⟨143626319446737148376541497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95750879631158098917694331 143626319446737148376541497)
  ·
    refine ⟨107719739585052861282406123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143626319446737148376541497 107719739585052861282406123)
    ·
      refine ⟨161579609377579291923609185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107719739585052861282406123 161579609377579291923609185)
      ·
        refine ⟨121184707033184468942706889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161579609377579291923609185 121184707033184468942706889)
        ·
          refine ⟨90888530274888351707030167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121184707033184468942706889 90888530274888351707030167)
          ·
            refine ⟨136332795412332527560545251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90888530274888351707030167 136332795412332527560545251)
            ·
              refine ⟨204499193118498791340817877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136332795412332527560545251 204499193118498791340817877)
              ·
                refine ⟨4792949838714815422050419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 204499193118498791340817877 4792949838714815422050419)
                ·
                  refine ⟨7189424758072223133075629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4792949838714815422050419 7189424758072223133075629)
                  ·
                    refine ⟨2696034284277083674903361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7189424758072223133075629 2696034284277083674903361)
                    ·
                      refine ⟨2022025713207812756177521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2696034284277083674903361 2022025713207812756177521)
                      ·
                        rfl

theorem cell23_3937881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 7, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 7, 1, 3, 2].length) (baseStart_3937881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3937881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3937881 prefixEnd_3937881 := by exact prefixLift 3937881
  have htrace : WordTrace (prefixWord ++ tailWord_3937881) baseStart_3937881 baseEnd_3937881 := by
    simpa [prefixWord, tailWord_3937881, baseEnd_3937881] using wordTrace_append hprefix tailTrace_3937881
  have hstable : (prefixWord ++ tailWord_3937881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3937881).length < 2 ^ (prefixWord ++ tailWord_3937881).sum := by decide
  have hdescent : baseEnd_3937881 < baseStart_3937881 := by decide
  rcases family_descends (prefixWord ++ tailWord_3937881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3937897 : List Nat := [1, 2, 1, 1, 1, 4, 2, 2, 1, 3, 5]
def baseStart_3937897 : Nat := 118140960795 + 3937897 * 2 ^ 59
def prefixEnd_3937897 : Nat := 4983230072969 + 3 ^ 40 * 3937897 * 2
def baseEnd_3937897 : Nat := 2022033928898284693577447

theorem tailTrace_3937897 : CollatzResearch.WordTrace tailWord_3937897 prefixEnd_3937897 2022033928898284693577447 := by
  unfold tailWord_3937897
  simp only [CollatzResearch.WordTrace]
  refine ⟨143626903014679183109123945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95751268676452788739415963 143626903014679183109123945)
  ·
    refine ⟨107720177261009387331842959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143626903014679183109123945 107720177261009387331842959)
    ·
      refine ⟨161580265891514080997764439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107720177261009387331842959 161580265891514080997764439)
      ·
        refine ⟨242370398837271121496646659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161580265891514080997764439 242370398837271121496646659)
        ·
          refine ⟨363555598255906682244969989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242370398837271121496646659 363555598255906682244969989)
          ·
            refine ⟨68166674672982502920931873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 363555598255906682244969989 68166674672982502920931873)
            ·
              refine ⟨51125006004736877190698905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68166674672982502920931873 51125006004736877190698905)
              ·
                refine ⟨38343754503552657893024179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51125006004736877190698905 38343754503552657893024179)
                ·
                  refine ⟨57515631755328986839536269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38343754503552657893024179 57515631755328986839536269)
                  ·
                    refine ⟨21568361908248370064826101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 57515631755328986839536269 21568361908248370064826101)
                    ·
                      refine ⟨2022033928898284693577447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21568361908248370064826101 2022033928898284693577447)
                      ·
                        rfl

theorem cell23_3937897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 2, 1, 3, 5].length) (baseStart_3937897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3937897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3937897 prefixEnd_3937897 := by exact prefixLift 3937897
  have htrace : WordTrace (prefixWord ++ tailWord_3937897) baseStart_3937897 baseEnd_3937897 := by
    simpa [prefixWord, tailWord_3937897, baseEnd_3937897] using wordTrace_append hprefix tailTrace_3937897
  have hstable : (prefixWord ++ tailWord_3937897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3937897).length < 2 ^ (prefixWord ++ tailWord_3937897).sum := by decide
  have hdescent : baseEnd_3937897 < baseStart_3937897 := by decide
  rcases family_descends (prefixWord ++ tailWord_3937897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3937904 : List Nat := [2, 1, 1, 1, 6, 2, 1, 1, 2, 6]
def baseStart_3937904 : Nat := 118140960795 + 3937904 * 2 ^ 59
def prefixEnd_3937904 : Nat := 4983230072969 + 3 ^ 40 * 3937904 * 2
def baseEnd_3937904 : Nat := 674012507754288722063305

theorem tailTrace_3937904 : CollatzResearch.WordTrace tailWord_3937904 prefixEnd_3937904 674012507754288722063305 := by
  unfold tailWord_3937904
  simp only [CollatzResearch.WordTrace]
  refine ⟨71813579162826911652314383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95751438883769215536419177 71813579162826911652314383)
  ·
    refine ⟨107720368744240367478471575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71813579162826911652314383 107720368744240367478471575)
    ·
      refine ⟨161580553116360551217707363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107720368744240367478471575 161580553116360551217707363)
      ·
        refine ⟨242370829674540826826561045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161580553116360551217707363 242370829674540826826561045)
        ·
          refine ⟨11361132640994101257495049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 242370829674540826826561045 11361132640994101257495049)
          ·
            refine ⟨8520849480745575943121287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11361132640994101257495049 8520849480745575943121287)
            ·
              refine ⟨12781274221118363914681931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8520849480745575943121287 12781274221118363914681931)
              ·
                refine ⟨19171911331677545872022897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12781274221118363914681931 19171911331677545872022897)
                ·
                  refine ⟨14378933498758159404017173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19171911331677545872022897 14378933498758159404017173)
                  ·
                    refine ⟨674012507754288722063305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14378933498758159404017173 674012507754288722063305)
                    ·
                      rfl

theorem cell23_3937904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 1, 1, 2, 6].length) (baseStart_3937904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3937904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3937904 prefixEnd_3937904 := by exact prefixLift 3937904
  have htrace : WordTrace (prefixWord ++ tailWord_3937904) baseStart_3937904 baseEnd_3937904 := by
    simpa [prefixWord, tailWord_3937904, baseEnd_3937904] using wordTrace_append hprefix tailTrace_3937904
  have hstable : (prefixWord ++ tailWord_3937904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3937904).length < 2 ^ (prefixWord ++ tailWord_3937904).sum := by decide
  have hdescent : baseEnd_3937904 < baseStart_3937904 := by decide
  rcases family_descends (prefixWord ++ tailWord_3937904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
