import V185TrunkScan23Chunk0087

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_522819 : List Nat := [1, 1, 1, 3, 1, 2, 1, 5, 4, 4]
def baseStart_522819 : Nat := 118140960795 + 522819 * 2 ^ 59
def prefixEnd_522819 : Nat := 4983230072969 + 3 ^ 40 * 522819 * 2
def baseEnd_522819 : Nat := 89485814101031733986035

theorem tailTrace_522819 : CollatzResearch.WordTrace tailWord_522819 prefixEnd_522819 89485814101031733986035 := by
  unfold tailWord_522819
  simp only [CollatzResearch.WordTrace]
  refine ⟨19068775492923528221539511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12712516995282352147693007 19068775492923528221539511)
  ·
    refine ⟨28603163239385292332309267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19068775492923528221539511 28603163239385292332309267)
    ·
      refine ⟨42904744859077938498463901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28603163239385292332309267 42904744859077938498463901)
      ·
        refine ⟨16089279322154226936923963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42904744859077938498463901 16089279322154226936923963)
        ·
          refine ⟨24133918983231340405385945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16089279322154226936923963 24133918983231340405385945)
          ·
            refine ⟨18100439237423505304039459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24133918983231340405385945 18100439237423505304039459)
            ·
              refine ⟨27150658856135257956059189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18100439237423505304039459 27150658856135257956059189)
              ·
                refine ⟨2545374267762680433380549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27150658856135257956059189 2545374267762680433380549)
                ·
                  refine ⟨477257675205502581258853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2545374267762680433380549 477257675205502581258853)
                  ·
                    refine ⟨89485814101031733986035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 477257675205502581258853 89485814101031733986035)
                    ·
                      rfl

theorem cell23_522819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 5, 4, 4].length) (baseStart_522819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_522819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_522819 prefixEnd_522819 := by exact prefixLift 522819
  have htrace : WordTrace (prefixWord ++ tailWord_522819) baseStart_522819 baseEnd_522819 := by
    simpa [prefixWord, tailWord_522819, baseEnd_522819] using wordTrace_append hprefix tailTrace_522819
  have hstable : (prefixWord ++ tailWord_522819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522819).length < 2 ^ (prefixWord ++ tailWord_522819).sum := by decide
  have hdescent : baseEnd_522819 < baseStart_522819 := by decide
  rcases family_descends (prefixWord ++ tailWord_522819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522832 : List Nat := [2, 1, 1, 1, 1, 3, 2, 12]
def baseStart_522832 : Nat := 118140960795 + 522832 * 2 ^ 59
def prefixEnd_522832 : Nat := 4983230072969 + 3 ^ 40 * 522832 * 2
def baseEnd_522832 : Nat := 9943115464874209299835

theorem tailTrace_522832 : CollatzResearch.WordTrace tailWord_522832 prefixEnd_522832 9943115464874209299835 := by
  unfold tailWord_522832
  simp only [CollatzResearch.WordTrace]
  refine ⟨9534624820938215720881375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12712833094584287627841833 9534624820938215720881375)
  ·
    refine ⟨14301937231407323581322063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9534624820938215720881375 14301937231407323581322063)
    ·
      refine ⟨21452905847110985371983095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14301937231407323581322063 21452905847110985371983095)
      ·
        refine ⟨32179358770666478057974643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21452905847110985371983095 32179358770666478057974643)
        ·
          refine ⟨48269038155999717086961965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32179358770666478057974643 48269038155999717086961965)
          ·
            refine ⟨18100889308499893907610737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48269038155999717086961965 18100889308499893907610737)
            ·
              refine ⟨13575666981374920430708053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18100889308499893907610737 13575666981374920430708053)
              ·
                refine ⟨9943115464874209299835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 13575666981374920430708053 9943115464874209299835)
                ·
                  rfl

theorem cell23_522832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 12].length) (baseStart_522832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_522832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_522832 prefixEnd_522832 := by exact prefixLift 522832
  have htrace : WordTrace (prefixWord ++ tailWord_522832) baseStart_522832 baseEnd_522832 := by
    simpa [prefixWord, tailWord_522832, baseEnd_522832] using wordTrace_append hprefix tailTrace_522832
  have hstable : (prefixWord ++ tailWord_522832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522832).length < 2 ^ (prefixWord ++ tailWord_522832).sum := by decide
  have hdescent : baseEnd_522832 < baseStart_522832 := by decide
  rcases family_descends (prefixWord ++ tailWord_522832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522836 : List Nat := [2, 4, 1, 1, 1, 4, 2, 1, 1, 6]
def baseStart_522836 : Nat := 118140960795 + 522836 * 2 ^ 59
def prefixEnd_522836 : Nat := 4983230072969 + 3 ^ 40 * 522836 * 2
def baseEnd_522836 : Nat := 89488723824740545148509

theorem tailTrace_522836 : CollatzResearch.WordTrace tailWord_522836 prefixEnd_522836 89488723824740545148509 := by
  unfold tailWord_522836
  simp only [CollatzResearch.WordTrace]
  refine ⟨9534697766930970062454181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12712930355907960083272241 9534697766930970062454181)
  ·
    refine ⟨1787755831299556886710159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9534697766930970062454181 1787755831299556886710159)
    ·
      refine ⟨2681633746949335330065239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1787755831299556886710159 2681633746949335330065239)
      ·
        refine ⟨4022450620424002995097859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2681633746949335330065239 4022450620424002995097859)
        ·
          refine ⟨6033675930636004492646789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4022450620424002995097859 6033675930636004492646789)
          ·
            refine ⟨1131314236994250842371273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6033675930636004492646789 1131314236994250842371273)
            ·
              refine ⟨848485677745688131778455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1131314236994250842371273 848485677745688131778455)
              ·
                refine ⟨1272728516618532197667683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 848485677745688131778455 1272728516618532197667683)
                ·
                  refine ⟨1909092774927798296501525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1272728516618532197667683 1909092774927798296501525)
                  ·
                    refine ⟨89488723824740545148509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1909092774927798296501525 89488723824740545148509)
                    ·
                      rfl

theorem cell23_522836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 2, 1, 1, 6].length) (baseStart_522836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_522836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_522836 prefixEnd_522836 := by exact prefixLift 522836
  have htrace : WordTrace (prefixWord ++ tailWord_522836) baseStart_522836 baseEnd_522836 := by
    simpa [prefixWord, tailWord_522836, baseEnd_522836] using wordTrace_append hprefix tailTrace_522836
  have hstable : (prefixWord ++ tailWord_522836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522836).length < 2 ^ (prefixWord ++ tailWord_522836).sum := by decide
  have hdescent : baseEnd_522836 < baseStart_522836 := by decide
  rcases family_descends (prefixWord ++ tailWord_522836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522859 : List Nat := [1, 1, 1, 1, 2, 2, 1, 5, 3, 3, 3]
def baseStart_522859 : Nat := 118140960795 + 522859 * 2 ^ 59
def prefixEnd_522859 : Nat := 4983230072969 + 3 ^ 40 * 522859 * 2
def baseEnd_522859 : Nat := 268477981529275045457921

theorem tailTrace_522859 : CollatzResearch.WordTrace tailWord_522859 prefixEnd_522859 268477981529275045457921 := by
  unfold tailWord_522859
  simp only [CollatzResearch.WordTrace]
  refine ⟨19070234412778615052995631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12713489608519076701997087 19070234412778615052995631)
  ·
    refine ⟨28605351619167922579493447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19070234412778615052995631 28605351619167922579493447)
    ·
      refine ⟨42908027428751883869240171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28605351619167922579493447 42908027428751883869240171)
      ·
        refine ⟨64362041143127825803860257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42908027428751883869240171 64362041143127825803860257)
        ·
          refine ⟨48271530857345869352895193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64362041143127825803860257 48271530857345869352895193)
          ·
            refine ⟨36203648143009402014671395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48271530857345869352895193 36203648143009402014671395)
            ·
              refine ⟨54305472214514103022007093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36203648143009402014671395 54305472214514103022007093)
              ·
                refine ⟨5091138020110697158313165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 54305472214514103022007093 5091138020110697158313165)
                ·
                  refine ⟨1909176757541511434367437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5091138020110697158313165 1909176757541511434367437)
                  ·
                    refine ⟨715941284078066787887789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1909176757541511434367437 715941284078066787887789)
                    ·
                      refine ⟨268477981529275045457921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 715941284078066787887789 268477981529275045457921)
                      ·
                        rfl

theorem cell23_522859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 5, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 5, 3, 3, 3].length) (baseStart_522859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_522859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_522859 prefixEnd_522859 := by exact prefixLift 522859
  have htrace : WordTrace (prefixWord ++ tailWord_522859) baseStart_522859 baseEnd_522859 := by
    simpa [prefixWord, tailWord_522859, baseEnd_522859] using wordTrace_append hprefix tailTrace_522859
  have hstable : (prefixWord ++ tailWord_522859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522859).length < 2 ^ (prefixWord ++ tailWord_522859).sum := by decide
  have hdescent : baseEnd_522859 < baseStart_522859 := by decide
  rcases family_descends (prefixWord ++ tailWord_522859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522860 : List Nat := [2, 2, 1, 1, 3, 1, 3, 5, 1, 2, 2]
def baseStart_522860 : Nat := 118140960795 + 522860 * 2 ^ 59
def prefixEnd_522860 : Nat := 4983230072969 + 3 ^ 40 * 522860 * 2
def baseEnd_522860 : Nat := 268478495009929541545417

theorem tailTrace_522860 : CollatzResearch.WordTrace tailWord_522860 prefixEnd_522860 268478495009929541545417 := by
  unfold tailWord_522860
  simp only [CollatzResearch.WordTrace]
  refine ⟨9535135442887496111891017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12713513923849994815854689 9535135442887496111891017)
  ·
    refine ⟨7151351582165622083918263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9535135442887496111891017 7151351582165622083918263)
    ·
      refine ⟨10727027373248433125877395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7151351582165622083918263 10727027373248433125877395)
      ·
        refine ⟨16090541059872649688816093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10727027373248433125877395 16090541059872649688816093)
        ·
          refine ⟨6033952897452243633306035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16090541059872649688816093 6033952897452243633306035)
          ·
            refine ⟨9050929346178365449959053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6033952897452243633306035 9050929346178365449959053)
            ·
              refine ⟨3394098504816887043734645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9050929346178365449959053 3394098504816887043734645)
              ·
                refine ⟨318196734826583160350123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3394098504816887043734645 318196734826583160350123)
                ·
                  refine ⟨477295102239874740525185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 318196734826583160350123 477295102239874740525185)
                  ·
                    refine ⟨357971326679906055393889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 477295102239874740525185 357971326679906055393889)
                    ·
                      refine ⟨268478495009929541545417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 357971326679906055393889 268478495009929541545417)
                      ·
                        rfl

theorem cell23_522860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 5, 1, 2, 2].length) (baseStart_522860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_522860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_522860 prefixEnd_522860 := by exact prefixLift 522860
  have htrace : WordTrace (prefixWord ++ tailWord_522860) baseStart_522860 baseEnd_522860 := by
    simpa [prefixWord, tailWord_522860, baseEnd_522860] using wordTrace_append hprefix tailTrace_522860
  have hstable : (prefixWord ++ tailWord_522860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522860).length < 2 ^ (prefixWord ++ tailWord_522860).sum := by decide
  have hdescent : baseEnd_522860 < baseStart_522860 := by decide
  rcases family_descends (prefixWord ++ tailWord_522860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522863 : List Nat := [1, 1, 2, 1, 3, 2, 6, 1, 1, 2, 3]
def baseStart_522863 : Nat := 118140960795 + 522863 * 2 ^ 59
def prefixEnd_522863 : Nat := 4983230072969 + 3 ^ 40 * 522863 * 2
def baseEnd_522863 : Nat := 268480035451893029807903

theorem tailTrace_522863 : CollatzResearch.WordTrace tailWord_522863 prefixEnd_522863 268480035451893029807903 := by
  unfold tailWord_522863
  simp only [CollatzResearch.WordTrace]
  refine ⟨19070380304764123736141243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12713586869842749157427495 19070380304764123736141243)
  ·
    refine ⟨28605570457146185604211865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19070380304764123736141243 28605570457146185604211865)
    ·
      refine ⟨21454177842859639203158899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28605570457146185604211865 21454177842859639203158899)
      ·
        refine ⟨32181266764289458804738349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21454177842859639203158899 32181266764289458804738349)
        ·
          refine ⟨12067975036608547051776881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32181266764289458804738349 12067975036608547051776881)
          ·
            refine ⟨9050981277456410288832661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12067975036608547051776881 9050981277456410288832661)
            ·
              refine ⟨424264747380769232289031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 9050981277456410288832661 424264747380769232289031)
              ·
                refine ⟨636397121071153848433547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 424264747380769232289031 636397121071153848433547)
                ·
                  refine ⟨954595681606730772650321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 636397121071153848433547 954595681606730772650321)
                  ·
                    refine ⟨715946761205048079487741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 954595681606730772650321 715946761205048079487741)
                    ·
                      refine ⟨268480035451893029807903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 715946761205048079487741 268480035451893029807903)
                      ·
                        rfl

theorem cell23_522863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 6, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 6, 1, 1, 2, 3].length) (baseStart_522863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_522863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_522863 prefixEnd_522863 := by exact prefixLift 522863
  have htrace : WordTrace (prefixWord ++ tailWord_522863) baseStart_522863 baseEnd_522863 := by
    simpa [prefixWord, tailWord_522863, baseEnd_522863] using wordTrace_append hprefix tailTrace_522863
  have hstable : (prefixWord ++ tailWord_522863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522863).length < 2 ^ (prefixWord ++ tailWord_522863).sum := by decide
  have hdescent : baseEnd_522863 < baseStart_522863 := by decide
  rcases family_descends (prefixWord ++ tailWord_522863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522890 : List Nat := [3, 1, 2, 3, 4, 1, 1, 1, 1, 2, 4]
def baseStart_522890 : Nat := 118140960795 + 522890 * 2 ^ 59
def prefixEnd_522890 : Nat := 4983230072969 + 3 ^ 40 * 522890 * 2
def baseEnd_522890 : Nat := 268493899429564424170279

theorem tailTrace_522890 : CollatzResearch.WordTrace tailWord_522890 prefixEnd_522890 268493899429564424170279 := by
  unfold tailWord_522890
  simp only [CollatzResearch.WordTrace]
  refine ⟨4767841268916576836843531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12714243383777538231582749 4767841268916576836843531)
  ·
    refine ⟨7151761903374865255265297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4767841268916576836843531 7151761903374865255265297)
    ·
      refine ⟨5363821427531148941448973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7151761903374865255265297 5363821427531148941448973)
      ·
        refine ⟨2011433035324180853043365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5363821427531148941448973 2011433035324180853043365)
        ·
          refine ⟨377143694123283909945631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2011433035324180853043365 377143694123283909945631)
          ·
            refine ⟨565715541184925864918447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 377143694123283909945631 565715541184925864918447)
            ·
              refine ⟨848573311777388797377671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 565715541184925864918447 848573311777388797377671)
              ·
                refine ⟨1272859967666083196066507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 848573311777388797377671 1272859967666083196066507)
                ·
                  refine ⟨1909289951499124794099761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1272859967666083196066507 1909289951499124794099761)
                  ·
                    refine ⟨1431967463624343595574821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1909289951499124794099761 1431967463624343595574821)
                    ·
                      refine ⟨268493899429564424170279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1431967463624343595574821 268493899429564424170279)
                      ·
                        rfl

theorem cell23_522890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 1, 1, 1, 2, 4].length) (baseStart_522890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_522890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_522890 prefixEnd_522890 := by exact prefixLift 522890
  have htrace : WordTrace (prefixWord ++ tailWord_522890) baseStart_522890 baseEnd_522890 := by
    simpa [prefixWord, tailWord_522890, baseEnd_522890] using wordTrace_append hprefix tailTrace_522890
  have hstable : (prefixWord ++ tailWord_522890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522890).length < 2 ^ (prefixWord ++ tailWord_522890).sum := by decide
  have hdescent : baseEnd_522890 < baseStart_522890 := by decide
  rcases family_descends (prefixWord ++ tailWord_522890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522909 : List Nat := [1, 4, 2, 1, 1, 1, 2, 2, 1, 8]
def baseStart_522909 : Nat := 118140960795 + 522909 * 2 ^ 59
def prefixEnd_522909 : Nat := 4983230072969 + 3 ^ 40 * 522909 * 2
def baseEnd_522909 : Nat := 89501218520666616610897

theorem tailTrace_522909 : CollatzResearch.WordTrace tailWord_522909 prefixEnd_522909 89501218520666616610897 := by
  unfold tailWord_522909
  simp only [CollatzResearch.WordTrace]
  refine ⟨19072058062597473592315781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12714705375064982394877187 19072058062597473592315781)
  ·
    refine ⟨3576010886737026298559209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19072058062597473592315781 3576010886737026298559209)
    ·
      refine ⟨2682008165052769723919407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3576010886737026298559209 2682008165052769723919407)
      ·
        refine ⟨4023012247579154585879111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2682008165052769723919407 4023012247579154585879111)
        ·
          refine ⟨6034518371368731878818667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4023012247579154585879111 6034518371368731878818667)
          ·
            refine ⟨9051777557053097818228001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6034518371368731878818667 9051777557053097818228001)
            ·
              refine ⟨6788833167789823363671001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9051777557053097818228001 6788833167789823363671001)
              ·
                refine ⟨5091624875842367522753251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6788833167789823363671001 5091624875842367522753251)
                ·
                  refine ⟨7637437313763551284129877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5091624875842367522753251 7637437313763551284129877)
                  ·
                    refine ⟨89501218520666616610897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 7637437313763551284129877 89501218520666616610897)
                    ·
                      rfl

theorem cell23_522909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 2, 1, 8].length) (baseStart_522909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_522909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_522909 prefixEnd_522909 := by exact prefixLift 522909
  have htrace : WordTrace (prefixWord ++ tailWord_522909) baseStart_522909 baseEnd_522909 := by
    simpa [prefixWord, tailWord_522909, baseEnd_522909] using wordTrace_append hprefix tailTrace_522909
  have hstable : (prefixWord ++ tailWord_522909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522909).length < 2 ^ (prefixWord ++ tailWord_522909).sum := by decide
  have hdescent : baseEnd_522909 < baseStart_522909 := by decide
  rcases family_descends (prefixWord ++ tailWord_522909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522990 : List Nat := [4, 1, 2, 1, 1, 3, 4, 2, 5]
def baseStart_522990 : Nat := 118140960795 + 522990 * 2 ^ 59
def prefixEnd_522990 : Nat := 4983230072969 + 3 ^ 40 * 522990 * 2
def baseEnd_522990 : Nat := 29838360832779336991091

theorem tailTrace_522990 : CollatzResearch.WordTrace tailWord_522990 prefixEnd_522990 29838360832779336991091 := by
  unfold tailWord_522990
  simp only [CollatzResearch.WordTrace]
  refine ⟨2384376546913003053251803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12716674916869349617342949 2384376546913003053251803)
  ·
    refine ⟨3576564820369504579877705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2384376546913003053251803 3576564820369504579877705)
    ·
      refine ⟨2682423615277128434908279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3576564820369504579877705 2682423615277128434908279)
      ·
        refine ⟨4023635422915692652362419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2682423615277128434908279 4023635422915692652362419)
        ·
          refine ⟨6035453134373538978543629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4023635422915692652362419 6035453134373538978543629)
          ·
            refine ⟨2263294925390077116953861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6035453134373538978543629 2263294925390077116953861)
            ·
              refine ⟨424367798510639459428849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2263294925390077116953861 424367798510639459428849)
              ·
                refine ⟨318275848882979594571637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 424367798510639459428849 318275848882979594571637)
                ·
                  refine ⟨29838360832779336991091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 318275848882979594571637 29838360832779336991091)
                  ·
                    rfl

theorem cell23_522990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 4, 2, 5].length) (baseStart_522990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_522990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_522990 prefixEnd_522990 := by exact prefixLift 522990
  have htrace : WordTrace (prefixWord ++ tailWord_522990) baseStart_522990 baseEnd_522990 := by
    simpa [prefixWord, tailWord_522990, baseEnd_522990] using wordTrace_append hprefix tailTrace_522990
  have hstable : (prefixWord ++ tailWord_522990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522990).length < 2 ^ (prefixWord ++ tailWord_522990).sum := by decide
  have hdescent : baseEnd_522990 < baseStart_522990 := by decide
  rcases family_descends (prefixWord ++ tailWord_522990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522997 : List Nat := [1, 3, 6, 1, 1, 1, 1, 1, 2, 2, 4]
def baseStart_522997 : Nat := 118140960795 + 522997 * 2 ^ 59
def prefixEnd_522997 : Nat := 4983230072969 + 3 ^ 40 * 522997 * 2
def baseEnd_522997 : Nat := 268548841859595505532287

theorem tailTrace_522997 : CollatzResearch.WordTrace tailWord_522997 prefixEnd_522997 268548841859595505532287 := by
  unfold tailWord_522997
  simp only [CollatzResearch.WordTrace]
  refine ⟨19075267686278664621519245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12716845124185776414346163 19075267686278664621519245)
  ·
    refine ⟨7153225382354499233069717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19075267686278664621519245 7153225382354499233069717)
    ·
      refine ⟨335307439797867151550143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 7153225382354499233069717 335307439797867151550143)
      ·
        refine ⟨502961159696800727325215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 335307439797867151550143 502961159696800727325215)
        ·
          refine ⟨754441739545201090987823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 502961159696800727325215 754441739545201090987823)
          ·
            refine ⟨1131662609317801636481735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 754441739545201090987823 1131662609317801636481735)
            ·
              refine ⟨1697493913976702454722603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1131662609317801636481735 1697493913976702454722603)
              ·
                refine ⟨2546240870965053682083905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1697493913976702454722603 2546240870965053682083905)
                ·
                  refine ⟨1909680653223790261562929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2546240870965053682083905 1909680653223790261562929)
                  ·
                    refine ⟨1432260489917842696172197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1909680653223790261562929 1432260489917842696172197)
                    ·
                      refine ⟨268548841859595505532287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1432260489917842696172197 268548841859595505532287)
                      ·
                        rfl

theorem cell23_522997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 1, 1, 2, 2, 4].length) (baseStart_522997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_522997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_522997 prefixEnd_522997 := by exact prefixLift 522997
  have htrace : WordTrace (prefixWord ++ tailWord_522997) baseStart_522997 baseEnd_522997 := by
    simpa [prefixWord, tailWord_522997, baseEnd_522997] using wordTrace_append hprefix tailTrace_522997
  have hstable : (prefixWord ++ tailWord_522997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522997).length < 2 ^ (prefixWord ++ tailWord_522997).sum := by decide
  have hdescent : baseEnd_522997 < baseStart_522997 := by decide
  rcases family_descends (prefixWord ++ tailWord_522997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522999 : List Nat := [1, 1, 3, 1, 1, 1, 3, 2, 2, 8]
def baseStart_522999 : Nat := 118140960795 + 522999 * 2 ^ 59
def prefixEnd_522999 : Nat := 4983230072969 + 3 ^ 40 * 522999 * 2
def baseEnd_522999 : Nat := 89516622940301499235759

theorem tailTrace_522999 : CollatzResearch.WordTrace tailWord_522999 prefixEnd_522999 89516622940301499235759 := by
  unfold tailWord_522999
  simp only [CollatzResearch.WordTrace]
  refine ⟨19075340632271418963092051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12716893754847612642061367 19075340632271418963092051)
  ·
    refine ⟨28613010948407128444638077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19075340632271418963092051 28613010948407128444638077)
    ·
      refine ⟨10729879105652673166739279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28613010948407128444638077 10729879105652673166739279)
      ·
        refine ⟨16094818658479009750108919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10729879105652673166739279 16094818658479009750108919)
        ·
          refine ⟨24142227987718514625163379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16094818658479009750108919 24142227987718514625163379)
          ·
            refine ⟨36213341981577771937745069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24142227987718514625163379 36213341981577771937745069)
            ·
              refine ⟨13580003243091664476654401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36213341981577771937745069 13580003243091664476654401)
              ·
                refine ⟨10185002432318748357490801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13580003243091664476654401 10185002432318748357490801)
                ·
                  refine ⟨7638751824239061268118101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10185002432318748357490801 7638751824239061268118101)
                  ·
                    refine ⟨89516622940301499235759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 7638751824239061268118101 89516622940301499235759)
                    ·
                      rfl

theorem cell23_522999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 2, 2, 8].length) (baseStart_522999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_522999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_522999 prefixEnd_522999 := by exact prefixLift 522999
  have htrace : WordTrace (prefixWord ++ tailWord_522999) baseStart_522999 baseEnd_522999 := by
    simpa [prefixWord, tailWord_522999, baseEnd_522999] using wordTrace_append hprefix tailTrace_522999
  have hstable : (prefixWord ++ tailWord_522999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522999).length < 2 ^ (prefixWord ++ tailWord_522999).sum := by decide
  have hdescent : baseEnd_522999 < baseStart_522999 := by decide
  rcases family_descends (prefixWord ++ tailWord_522999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523036 : List Nat := [2, 2, 3, 1, 1, 3, 1, 1, 2, 1, 6]
def baseStart_523036 : Nat := 118140960795 + 523036 * 2 ^ 59
def prefixEnd_523036 : Nat := 4983230072969 + 3 ^ 40 * 523036 * 2
def baseEnd_523036 : Nat := 268568867605120852944607

theorem tailTrace_523036 : CollatzResearch.WordTrace tailWord_523036 prefixEnd_523036 268568867605120852944607 := by
  unfold tailWord_523036
  simp only [CollatzResearch.WordTrace]
  refine ⟨9538345066568687141094481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12717793422091582854792641 9538345066568687141094481)
  ·
    refine ⟨7153758799926515355820861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9538345066568687141094481 7153758799926515355820861)
    ·
      refine ⟨2682659549972443258432823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7153758799926515355820861 2682659549972443258432823)
      ·
        refine ⟨4023989324958664887649235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2682659549972443258432823 4023989324958664887649235)
        ·
          refine ⟨6035983987437997331473853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4023989324958664887649235 6035983987437997331473853)
          ·
            refine ⟨2263493995289248999302695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6035983987437997331473853 2263493995289248999302695)
            ·
              refine ⟨3395240992933873498954043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2263493995289248999302695 3395240992933873498954043)
              ·
                refine ⟨5092861489400810248431065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3395240992933873498954043 5092861489400810248431065)
                ·
                  refine ⟨3819646117050607686323299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5092861489400810248431065 3819646117050607686323299)
                  ·
                    refine ⟨5729469175575911529484949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3819646117050607686323299 5729469175575911529484949)
                    ·
                      refine ⟨268568867605120852944607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 5729469175575911529484949 268568867605120852944607)
                      ·
                        rfl

theorem cell23_523036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 1, 2, 1, 6].length) (baseStart_523036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_523036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_523036 prefixEnd_523036 := by exact prefixLift 523036
  have htrace : WordTrace (prefixWord ++ tailWord_523036) baseStart_523036 baseEnd_523036 := by
    simpa [prefixWord, tailWord_523036, baseEnd_523036] using wordTrace_append hprefix tailTrace_523036
  have hstable : (prefixWord ++ tailWord_523036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523036).length < 2 ^ (prefixWord ++ tailWord_523036).sum := by decide
  have hdescent : baseEnd_523036 < baseStart_523036 := by decide
  rcases family_descends (prefixWord ++ tailWord_523036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523063 : List Nat := [1, 1, 3, 1, 2, 1, 7, 1, 6]
def baseStart_523063 : Nat := 118140960795 + 523063 * 2 ^ 59
def prefixEnd_523063 : Nat := 4983230072969 + 3 ^ 40 * 523063 * 2
def baseEnd_523063 : Nat := 29842525731421360811887

theorem tailTrace_523063 : CollatzResearch.WordTrace tailWord_523063 prefixEnd_523063 29842525731421360811887 := by
  unfold tailWord_523063
  simp only [CollatzResearch.WordTrace]
  refine ⟨19077674904039557893421843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12718449936026371928947895 19077674904039557893421843)
  ·
    refine ⟨28616512356059336840132765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19077674904039557893421843 28616512356059336840132765)
    ·
      refine ⟨10731192133522251315049787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28616512356059336840132765 10731192133522251315049787)
      ·
        refine ⟨16096788200283376972574681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10731192133522251315049787 16096788200283376972574681)
        ·
          refine ⟨12072591150212532729431011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16096788200283376972574681 12072591150212532729431011)
          ·
            refine ⟨18108886725318799094146517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12072591150212532729431011 18108886725318799094146517)
            ·
              refine ⟨424427032624659353769059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 18108886725318799094146517 424427032624659353769059)
              ·
                refine ⟨636640548936989030653589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 424427032624659353769059 636640548936989030653589)
                ·
                  refine ⟨29842525731421360811887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 636640548936989030653589 29842525731421360811887)
                  ·
                    rfl

theorem cell23_523063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 7, 1, 6].length) (baseStart_523063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_523063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_523063 prefixEnd_523063 := by exact prefixLift 523063
  have htrace : WordTrace (prefixWord ++ tailWord_523063) baseStart_523063 baseEnd_523063 := by
    simpa [prefixWord, tailWord_523063, baseEnd_523063] using wordTrace_append hprefix tailTrace_523063
  have hstable : (prefixWord ++ tailWord_523063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523063).length < 2 ^ (prefixWord ++ tailWord_523063).sum := by decide
  have hdescent : baseEnd_523063 < baseStart_523063 := by decide
  rcases family_descends (prefixWord ++ tailWord_523063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523083 : List Nat := [1, 1, 1, 1, 3, 1, 1, 1, 8, 3, 2]
def baseStart_523083 : Nat := 118140960795 + 523083 * 2 ^ 59
def prefixEnd_523083 : Nat := 4983230072969 + 3 ^ 40 * 523083 * 2
def baseEnd_523083 : Nat := 268593001195882169056891

theorem tailTrace_523083 : CollatzResearch.WordTrace tailWord_523083 prefixEnd_523083 268593001195882169056891 := by
  unfold tailWord_523083
  simp only [CollatzResearch.WordTrace]
  refine ⟨19078404363967101309149903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12718936242644734206099935 19078404363967101309149903)
  ·
    refine ⟨28617606545950651963724855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19078404363967101309149903 28617606545950651963724855)
    ·
      refine ⟨42926409818925977945587283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28617606545950651963724855 42926409818925977945587283)
      ·
        refine ⟨64389614728388966918380925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42926409818925977945587283 64389614728388966918380925)
        ·
          refine ⟨24146105523145862594392847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64389614728388966918380925 24146105523145862594392847)
          ·
            refine ⟨36219158284718793891589271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24146105523145862594392847 36219158284718793891589271)
            ·
              refine ⟨54328737427078190837383907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36219158284718793891589271 54328737427078190837383907)
              ·
                refine ⟨81493106140617286256075861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54328737427078190837383907 81493106140617286256075861)
                ·
                  refine ⟨954997337585358823313389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 81493106140617286256075861 954997337585358823313389)
                  ·
                    refine ⟨358124001594509558742521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 954997337585358823313389 358124001594509558742521)
                    ·
                      refine ⟨268593001195882169056891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 358124001594509558742521 268593001195882169056891)
                      ·
                        rfl

theorem cell23_523083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 8, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 8, 3, 2].length) (baseStart_523083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_523083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_523083 prefixEnd_523083 := by exact prefixLift 523083
  have htrace : WordTrace (prefixWord ++ tailWord_523083) baseStart_523083 baseEnd_523083 := by
    simpa [prefixWord, tailWord_523083, baseEnd_523083] using wordTrace_append hprefix tailTrace_523083
  have hstable : (prefixWord ++ tailWord_523083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523083).length < 2 ^ (prefixWord ++ tailWord_523083).sum := by decide
  have hdescent : baseEnd_523083 < baseStart_523083 := by decide
  rcases family_descends (prefixWord ++ tailWord_523083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523093 : List Nat := [1, 3, 2, 2, 2, 1, 1, 5, 1, 5]
def baseStart_523093 : Nat := 118140960795 + 523093 * 2 ^ 59
def prefixEnd_523093 : Nat := 4983230072969 + 3 ^ 40 * 523093 * 2
def baseEnd_523093 : Nat := 89532712000809043310615

theorem tailTrace_523093 : CollatzResearch.WordTrace tailWord_523093 prefixEnd_523093 89532712000809043310615 := by
  unfold tailWord_523093
  simp only [CollatzResearch.WordTrace]
  refine ⟨19078769093930873017013933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12719179395953915344675955 19078769093930873017013933)
  ·
    refine ⟨7154538410224077381380225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19078769093930873017013933 7154538410224077381380225)
    ·
      refine ⟨5365903807668058036035169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7154538410224077381380225 5365903807668058036035169)
      ·
        refine ⟨4024427855751043527026377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5365903807668058036035169 4024427855751043527026377)
        ·
          refine ⟨3018320891813282645269783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4024427855751043527026377 3018320891813282645269783)
          ·
            refine ⟨4527481337719923967904675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3018320891813282645269783 4527481337719923967904675)
            ·
              refine ⟨6791222006579885951857013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4527481337719923967904675 6791222006579885951857013)
              ·
                refine ⟨636677063116864307986595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6791222006579885951857013 636677063116864307986595)
                ·
                  refine ⟨955015594675296461979893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 636677063116864307986595 955015594675296461979893)
                  ·
                    refine ⟨89532712000809043310615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 955015594675296461979893 89532712000809043310615)
                    ·
                      rfl

theorem cell23_523093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 5, 1, 5].length) (baseStart_523093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_523093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_523093 prefixEnd_523093 := by exact prefixLift 523093
  have htrace : WordTrace (prefixWord ++ tailWord_523093) baseStart_523093 baseEnd_523093 := by
    simpa [prefixWord, tailWord_523093, baseEnd_523093] using wordTrace_append hprefix tailTrace_523093
  have hstable : (prefixWord ++ tailWord_523093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523093).length < 2 ^ (prefixWord ++ tailWord_523093).sum := by decide
  have hdescent : baseEnd_523093 < baseStart_523093 := by decide
  rcases family_descends (prefixWord ++ tailWord_523093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523107 : List Nat := [1, 1, 1, 5, 3, 3, 1, 1, 3, 1, 3]
def baseStart_523107 : Nat := 118140960795 + 523107 * 2 ^ 59
def prefixEnd_523107 : Nat := 4983230072969 + 3 ^ 40 * 523107 * 2
def baseEnd_523107 : Nat := 268605324731590075156781

theorem tailTrace_523107 : CollatzResearch.WordTrace tailWord_523107 prefixEnd_523107 268605324731590075156781 := by
  unfold tailWord_523107
  simp only [CollatzResearch.WordTrace]
  refine ⟨19079279715880153408023575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12719519810586768938682383 19079279715880153408023575)
  ·
    refine ⟨28618919573820230112035363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19079279715880153408023575 28618919573820230112035363)
    ·
      refine ⟨42928379360730345168053045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28618919573820230112035363 42928379360730345168053045)
      ·
        refine ⟨4024535565068469859504973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 42928379360730345168053045 4024535565068469859504973)
        ·
          refine ⟨1509200836900676197314365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4024535565068469859504973 1509200836900676197314365)
          ·
            refine ⟨565950313837753573992887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1509200836900676197314365 565950313837753573992887)
            ·
              refine ⟨848925470756630360989331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 565950313837753573992887 848925470756630360989331)
              ·
                refine ⟨1273388206134945541483997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 848925470756630360989331 1273388206134945541483997)
                ·
                  refine ⟨477520577300604578056499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1273388206134945541483997 477520577300604578056499)
                  ·
                    refine ⟨716280865950906867084749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 477520577300604578056499 716280865950906867084749)
                    ·
                      refine ⟨268605324731590075156781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 716280865950906867084749 268605324731590075156781)
                      ·
                        rfl

theorem cell23_523107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 1, 1, 3, 1, 3].length) (baseStart_523107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_523107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_523107 prefixEnd_523107 := by exact prefixLift 523107
  have htrace : WordTrace (prefixWord ++ tailWord_523107) baseStart_523107 baseEnd_523107 := by
    simpa [prefixWord, tailWord_523107, baseEnd_523107] using wordTrace_append hprefix tailTrace_523107
  have hstable : (prefixWord ++ tailWord_523107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523107).length < 2 ^ (prefixWord ++ tailWord_523107).sum := by decide
  have hdescent : baseEnd_523107 < baseStart_523107 := by decide
  rcases family_descends (prefixWord ++ tailWord_523107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523130 : List Nat := [3, 1, 1, 1, 1, 1, 3, 3, 5, 2, 2]
def baseStart_523130 : Nat := 118140960795 + 523130 * 2 ^ 59
def prefixEnd_523130 : Nat := 4983230072969 + 3 ^ 40 * 523130 * 2
def baseEnd_523130 : Nat := 268617134786643485169175

theorem tailTrace_523130 : CollatzResearch.WordTrace tailWord_523130 prefixEnd_523130 268617134786643485169175 := by
  unfold tailWord_523130
  simp only [CollatzResearch.WordTrace]
  refine ⟨4770029648699207084027711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12720079063197885557407229 4770029648699207084027711)
  ·
    refine ⟨7155044473048810626041567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4770029648699207084027711 7155044473048810626041567)
    ·
      refine ⟨10732566709573215939062351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7155044473048810626041567 10732566709573215939062351)
      ·
        refine ⟨16098850064359823908593527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10732566709573215939062351 16098850064359823908593527)
        ·
          refine ⟨24148275096539735862890291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16098850064359823908593527 24148275096539735862890291)
          ·
            refine ⟨36222412644809603794335437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24148275096539735862890291 36222412644809603794335437)
            ·
              refine ⟨13583404741803601422875789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36222412644809603794335437 13583404741803601422875789)
              ·
                refine ⟨5093776778176350533578421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13583404741803601422875789 5093776778176350533578421)
                ·
                  refine ⟨477541572954032862522977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5093776778176350533578421 477541572954032862522977)
                  ·
                    refine ⟨358156179715524646892233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 477541572954032862522977 358156179715524646892233)
                    ·
                      refine ⟨268617134786643485169175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 358156179715524646892233 268617134786643485169175)
                      ·
                        rfl

theorem cell23_523130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 3, 5, 2, 2].length) (baseStart_523130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_523130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_523130 prefixEnd_523130 := by exact prefixLift 523130
  have htrace : WordTrace (prefixWord ++ tailWord_523130) baseStart_523130 baseEnd_523130 := by
    simpa [prefixWord, tailWord_523130, baseEnd_523130] using wordTrace_append hprefix tailTrace_523130
  have hstable : (prefixWord ++ tailWord_523130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523130).length < 2 ^ (prefixWord ++ tailWord_523130).sum := by decide
  have hdescent : baseEnd_523130 < baseStart_523130 := by decide
  rcases family_descends (prefixWord ++ tailWord_523130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523143 : List Nat := [1, 1, 4, 2, 3, 1, 1, 1, 3, 2, 4]
def baseStart_523143 : Nat := 118140960795 + 523143 * 2 ^ 59
def prefixEnd_523143 : Nat := 4983230072969 + 3 ^ 40 * 523143 * 2
def baseEnd_523143 : Nat := 268623810035151934306615

theorem tailTrace_523143 : CollatzResearch.WordTrace tailWord_523143 prefixEnd_523143 268623810035151934306615 := by
  unfold tailWord_523143
  simp only [CollatzResearch.WordTrace]
  refine ⟨19080592743749731556334083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12720395162499821037556055 19080592743749731556334083)
  ·
    refine ⟨28620889115624597334501125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19080592743749731556334083 28620889115624597334501125)
    ·
      refine ⟨5366416709179612000218961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28620889115624597334501125 5366416709179612000218961)
      ·
        refine ⟨4024812531884709000164221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5366416709179612000218961 4024812531884709000164221)
        ·
          refine ⟨1509304699456765875061583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4024812531884709000164221 1509304699456765875061583)
          ·
            refine ⟨2263957049185148812592375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1509304699456765875061583 2263957049185148812592375)
            ·
              refine ⟨3395935573777723218888563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2263957049185148812592375 3395935573777723218888563)
              ·
                refine ⟨5093903360666584828332845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3395935573777723218888563 5093903360666584828332845)
                ·
                  refine ⟨1910213760249969310624817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5093903360666584828332845 1910213760249969310624817)
                  ·
                    refine ⟨1432660320187476982968613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1910213760249969310624817 1432660320187476982968613)
                    ·
                      refine ⟨268623810035151934306615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1432660320187476982968613 268623810035151934306615)
                      ·
                        rfl

theorem cell23_523143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 1, 3, 2, 4].length) (baseStart_523143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_523143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_523143 prefixEnd_523143 := by exact prefixLift 523143
  have htrace : WordTrace (prefixWord ++ tailWord_523143) baseStart_523143 baseEnd_523143 := by
    simpa [prefixWord, tailWord_523143, baseEnd_523143] using wordTrace_append hprefix tailTrace_523143
  have hstable : (prefixWord ++ tailWord_523143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523143).length < 2 ^ (prefixWord ++ tailWord_523143).sum := by decide
  have hdescent : baseEnd_523143 < baseStart_523143 := by decide
  rcases family_descends (prefixWord ++ tailWord_523143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523158 : List Nat := [5, 3, 1, 1, 1, 2, 1, 4, 1, 1, 3]
def baseStart_523158 : Nat := 118140960795 + 523158 * 2 ^ 59
def prefixEnd_523158 : Nat := 4983230072969 + 3 ^ 40 * 523158 * 2
def baseEnd_523158 : Nat := 268631512244969375619047

theorem tailTrace_523158 : CollatzResearch.WordTrace tailWord_523158 prefixEnd_523158 268631512244969375619047 := by
  unfold tailWord_523158
  simp only [CollatzResearch.WordTrace]
  refine ⟨1192571239918461819883133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12720759892463592745420085 1192571239918461819883133)
  ·
    refine ⟨447214214969423182456175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1192571239918461819883133 447214214969423182456175)
    ·
      refine ⟨670821322454134773684263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 447214214969423182456175 670821322454134773684263)
      ·
        refine ⟨1006231983681202160526395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 670821322454134773684263 1006231983681202160526395)
        ·
          refine ⟨1509347975521803240789593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1006231983681202160526395 1509347975521803240789593)
          ·
            refine ⟨1132010981641352430592195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1509347975521803240789593 1132010981641352430592195)
            ·
              refine ⟨1698016472462028645888293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1132010981641352430592195 1698016472462028645888293)
              ·
                refine ⟨318378088586630371104055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1698016472462028645888293 318378088586630371104055)
                ·
                  refine ⟨477567132879945556656083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 318378088586630371104055 477567132879945556656083)
                  ·
                    refine ⟨716350699319918334984125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 477567132879945556656083 716350699319918334984125)
                    ·
                      refine ⟨268631512244969375619047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 716350699319918334984125 268631512244969375619047)
                      ·
                        rfl

theorem cell23_523158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 1, 4, 1, 1, 3].length) (baseStart_523158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_523158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_523158 prefixEnd_523158 := by exact prefixLift 523158
  have htrace : WordTrace (prefixWord ++ tailWord_523158) baseStart_523158 baseEnd_523158 := by
    simpa [prefixWord, tailWord_523158, baseEnd_523158] using wordTrace_append hprefix tailTrace_523158
  have hstable : (prefixWord ++ tailWord_523158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523158).length < 2 ^ (prefixWord ++ tailWord_523158).sum := by decide
  have hdescent : baseEnd_523158 < baseStart_523158 := by decide
  rcases family_descends (prefixWord ++ tailWord_523158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523170 : List Nat := [3, 3, 1, 2, 2, 3, 1, 8]
def baseStart_523170 : Nat := 118140960795 + 523170 * 2 ^ 59
def prefixEnd_523170 : Nat := 4983230072969 + 3 ^ 40 * 523170 * 2
def baseEnd_523170 : Nat := 9949543481956419580333

theorem tailTrace_523170 : CollatzResearch.WordTrace tailWord_523170 prefixEnd_523170 9949543481956419580333 := by
  unfold tailWord_523170
  simp only [CollatzResearch.WordTrace]
  refine ⟨4770394378662978791891741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12721051676434610111711309 4770394378662978791891741)
  ·
    refine ⟨1788897891998617046959403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4770394378662978791891741 1788897891998617046959403)
    ·
      refine ⟨2683346837997925570439105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1788897891998617046959403 2683346837997925570439105)
      ·
        refine ⟨2012510128498444177829329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2683346837997925570439105 2012510128498444177829329)
        ·
          refine ⟨1509382596373833133371997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2012510128498444177829329 1509382596373833133371997)
          ·
            refine ⟨566018473640187425014499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1509382596373833133371997 566018473640187425014499)
            ·
              refine ⟨849027710460281137521749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 566018473640187425014499 849027710460281137521749)
              ·
                refine ⟨9949543481956419580333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 849027710460281137521749 9949543481956419580333)
                ·
                  rfl

theorem cell23_523170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 1, 8].length) (baseStart_523170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_523170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_523170 prefixEnd_523170 := by exact prefixLift 523170
  have htrace : WordTrace (prefixWord ++ tailWord_523170) baseStart_523170 baseEnd_523170 := by
    simpa [prefixWord, tailWord_523170, baseEnd_523170] using wordTrace_append hprefix tailTrace_523170
  have hstable : (prefixWord ++ tailWord_523170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523170).length < 2 ^ (prefixWord ++ tailWord_523170).sum := by decide
  have hdescent : baseEnd_523170 < baseStart_523170 := by decide
  rcases family_descends (prefixWord ++ tailWord_523170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523181 : List Nat := [1, 5, 2, 3, 1, 1, 1, 2, 3, 2, 2]
def baseStart_523181 : Nat := 118140960795 + 523181 * 2 ^ 59
def prefixEnd_523181 : Nat := 4983230072969 + 3 ^ 40 * 523181 * 2
def baseEnd_523181 : Nat := 268643322300022785631441

theorem tailTrace_523181 : CollatzResearch.WordTrace tailWord_523181 prefixEnd_523181 268643322300022785631441 := by
  unfold tailWord_523181
  simp only [CollatzResearch.WordTrace]
  refine ⟨19081978717612064046217397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12721319145074709364144931 19081978717612064046217397)
  ·
    refine ⟨1788935504776131004332881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 19081978717612064046217397 1788935504776131004332881)
    ·
      refine ⟨1341701628582098253249661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1788935504776131004332881 1341701628582098253249661)
      ·
        refine ⟨503138110718286844968623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1341701628582098253249661 503138110718286844968623)
        ·
          refine ⟨754707166077430267452935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 503138110718286844968623 754707166077430267452935)
          ·
            refine ⟨1132060749116145401179403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 754707166077430267452935 1132060749116145401179403)
            ·
              refine ⟨1698091123674218101769105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1132060749116145401179403 1698091123674218101769105)
              ·
                refine ⟨1273568342755663576326829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1698091123674218101769105 1273568342755663576326829)
                ·
                  refine ⟨477588128533373841122561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1273568342755663576326829 477588128533373841122561)
                  ·
                    refine ⟨358191096400030380841921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 477588128533373841122561 358191096400030380841921)
                    ·
                      refine ⟨268643322300022785631441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 358191096400030380841921 268643322300022785631441)
                      ·
                        rfl

theorem cell23_523181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 1, 2, 3, 2, 2].length) (baseStart_523181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_523181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_523181 prefixEnd_523181 := by exact prefixLift 523181
  have htrace : WordTrace (prefixWord ++ tailWord_523181) baseStart_523181 baseEnd_523181 := by
    simpa [prefixWord, tailWord_523181, baseEnd_523181] using wordTrace_append hprefix tailTrace_523181
  have hstable : (prefixWord ++ tailWord_523181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523181).length < 2 ^ (prefixWord ++ tailWord_523181).sum := by decide
  have hdescent : baseEnd_523181 < baseStart_523181 := by decide
  rcases family_descends (prefixWord ++ tailWord_523181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523214 : List Nat := [4, 1, 1, 1, 2, 5, 1, 2, 2, 1, 3]
def baseStart_523214 : Nat := 118140960795 + 523214 * 2 ^ 59
def prefixEnd_523214 : Nat := 4983230072969 + 3 ^ 40 * 523214 * 2
def baseEnd_523214 : Nat := 268660267161621156518789

theorem tailTrace_523214 : CollatzResearch.WordTrace tailWord_523214 prefixEnd_523214 268660267161621156518789 := by
  unfold tailWord_523214
  simp only [CollatzResearch.WordTrace]
  refine ⟨2385397790811563835271087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12722121550995007121445797 2385397790811563835271087)
  ·
    refine ⟨3578096686217345752906631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2385397790811563835271087 3578096686217345752906631)
    ·
      refine ⟨5367145029326018629359947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3578096686217345752906631 5367145029326018629359947)
      ·
        refine ⟨8050717543989027944039921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5367145029326018629359947 8050717543989027944039921)
        ·
          refine ⟨6038038157991770958029941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8050717543989027944039921 6038038157991770958029941)
          ·
            refine ⟨566066077311728527315307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6038038157991770958029941 566066077311728527315307)
            ·
              refine ⟨849099115967592790972961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 566066077311728527315307 849099115967592790972961)
              ·
                refine ⟨636824336975694593229721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 849099115967592790972961 636824336975694593229721)
                ·
                  refine ⟨477618252731770944922291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 636824336975694593229721 477618252731770944922291)
                  ·
                    refine ⟨716427379097656417383437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 477618252731770944922291 716427379097656417383437)
                    ·
                      refine ⟨268660267161621156518789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 716427379097656417383437 268660267161621156518789)
                      ·
                        rfl

theorem cell23_523214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 1, 2, 2, 1, 3].length) (baseStart_523214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_523214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_523214 prefixEnd_523214 := by exact prefixLift 523214
  have htrace : WordTrace (prefixWord ++ tailWord_523214) baseStart_523214 baseEnd_523214 := by
    simpa [prefixWord, tailWord_523214, baseEnd_523214] using wordTrace_append hprefix tailTrace_523214
  have hstable : (prefixWord ++ tailWord_523214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523214).length < 2 ^ (prefixWord ++ tailWord_523214).sum := by decide
  have hdescent : baseEnd_523214 < baseStart_523214 := by decide
  rcases family_descends (prefixWord ++ tailWord_523214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523223 : List Nat := [1, 1, 3, 2, 1, 1, 2, 3, 2, 4, 3]
def baseStart_523223 : Nat := 118140960795 + 523223 * 2 ^ 59
def prefixEnd_523223 : Nat := 4983230072969 + 3 ^ 40 * 523223 * 2
def baseEnd_523223 : Nat := 268664888487511621306247

theorem tailTrace_523223 : CollatzResearch.WordTrace tailWord_523223 prefixEnd_523223 268664888487511621306247 := by
  unfold tailWord_523223
  simp only [CollatzResearch.WordTrace]
  refine ⟨19083510583459905219246323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12722340388973270146164215 19083510583459905219246323)
  ·
    refine ⟨28625265875189857828869485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19083510583459905219246323 28625265875189857828869485)
    ·
      refine ⟨10734474703196196685826057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28625265875189857828869485 10734474703196196685826057)
      ·
        refine ⟨8050856027397147514369543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10734474703196196685826057 8050856027397147514369543)
        ·
          refine ⟨12076284041095721271554315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8050856027397147514369543 12076284041095721271554315)
          ·
            refine ⟨18114426061643581907331473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12076284041095721271554315 18114426061643581907331473)
            ·
              refine ⟨13585819546232686430498605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18114426061643581907331473 13585819546232686430498605)
              ·
                refine ⟨5094682329837257411436977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13585819546232686430498605 5094682329837257411436977)
                ·
                  refine ⟨3821011747377943058577733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5094682329837257411436977 3821011747377943058577733)
                  ·
                    refine ⟨716439702633364323483325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3821011747377943058577733 716439702633364323483325)
                    ·
                      refine ⟨268664888487511621306247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 716439702633364323483325 268664888487511621306247)
                      ·
                        rfl

theorem cell23_523223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 3, 2, 4, 3].length) (baseStart_523223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_523223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_523223 prefixEnd_523223 := by exact prefixLift 523223
  have htrace : WordTrace (prefixWord ++ tailWord_523223) baseStart_523223 baseEnd_523223 := by
    simpa [prefixWord, tailWord_523223, baseEnd_523223] using wordTrace_append hprefix tailTrace_523223
  have hstable : (prefixWord ++ tailWord_523223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523223).length < 2 ^ (prefixWord ++ tailWord_523223).sum := by decide
  have hdescent : baseEnd_523223 < baseStart_523223 := by decide
  rcases family_descends (prefixWord ++ tailWord_523223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523254 : List Nat := [5, 1, 1, 1, 3, 1, 1, 2, 4, 2, 2]
def baseStart_523254 : Nat := 118140960795 + 523254 * 2 ^ 59
def prefixEnd_523254 : Nat := 4983230072969 + 3 ^ 40 * 523254 * 2
def baseEnd_523254 : Nat := 268680806387801000018605

theorem tailTrace_523254 : CollatzResearch.WordTrace tailWord_523254 prefixEnd_523254 268680806387801000018605 := by
  unfold tailWord_523254
  simp only [CollatzResearch.WordTrace]
  refine ⟨1192790077896724844601551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12723094164231731675749877 1192790077896724844601551)
  ·
    refine ⟨1789185116845087266902327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1192790077896724844601551 1789185116845087266902327)
    ·
      refine ⟨2683777675267630900353491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1789185116845087266902327 2683777675267630900353491)
      ·
        refine ⟨4025666512901446350530237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2683777675267630900353491 4025666512901446350530237)
        ·
          refine ⟨1509624942338042381448839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4025666512901446350530237 1509624942338042381448839)
          ·
            refine ⟨2264437413507063572173259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1509624942338042381448839 2264437413507063572173259)
            ·
              refine ⟨3396656120260595358259889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2264437413507063572173259 3396656120260595358259889)
              ·
                refine ⟨2547492090195446518694917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3396656120260595358259889 2547492090195446518694917)
                ·
                  refine ⟨477654766911646222255297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2547492090195446518694917 477654766911646222255297)
                  ·
                    refine ⟨358241075183734666691473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 477654766911646222255297 358241075183734666691473)
                    ·
                      refine ⟨268680806387801000018605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 358241075183734666691473 268680806387801000018605)
                      ·
                        rfl

theorem cell23_523254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 2, 4, 2, 2].length) (baseStart_523254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_523254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_523254 prefixEnd_523254 := by exact prefixLift 523254
  have htrace : WordTrace (prefixWord ++ tailWord_523254) baseStart_523254 baseEnd_523254 := by
    simpa [prefixWord, tailWord_523254, baseEnd_523254] using wordTrace_append hprefix tailTrace_523254
  have hstable : (prefixWord ++ tailWord_523254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523254).length < 2 ^ (prefixWord ++ tailWord_523254).sum := by decide
  have hdescent : baseEnd_523254 < baseStart_523254 := by decide
  rcases family_descends (prefixWord ++ tailWord_523254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523282 : List Nat := [3, 2, 5, 1, 2, 1, 2, 1, 2, 1, 3]
def baseStart_523282 : Nat := 118140960795 + 523282 * 2 ^ 59
def prefixEnd_523282 : Nat := 4983230072969 + 3 ^ 40 * 523282 * 2
def baseEnd_523282 : Nat := 268695183846126890468477

theorem tailTrace_523282 : CollatzResearch.WordTrace tailWord_523282 prefixEnd_523282 268695183846126890468477 := by
  unfold tailWord_523282
  simp only [CollatzResearch.WordTrace]
  refine ⟨4771415622561539573911025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12723774993497438863762733 4771415622561539573911025)
  ·
    refine ⟨3578561716921154680433269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4771415622561539573911025 3578561716921154680433269)
    ·
      refine ⟨335490160961358251290619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3578561716921154680433269 335490160961358251290619)
      ·
        refine ⟨503235241442037376935929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 335490160961358251290619 503235241442037376935929)
        ·
          refine ⟨377426431081528032701947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 503235241442037376935929 377426431081528032701947)
          ·
            refine ⟨566139646622292049052921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 377426431081528032701947 566139646622292049052921)
            ·
              refine ⟨424604734966719036789691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 566139646622292049052921 424604734966719036789691)
              ·
                refine ⟨636907102450078555184537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 424604734966719036789691 636907102450078555184537)
                ·
                  refine ⟨477680326837558916388403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 636907102450078555184537 477680326837558916388403)
                  ·
                    refine ⟨716520490256338374582605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 477680326837558916388403 716520490256338374582605)
                    ·
                      refine ⟨268695183846126890468477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 716520490256338374582605 268695183846126890468477)
                      ·
                        rfl

theorem cell23_523282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 2, 1, 2, 1, 3].length) (baseStart_523282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_523282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_523282 prefixEnd_523282 := by exact prefixLift 523282
  have htrace : WordTrace (prefixWord ++ tailWord_523282) baseStart_523282 baseEnd_523282 := by
    simpa [prefixWord, tailWord_523282, baseEnd_523282] using wordTrace_append hprefix tailTrace_523282
  have hstable : (prefixWord ++ tailWord_523282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523282).length < 2 ^ (prefixWord ++ tailWord_523282).sum := by decide
  have hdescent : baseEnd_523282 < baseStart_523282 := by decide
  rcases family_descends (prefixWord ++ tailWord_523282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523333 : List Nat := [1, 3, 1, 1, 1, 3, 2, 3, 8]
def baseStart_523333 : Nat := 118140960795 + 523333 * 2 ^ 59
def prefixEnd_523333 : Nat := 4983230072969 + 3 ^ 40 * 523333 * 2
def baseEnd_523333 : Nat := 29857930151056243436749

theorem tailTrace_523333 : CollatzResearch.WordTrace tailWord_523333 prefixEnd_523333 29857930151056243436749 := by
  unfold tailWord_523333
  simp only [CollatzResearch.WordTrace]
  refine ⟨19087522613061394005750653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12725015075374262670500435 19087522613061394005750653)
  ·
    refine ⟨7157820979898022752156495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19087522613061394005750653 7157820979898022752156495)
    ·
      refine ⟨10736731469847034128234743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7157820979898022752156495 10736731469847034128234743)
      ·
        refine ⟨16105097204770551192352115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10736731469847034128234743 16105097204770551192352115)
        ·
          refine ⟨24157645807155826788528173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16105097204770551192352115 24157645807155826788528173)
          ·
            refine ⟨9059117177683435045698065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24157645807155826788528173 9059117177683435045698065)
            ·
              refine ⟨6794337883262576284273549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9059117177683435045698065 6794337883262576284273549)
              ·
                refine ⟨2547876706223466106602581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6794337883262576284273549 2547876706223466106602581)
                ·
                  refine ⟨29857930151056243436749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2547876706223466106602581 29857930151056243436749)
                  ·
                    rfl

theorem cell23_523333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 3, 8].length) (baseStart_523333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_523333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_523333 prefixEnd_523333 := by exact prefixLift 523333
  have htrace : WordTrace (prefixWord ++ tailWord_523333) baseStart_523333 baseEnd_523333 := by
    simpa [prefixWord, tailWord_523333, baseEnd_523333] using wordTrace_append hprefix tailTrace_523333
  have hstable : (prefixWord ++ tailWord_523333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523333).length < 2 ^ (prefixWord ++ tailWord_523333).sum := by decide
  have hdescent : baseEnd_523333 < baseStart_523333 := by decide
  rcases family_descends (prefixWord ++ tailWord_523333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523353 : List Nat := [1, 2, 1, 2, 2, 1, 2, 1, 3, 2, 6]
def baseStart_523353 : Nat := 118140960795 + 523353 * 2 ^ 59
def prefixEnd_523353 : Nat := 4983230072969 + 3 ^ 40 * 523353 * 2
def baseEnd_523353 : Nat := 268731640972596112680649

theorem tailTrace_523353 : CollatzResearch.WordTrace tailWord_523353 prefixEnd_523353 268731640972596112680649 := by
  unfold tailWord_523353
  simp only [CollatzResearch.WordTrace]
  refine ⟨19088252072988937421478713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12725501381992624947652475 19088252072988937421478713)
  ·
    refine ⟨14316189054741703066109035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19088252072988937421478713 14316189054741703066109035)
    ·
      refine ⟨21474283582112554599163553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14316189054741703066109035 21474283582112554599163553)
      ·
        refine ⟨16105712686584415949372665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21474283582112554599163553 16105712686584415949372665)
        ·
          refine ⟨12079284514938311962029499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16105712686584415949372665 12079284514938311962029499)
          ·
            refine ⟨18118926772407467943044249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12079284514938311962029499 18118926772407467943044249)
            ·
              refine ⟨13589195079305600957283187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18118926772407467943044249 13589195079305600957283187)
              ·
                refine ⟨20383792618958401435924781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13589195079305600957283187 20383792618958401435924781)
                ·
                  refine ⟨7643922232109400538471793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20383792618958401435924781 7643922232109400538471793)
                  ·
                    refine ⟨5732941674082050403853845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7643922232109400538471793 5732941674082050403853845)
                    ·
                      refine ⟨268731640972596112680649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 5732941674082050403853845 268731640972596112680649)
                      ·
                        rfl

theorem cell23_523353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 1, 3, 2, 6].length) (baseStart_523353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_523353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_523353 prefixEnd_523353 := by exact prefixLift 523353
  have htrace : WordTrace (prefixWord ++ tailWord_523353) baseStart_523353 baseEnd_523353 := by
    simpa [prefixWord, tailWord_523353, baseEnd_523353] using wordTrace_append hprefix tailTrace_523353
  have hstable : (prefixWord ++ tailWord_523353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523353).length < 2 ^ (prefixWord ++ tailWord_523353).sum := by decide
  have hdescent : baseEnd_523353 < baseStart_523353 := by decide
  rcases family_descends (prefixWord ++ tailWord_523353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523387 : List Nat := [1, 1, 1, 1, 1, 4, 1, 6, 2, 3, 2]
def baseStart_523387 : Nat := 118140960795 + 523387 * 2 ^ 59
def prefixEnd_523387 : Nat := 4983230072969 + 3 ^ 40 * 523387 * 2
def baseEnd_523387 : Nat := 268749099314848979655493

theorem tailTrace_523387 : CollatzResearch.WordTrace tailWord_523387 prefixEnd_523387 268749099314848979655493 := by
  unfold tailWord_523387
  simp only [CollatzResearch.WordTrace]
  refine ⟨19089492154865761228216415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12726328103243840818810943 19089492154865761228216415)
  ·
    refine ⟨28634238232298641842324623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19089492154865761228216415 28634238232298641842324623)
    ·
      refine ⟨42951357348447962763486935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28634238232298641842324623 42951357348447962763486935)
      ·
        refine ⟨64427036022671944145230403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42951357348447962763486935 64427036022671944145230403)
        ·
          refine ⟨96640554034007916217845605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64427036022671944145230403 96640554034007916217845605)
          ·
            refine ⟨18120103881376484290846051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 96640554034007916217845605 18120103881376484290846051)
            ·
              refine ⟨27180155822064726436269077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18120103881376484290846051 27180155822064726436269077)
              ·
                refine ⟨1274069804159284051700113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 27180155822064726436269077 1274069804159284051700113)
                ·
                  refine ⟨955552353119463038775085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1274069804159284051700113 955552353119463038775085)
                  ·
                    refine ⟨358332132419798639540657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 955552353119463038775085 358332132419798639540657)
                    ·
                      refine ⟨268749099314848979655493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 358332132419798639540657 268749099314848979655493)
                      ·
                        rfl

theorem cell23_523387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 6, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 6, 2, 3, 2].length) (baseStart_523387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_523387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_523387 prefixEnd_523387 := by exact prefixLift 523387
  have htrace : WordTrace (prefixWord ++ tailWord_523387) baseStart_523387 baseEnd_523387 := by
    simpa [prefixWord, tailWord_523387, baseEnd_523387] using wordTrace_append hprefix tailTrace_523387
  have hstable : (prefixWord ++ tailWord_523387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523387).length < 2 ^ (prefixWord ++ tailWord_523387).sum := by decide
  have hdescent : baseEnd_523387 < baseStart_523387 := by decide
  rcases family_descends (prefixWord ++ tailWord_523387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523428 : List Nat := [2, 3, 1, 2, 3, 3, 1, 3, 1, 1, 3]
def baseStart_523428 : Nat := 118140960795 + 523428 * 2 ^ 59
def prefixEnd_523428 : Nat := 4983230072969 + 3 ^ 40 * 523428 * 2
def baseEnd_523428 : Nat := 268770152021683319242805

theorem tailTrace_523428 : CollatzResearch.WordTrace tailWord_523428 prefixEnd_523428 268770152021683319242805 := by
  unfold tailWord_523428
  simp only [CollatzResearch.WordTrace]
  refine ⟨9545493773858612615229469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12727325031811483486972625 9545493773858612615229469)
  ·
    refine ⟨3579560165196979730711051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9545493773858612615229469 3579560165196979730711051)
    ·
      refine ⟨5369340247795469596066577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3579560165196979730711051 5369340247795469596066577)
      ·
        refine ⟨4027005185846602197049933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5369340247795469596066577 4027005185846602197049933)
        ·
          refine ⟨1510126944692475823893725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4027005185846602197049933 1510126944692475823893725)
          ·
            refine ⟨566297604259678433960147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1510126944692475823893725 566297604259678433960147)
            ·
              refine ⟨849446406389517650940221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 566297604259678433960147 849446406389517650940221)
              ·
                refine ⟨318542402396069119102583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 849446406389517650940221 318542402396069119102583)
                ·
                  refine ⟨477813603594103678653875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 318542402396069119102583 477813603594103678653875)
                  ·
                    refine ⟨716720405391155517980813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 477813603594103678653875 716720405391155517980813)
                    ·
                      refine ⟨268770152021683319242805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 716720405391155517980813 268770152021683319242805)
                      ·
                        rfl

theorem cell23_523428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 1, 3, 1, 1, 3].length) (baseStart_523428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_523428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_523428 prefixEnd_523428 := by exact prefixLift 523428
  have htrace : WordTrace (prefixWord ++ tailWord_523428) baseStart_523428 baseEnd_523428 := by
    simpa [prefixWord, tailWord_523428, baseEnd_523428] using wordTrace_append hprefix tailTrace_523428
  have hstable : (prefixWord ++ tailWord_523428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523428).length < 2 ^ (prefixWord ++ tailWord_523428).sum := by decide
  have hdescent : baseEnd_523428 < baseStart_523428 := by decide
  rcases family_descends (prefixWord ++ tailWord_523428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523457 : List Nat := [1, 2, 6, 1, 1, 1, 1, 10]
def baseStart_523457 : Nat := 118140960795 + 523457 * 2 ^ 59
def prefixEnd_523457 : Nat := 4983230072969 + 3 ^ 40 * 523457 * 2
def baseEnd_523457 : Nat := 9955001591135692806673

theorem tailTrace_523457 : CollatzResearch.WordTrace tailWord_523457 prefixEnd_523457 9955001591135692806673 := by
  unfold tailWord_523457
  simp only [CollatzResearch.WordTrace]
  refine ⟨19092045264612163183264625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12728030176408108788843083 19092045264612163183264625)
  ·
    refine ⟨14319033948459122387448469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19092045264612163183264625 14319033948459122387448469)
    ·
      refine ⟨671204716334021361911647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 14319033948459122387448469 671204716334021361911647)
      ·
        refine ⟨1006807074501032042867471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 671204716334021361911647 1006807074501032042867471)
        ·
          refine ⟨1510210611751548064301207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1006807074501032042867471 1510210611751548064301207)
          ·
            refine ⟨2265315917627322096451811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1510210611751548064301207 2265315917627322096451811)
            ·
              refine ⟨3397973876440983144677717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2265315917627322096451811 3397973876440983144677717)
              ·
                refine ⟨9955001591135692806673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 3397973876440983144677717 9955001591135692806673)
                ·
                  rfl

theorem cell23_523457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 10].length) (baseStart_523457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_523457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_523457 prefixEnd_523457 := by exact prefixLift 523457
  have htrace : WordTrace (prefixWord ++ tailWord_523457) baseStart_523457 baseEnd_523457 := by
    simpa [prefixWord, tailWord_523457, baseEnd_523457] using wordTrace_append hprefix tailTrace_523457
  have hstable : (prefixWord ++ tailWord_523457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523457).length < 2 ^ (prefixWord ++ tailWord_523457).sum := by decide
  have hdescent : baseEnd_523457 < baseStart_523457 := by decide
  rcases family_descends (prefixWord ++ tailWord_523457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523467 : List Nat := [1, 1, 1, 1, 3, 2, 2, 2, 6, 1, 3]
def baseStart_523467 : Nat := 118140960795 + 523467 * 2 ^ 59
def prefixEnd_523467 : Nat := 4983230072969 + 3 ^ 40 * 523467 * 2
def baseEnd_523467 : Nat := 268790177767208666655125

theorem tailTrace_523467 : CollatzResearch.WordTrace tailWord_523467 prefixEnd_523467 268790177767208666655125 := by
  unfold tailWord_523467
  simp only [CollatzResearch.WordTrace]
  refine ⟨19092409994575934891128655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12728273329717289927419103 19092409994575934891128655)
  ·
    refine ⟨28638614991863902336692983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19092409994575934891128655 28638614991863902336692983)
    ·
      refine ⟨42957922487795853505039475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28638614991863902336692983 42957922487795853505039475)
      ·
        refine ⟨64436883731693780257559213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42957922487795853505039475 64436883731693780257559213)
        ·
          refine ⟨24163831399385167596584705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64436883731693780257559213 24163831399385167596584705)
          ·
            refine ⟨18122873549538875697438529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24163831399385167596584705 18122873549538875697438529)
            ·
              refine ⟨13592155162154156773078897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18122873549538875697438529 13592155162154156773078897)
              ·
                refine ⟨10194116371615617579809173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13592155162154156773078897 10194116371615617579809173)
                ·
                  refine ⟨477849204919482074053555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10194116371615617579809173 477849204919482074053555)
                  ·
                    refine ⟨716773807379223111080333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 477849204919482074053555 716773807379223111080333)
                    ·
                      refine ⟨268790177767208666655125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 716773807379223111080333 268790177767208666655125)
                      ·
                        rfl

theorem cell23_523467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 2, 6, 1, 3].length) (baseStart_523467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_523467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_523467 prefixEnd_523467 := by exact prefixLift 523467
  have htrace : WordTrace (prefixWord ++ tailWord_523467) baseStart_523467 baseEnd_523467 := by
    simpa [prefixWord, tailWord_523467, baseEnd_523467] using wordTrace_append hprefix tailTrace_523467
  have hstable : (prefixWord ++ tailWord_523467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523467).length < 2 ^ (prefixWord ++ tailWord_523467).sum := by decide
  have hdescent : baseEnd_523467 < baseStart_523467 := by decide
  rcases family_descends (prefixWord ++ tailWord_523467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523501 : List Nat := [1, 5, 1, 2, 2, 1, 1, 4, 2, 1, 3]
def baseStart_523501 : Nat := 118140960795 + 523501 * 2 ^ 59
def prefixEnd_523501 : Nat := 4983230072969 + 3 ^ 40 * 523501 * 2
def baseEnd_523501 : Nat := 268807636109461533629969

theorem tailTrace_523501 : CollatzResearch.WordTrace tailWord_523501 prefixEnd_523501 268807636109461533629969 := by
  unfold tailWord_523501
  simp only [CollatzResearch.WordTrace]
  refine ⟨19093650076452758697866357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12729100050968505798577571 19093650076452758697866357)
  ·
    refine ⟨1790029694667446127924971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 19093650076452758697866357 1790029694667446127924971)
    ·
      refine ⟨2685044542001169191887457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1790029694667446127924971 2685044542001169191887457)
      ·
        refine ⟨2013783406500876893915593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2685044542001169191887457 2013783406500876893915593)
        ·
          refine ⟨1510337554875657670436695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2013783406500876893915593 1510337554875657670436695)
          ·
            refine ⟨2265506332313486505655043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1510337554875657670436695 2265506332313486505655043)
            ·
              refine ⟨3398259498470229758482565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2265506332313486505655043 3398259498470229758482565)
              ·
                refine ⟨637173655963168079715481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3398259498470229758482565 637173655963168079715481)
                ·
                  refine ⟨477880241972376059786611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 637173655963168079715481 477880241972376059786611)
                  ·
                    refine ⟨716820362958564089679917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 477880241972376059786611 716820362958564089679917)
                    ·
                      refine ⟨268807636109461533629969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 716820362958564089679917 268807636109461533629969)
                      ·
                        rfl

theorem cell23_523501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 4, 2, 1, 3].length) (baseStart_523501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_523501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_523501 prefixEnd_523501 := by exact prefixLift 523501
  have htrace : WordTrace (prefixWord ++ tailWord_523501) baseStart_523501 baseEnd_523501 := by
    simpa [prefixWord, tailWord_523501, baseEnd_523501] using wordTrace_append hprefix tailTrace_523501
  have hstable : (prefixWord ++ tailWord_523501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523501).length < 2 ^ (prefixWord ++ tailWord_523501).sum := by decide
  have hdescent : baseEnd_523501 < baseStart_523501 := by decide
  rcases family_descends (prefixWord ++ tailWord_523501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523508 : List Nat := [2, 6, 1, 2, 1, 2, 1, 8]
def baseStart_523508 : Nat := 118140960795 + 523508 * 2 ^ 59
def prefixEnd_523508 : Nat := 4983230072969 + 3 ^ 40 * 523508 * 2
def baseEnd_523508 : Nat := 9955971499038629860831

theorem tailTrace_523508 : CollatzResearch.WordTrace tailWord_523508 prefixEnd_523508 9955971499038629860831 := by
  unfold tailWord_523508
  simp only [CollatzResearch.WordTrace]
  refine ⟨9546952693713699446685589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12729270258284932595580785 9546952693713699446685589)
  ·
    refine ⟨447513407517829661563387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 9546952693713699446685589 447513407517829661563387)
    ·
      refine ⟨671270111276744492345081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 447513407517829661563387 671270111276744492345081)
      ·
        refine ⟨503452583457558369258811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 671270111276744492345081 503452583457558369258811)
        ·
          refine ⟨755178875186337553888217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 503452583457558369258811 755178875186337553888217)
          ·
            refine ⟨566384156389753165416163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 755178875186337553888217 566384156389753165416163)
            ·
              refine ⟨849576234584629748124245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 566384156389753165416163 849576234584629748124245)
              ·
                refine ⟨9955971499038629860831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 849576234584629748124245 9955971499038629860831)
                ·
                  rfl

theorem cell23_523508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 1, 8].length) (baseStart_523508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_523508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_523508 prefixEnd_523508 := by exact prefixLift 523508
  have htrace : WordTrace (prefixWord ++ tailWord_523508) baseStart_523508 baseEnd_523508 := by
    simpa [prefixWord, tailWord_523508, baseEnd_523508] using wordTrace_append hprefix tailTrace_523508
  have hstable : (prefixWord ++ tailWord_523508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523508).length < 2 ^ (prefixWord ++ tailWord_523508).sum := by decide
  have hdescent : baseEnd_523508 < baseStart_523508 := by decide
  rcases family_descends (prefixWord ++ tailWord_523508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523634 : List Nat := [3, 2, 1, 2, 1, 2, 1, 2, 4, 2, 3]
def baseStart_523634 : Nat := 118140960795 + 523634 * 2 ^ 59
def prefixEnd_523634 : Nat := 4983230072969 + 3 ^ 40 * 523634 * 2
def baseEnd_523634 : Nat := 268875929036509513266857

theorem tailTrace_523634 : CollatzResearch.WordTrace tailWord_523634 prefixEnd_523634 268875929036509513266857 := by
  unfold tailWord_523634
  simp only [CollatzResearch.WordTrace]
  refine ⟨4774625246242730603114489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12732333989980614941638637 4774625246242730603114489)
  ·
    refine ⟨3580968934682047952335867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4774625246242730603114489 3580968934682047952335867)
    ·
      refine ⟨5371453402023071928503801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3580968934682047952335867 5371453402023071928503801)
      ·
        refine ⟨4028590051517303946377851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5371453402023071928503801 4028590051517303946377851)
        ·
          refine ⟨6042885077275955919566777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4028590051517303946377851 6042885077275955919566777)
          ·
            refine ⟨4532163807956966939675083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6042885077275955919566777 4532163807956966939675083)
            ·
              refine ⟨6798245711935450409512625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4532163807956966939675083 6798245711935450409512625)
              ·
                refine ⟨5098684283951587807134469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6798245711935450409512625 5098684283951587807134469)
                ·
                  refine ⟨956003303240922713837713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5098684283951587807134469 956003303240922713837713)
                  ·
                    refine ⟨717002477430692035378285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 956003303240922713837713 717002477430692035378285)
                    ·
                      refine ⟨268875929036509513266857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 717002477430692035378285 268875929036509513266857)
                      ·
                        rfl

theorem cell23_523634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 2, 4, 2, 3].length) (baseStart_523634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_523634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_523634 prefixEnd_523634 := by exact prefixLift 523634
  have htrace : WordTrace (prefixWord ++ tailWord_523634) baseStart_523634 baseEnd_523634 := by
    simpa [prefixWord, tailWord_523634, baseEnd_523634] using wordTrace_append hprefix tailTrace_523634
  have hstable : (prefixWord ++ tailWord_523634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523634).length < 2 ^ (prefixWord ++ tailWord_523634).sum := by decide
  have hdescent : baseEnd_523634 < baseStart_523634 := by decide
  rcases family_descends (prefixWord ++ tailWord_523634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523651 : List Nat := [1, 1, 1, 3, 5, 2, 2, 1, 2, 2, 3]
def baseStart_523651 : Nat := 118140960795 + 523651 * 2 ^ 59
def prefixEnd_523651 : Nat := 4983230072969 + 3 ^ 40 * 523651 * 2
def baseEnd_523651 : Nat := 268884658207635946754279

theorem tailTrace_523651 : CollatzResearch.WordTrace tailWord_523651 prefixEnd_523651 268884658207635946754279 := by
  unfold tailWord_523651
  simp only [CollatzResearch.WordTrace]
  refine ⟨19099121025909334315826807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12732747350606222877217871 19099121025909334315826807)
  ·
    refine ⟨28648681538864001473740211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19099121025909334315826807 28648681538864001473740211)
    ·
      refine ⟨42973022308296002210610317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28648681538864001473740211 42973022308296002210610317)
      ·
        refine ⟨16114883365611000828978869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42973022308296002210610317 16114883365611000828978869)
        ·
          refine ⟨1510770315526031327716769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16114883365611000828978869 1510770315526031327716769)
          ·
            refine ⟨1133077736644523495787577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1510770315526031327716769 1133077736644523495787577)
            ·
              refine ⟨849808302483392621840683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1133077736644523495787577 849808302483392621840683)
              ·
                refine ⟨1274712453725088932761025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 849808302483392621840683 1274712453725088932761025)
                ·
                  refine ⟨956034340293816699570769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1274712453725088932761025 956034340293816699570769)
                  ·
                    refine ⟨717025755220362524678077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 956034340293816699570769 717025755220362524678077)
                    ·
                      refine ⟨268884658207635946754279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 717025755220362524678077 268884658207635946754279)
                      ·
                        rfl

theorem cell23_523651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 2, 1, 2, 2, 3].length) (baseStart_523651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_523651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_523651 prefixEnd_523651 := by exact prefixLift 523651
  have htrace : WordTrace (prefixWord ++ tailWord_523651) baseStart_523651 baseEnd_523651 := by
    simpa [prefixWord, tailWord_523651, baseEnd_523651] using wordTrace_append hprefix tailTrace_523651
  have hstable : (prefixWord ++ tailWord_523651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523651).length < 2 ^ (prefixWord ++ tailWord_523651).sum := by decide
  have hdescent : baseEnd_523651 < baseStart_523651 := by decide
  rcases family_descends (prefixWord ++ tailWord_523651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523704 : List Nat := [2, 1, 2, 1, 2, 2, 4, 1, 3, 1, 4]
def baseStart_523704 : Nat := 118140960795 + 523704 * 2 ^ 59
def prefixEnd_523704 : Nat := 4983230072969 + 3 ^ 40 * 523704 * 2
def baseEnd_523704 : Nat := 268911872682324239391535

theorem tailTrace_523704 : CollatzResearch.WordTrace tailWord_523704 prefixEnd_523704 268911872682324239391535 := by
  unfold tailWord_523704
  simp only [CollatzResearch.WordTrace]
  refine ⟨9550527047358662183753083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12734036063144882911670777 9550527047358662183753083)
  ·
    refine ⟨14325790571037993275629625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9550527047358662183753083 14325790571037993275629625)
    ·
      refine ⟨10744342928278494956722219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14325790571037993275629625 10744342928278494956722219)
      ·
        refine ⟨16116514392417742435083329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10744342928278494956722219 16116514392417742435083329)
        ·
          refine ⟨12087385794313306826312497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16116514392417742435083329 12087385794313306826312497)
          ·
            refine ⟨9065539345734980119734373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12087385794313306826312497 9065539345734980119734373)
            ·
              refine ⟨1699788627325308772450195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9065539345734980119734373 1699788627325308772450195)
              ·
                refine ⟨2549682940987963158675293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1699788627325308772450195 2549682940987963158675293)
                ·
                  refine ⟨956131102870486184503235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2549682940987963158675293 956131102870486184503235)
                  ·
                    refine ⟨1434196654305729276754853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 956131102870486184503235 1434196654305729276754853)
                    ·
                      refine ⟨268911872682324239391535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1434196654305729276754853 268911872682324239391535)
                      ·
                        rfl

theorem cell23_523704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4, 1, 3, 1, 4].length) (baseStart_523704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_523704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_523704 prefixEnd_523704 := by exact prefixLift 523704
  have htrace : WordTrace (prefixWord ++ tailWord_523704) baseStart_523704 baseEnd_523704 := by
    simpa [prefixWord, tailWord_523704, baseEnd_523704] using wordTrace_append hprefix tailTrace_523704
  have hstable : (prefixWord ++ tailWord_523704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523704).length < 2 ^ (prefixWord ++ tailWord_523704).sum := by decide
  have hdescent : baseEnd_523704 < baseStart_523704 := by decide
  rcases family_descends (prefixWord ++ tailWord_523704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523708 : List Nat := [2, 2, 2, 4, 2, 1, 1, 1, 1, 5, 2]
def baseStart_523708 : Nat := 118140960795 + 523708 * 2 ^ 59
def prefixEnd_523708 : Nat := 4983230072969 + 3 ^ 40 * 523708 * 2
def baseEnd_523708 : Nat := 268913926604942223741517

theorem tailTrace_523708 : CollatzResearch.WordTrace tailWord_523708 prefixEnd_523708 268913926604942223741517 := by
  unfold tailWord_523708
  simp only [CollatzResearch.WordTrace]
  refine ⟨9550599993351416525325889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12734133324468555367101185 9550599993351416525325889)
  ·
    refine ⟨7162949995013562393994417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9550599993351416525325889 7162949995013562393994417)
    ·
      refine ⟨5372212496260171795495813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7162949995013562393994417 5372212496260171795495813)
      ·
        refine ⟨1007289843048782211655465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5372212496260171795495813 1007289843048782211655465)
        ·
          refine ⟨755467382286586658741599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1007289843048782211655465 755467382286586658741599)
          ·
            refine ⟨1133201073429879988112399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 755467382286586658741599 1133201073429879988112399)
            ·
              refine ⟨1699801610144819982168599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1133201073429879988112399 1699801610144819982168599)
              ·
                refine ⟨2549702415217229973252899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1699801610144819982168599 2549702415217229973252899)
                ·
                  refine ⟨3824553622825844959879349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2549702415217229973252899 3824553622825844959879349)
                  ·
                    refine ⟨358551902139922964988689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3824553622825844959879349 358551902139922964988689)
                    ·
                      refine ⟨268913926604942223741517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 358551902139922964988689 268913926604942223741517)
                      ·
                        rfl

theorem cell23_523708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 1, 1, 1, 5, 2].length) (baseStart_523708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_523708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_523708 prefixEnd_523708 := by exact prefixLift 523708
  have htrace : WordTrace (prefixWord ++ tailWord_523708) baseStart_523708 baseEnd_523708 := by
    simpa [prefixWord, tailWord_523708, baseEnd_523708] using wordTrace_append hprefix tailTrace_523708
  have hstable : (prefixWord ++ tailWord_523708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523708).length < 2 ^ (prefixWord ++ tailWord_523708).sum := by decide
  have hdescent : baseEnd_523708 < baseStart_523708 := by decide
  rcases family_descends (prefixWord ++ tailWord_523708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523721 : List Nat := [1, 2, 1, 1, 2, 1, 3, 1, 7, 2, 2]
def baseStart_523721 : Nat := 118140960795 + 523721 * 2 ^ 59
def prefixEnd_523721 : Nat := 4983230072969 + 3 ^ 40 * 523721 * 2
def baseEnd_523721 : Nat := 268920601853450672878957

theorem tailTrace_523721 : CollatzResearch.WordTrace tailWord_523721 prefixEnd_523721 268920601853450672878957 := by
  unfold tailWord_523721
  simp only [CollatzResearch.WordTrace]
  refine ⟨19101674135655736270875017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12734449423770490847250011 19101674135655736270875017)
  ·
    refine ⟨14326255601741802203156263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19101674135655736270875017 14326255601741802203156263)
    ·
      refine ⟨21489383402612703304734395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14326255601741802203156263 21489383402612703304734395)
      ·
        refine ⟨32234075103919054957101593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21489383402612703304734395 32234075103919054957101593)
        ·
          refine ⟨24175556327939291217826195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32234075103919054957101593 24175556327939291217826195)
          ·
            refine ⟨36263334491908936826739293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24175556327939291217826195 36263334491908936826739293)
            ·
              refine ⟨13598750434465851310027235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36263334491908936826739293 13598750434465851310027235)
              ·
                refine ⟨20398125651698776965040853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13598750434465851310027235 20398125651698776965040853)
                ·
                  refine ⟨478081069961690085118145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20398125651698776965040853 478081069961690085118145)
                  ·
                    refine ⟨358560802471267563838609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 478081069961690085118145 358560802471267563838609)
                    ·
                      refine ⟨268920601853450672878957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 358560802471267563838609 268920601853450672878957)
                      ·
                        rfl

theorem cell23_523721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 1, 7, 2, 2].length) (baseStart_523721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_523721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_523721 prefixEnd_523721 := by exact prefixLift 523721
  have htrace : WordTrace (prefixWord ++ tailWord_523721) baseStart_523721 baseEnd_523721 := by
    simpa [prefixWord, tailWord_523721, baseEnd_523721] using wordTrace_append hprefix tailTrace_523721
  have hstable : (prefixWord ++ tailWord_523721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523721).length < 2 ^ (prefixWord ++ tailWord_523721).sum := by decide
  have hdescent : baseEnd_523721 < baseStart_523721 := by decide
  rcases family_descends (prefixWord ++ tailWord_523721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523738 : List Nat := [3, 1, 1, 2, 3, 2, 1, 3, 3, 2, 2]
def baseStart_523738 : Nat := 118140960795 + 523738 * 2 ^ 59
def prefixEnd_523738 : Nat := 4983230072969 + 3 ^ 40 * 523738 * 2
def baseEnd_523738 : Nat := 268929331024577106366379

theorem tailTrace_523738 : CollatzResearch.WordTrace tailWord_523738 prefixEnd_523738 268929331024577106366379 := by
  unfold tailWord_523738
  simp only [CollatzResearch.WordTrace]
  refine ⟨4775573544148537043560967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12734862784396098782829245 4775573544148537043560967)
  ·
    refine ⟨7163360316222805565341451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4775573544148537043560967 7163360316222805565341451)
    ·
      refine ⟨10745040474334208348012177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7163360316222805565341451 10745040474334208348012177)
      ·
        refine ⟨8058780355750656261009133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10745040474334208348012177 8058780355750656261009133)
        ·
          refine ⟨3022042633406496097878425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8058780355750656261009133 3022042633406496097878425)
          ·
            refine ⟨2266531975054872073408819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3022042633406496097878425 2266531975054872073408819)
            ·
              refine ⟨3399797962582308110113229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2266531975054872073408819 3399797962582308110113229)
              ·
                refine ⟨1274924235968365541292461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3399797962582308110113229 1274924235968365541292461)
                ·
                  refine ⟨478096588488137077984673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1274924235968365541292461 478096588488137077984673)
                  ·
                    refine ⟨358572441366102808488505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 478096588488137077984673 358572441366102808488505)
                    ·
                      refine ⟨268929331024577106366379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 358572441366102808488505 268929331024577106366379)
                      ·
                        rfl

theorem cell23_523738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 3, 3, 2, 2].length) (baseStart_523738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_523738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_523738 prefixEnd_523738 := by exact prefixLift 523738
  have htrace : WordTrace (prefixWord ++ tailWord_523738) baseStart_523738 baseEnd_523738 := by
    simpa [prefixWord, tailWord_523738, baseEnd_523738] using wordTrace_append hprefix tailTrace_523738
  have hstable : (prefixWord ++ tailWord_523738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523738).length < 2 ^ (prefixWord ++ tailWord_523738).sum := by decide
  have hdescent : baseEnd_523738 < baseStart_523738 := by decide
  rcases family_descends (prefixWord ++ tailWord_523738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523741 : List Nat := [1, 4, 3, 1, 1, 3, 1, 2, 1, 1, 5]
def baseStart_523741 : Nat := 118140960795 + 523741 * 2 ^ 59
def prefixEnd_523741 : Nat := 4983230072969 + 3 ^ 40 * 523741 * 2
def baseEnd_523741 : Nat := 268930871466540594628865

theorem tailTrace_523741 : CollatzResearch.WordTrace tailWord_523741 prefixEnd_523741 268930871466540594628865 := by
  unfold tailWord_523741
  simp only [CollatzResearch.WordTrace]
  refine ⟨19102403595583279686603077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12734935730388853124402051 19102403595583279686603077)
  ·
    refine ⟨3581700674171864941238077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19102403595583279686603077 3581700674171864941238077)
    ·
      refine ⟨1343137752814449352964279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3581700674171864941238077 1343137752814449352964279)
      ·
        refine ⟨2014706629221674029446419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1343137752814449352964279 2014706629221674029446419)
        ·
          refine ⟨3022059943832511044169629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2014706629221674029446419 3022059943832511044169629)
          ·
            refine ⟨1133272478937191641563611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3022059943832511044169629 1133272478937191641563611)
            ·
              refine ⟨1699908718405787462345417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1133272478937191641563611 1699908718405787462345417)
              ·
                refine ⟨1274931538804340596759063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1699908718405787462345417 1274931538804340596759063)
                ·
                  refine ⟨1912397308206510895138595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1274931538804340596759063 1912397308206510895138595)
                  ·
                    refine ⟨2868595962309766342707893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1912397308206510895138595 2868595962309766342707893)
                    ·
                      refine ⟨268930871466540594628865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2868595962309766342707893 268930871466540594628865)
                      ·
                        rfl

theorem cell23_523741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 1, 2, 1, 1, 5].length) (baseStart_523741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_523741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_523741 prefixEnd_523741 := by exact prefixLift 523741
  have htrace : WordTrace (prefixWord ++ tailWord_523741) baseStart_523741 baseEnd_523741 := by
    simpa [prefixWord, tailWord_523741, baseEnd_523741] using wordTrace_append hprefix tailTrace_523741
  have hstable : (prefixWord ++ tailWord_523741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523741).length < 2 ^ (prefixWord ++ tailWord_523741).sum := by decide
  have hdescent : baseEnd_523741 < baseStart_523741 := by decide
  rcases family_descends (prefixWord ++ tailWord_523741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523751 : List Nat := [1, 1, 5, 2, 1, 2, 3, 1, 1, 2, 4]
def baseStart_523751 : Nat := 118140960795 + 523751 * 2 ^ 59
def prefixEnd_523751 : Nat := 4983230072969 + 3 ^ 40 * 523751 * 2
def baseEnd_523751 : Nat := 268936006273085555503819

theorem tailTrace_523751 : CollatzResearch.WordTrace tailWord_523751 prefixEnd_523751 268936006273085555503819 := by
  unfold tailWord_523751
  simp only [CollatzResearch.WordTrace]
  refine ⟨19102768325547051394467107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12735178883698034262978071 19102768325547051394467107)
  ·
    refine ⟨28654152488320577091700661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19102768325547051394467107 28654152488320577091700661)
    ·
      refine ⟨2686326795780054102346937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 28654152488320577091700661 2686326795780054102346937)
      ·
        refine ⟨2014745096835040576760203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2686326795780054102346937 2014745096835040576760203)
        ·
          refine ⟨3022117645252560865140305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2014745096835040576760203 3022117645252560865140305)
          ·
            refine ⟨2266588233939420648855229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3022117645252560865140305 2266588233939420648855229)
            ·
              refine ⟨849970587727282743320711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2266588233939420648855229 849970587727282743320711)
              ·
                refine ⟨1274955881590924114981067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 849970587727282743320711 1274955881590924114981067)
                ·
                  refine ⟨1912433822386386172471601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1274955881590924114981067 1912433822386386172471601)
                  ·
                    refine ⟨1434325366789789629353701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1912433822386386172471601 1434325366789789629353701)
                    ·
                      refine ⟨268936006273085555503819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1434325366789789629353701 268936006273085555503819)
                      ·
                        rfl

theorem cell23_523751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 3, 1, 1, 2, 4].length) (baseStart_523751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_523751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_523751 prefixEnd_523751 := by exact prefixLift 523751
  have htrace : WordTrace (prefixWord ++ tailWord_523751) baseStart_523751 baseEnd_523751 := by
    simpa [prefixWord, tailWord_523751, baseEnd_523751] using wordTrace_append hprefix tailTrace_523751
  have hstable : (prefixWord ++ tailWord_523751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523751).length < 2 ^ (prefixWord ++ tailWord_523751).sum := by decide
  have hdescent : baseEnd_523751 < baseStart_523751 := by decide
  rcases family_descends (prefixWord ++ tailWord_523751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523758 : List Nat := [4, 1, 2, 1, 2, 1, 4, 2, 1, 2, 3]
def baseStart_523758 : Nat := 118140960795 + 523758 * 2 ^ 59
def prefixEnd_523758 : Nat := 4983230072969 + 3 ^ 40 * 523758 * 2
def baseEnd_523758 : Nat := 268939600637667028116287

theorem tailTrace_523758 : CollatzResearch.WordTrace tailWord_523758 prefixEnd_523758 268939600637667028116287 := by
  unfold tailWord_523758
  simp only [CollatzResearch.WordTrace]
  refine ⟨2387877954565211448746491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12735349091014461059981285 2387877954565211448746491)
  ·
    refine ⟨3581816931847817173119737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2387877954565211448746491 3581816931847817173119737)
    ·
      refine ⟨2686362698885862879839803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3581816931847817173119737 2686362698885862879839803)
      ·
        refine ⟨4029544048328794319759705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2686362698885862879839803 4029544048328794319759705)
        ·
          refine ⟨3022158036246595739819779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4029544048328794319759705 3022158036246595739819779)
          ·
            refine ⟨4533237054369893609729669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3022158036246595739819779 4533237054369893609729669)
            ·
              refine ⟨849981947694355051824313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4533237054369893609729669 849981947694355051824313)
              ·
                refine ⟨637486460770766288868235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 849981947694355051824313 637486460770766288868235)
                ·
                  refine ⟨956229691156149433302353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 637486460770766288868235 956229691156149433302353)
                  ·
                    refine ⟨717172268367112074976765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 956229691156149433302353 717172268367112074976765)
                    ·
                      refine ⟨268939600637667028116287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 717172268367112074976765 268939600637667028116287)
                      ·
                        rfl

theorem cell23_523758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 4, 2, 1, 2, 3].length) (baseStart_523758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_523758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_523758 prefixEnd_523758 := by exact prefixLift 523758
  have htrace : WordTrace (prefixWord ++ tailWord_523758) baseStart_523758 baseEnd_523758 := by
    simpa [prefixWord, tailWord_523758, baseEnd_523758] using wordTrace_append hprefix tailTrace_523758
  have hstable : (prefixWord ++ tailWord_523758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523758).length < 2 ^ (prefixWord ++ tailWord_523758).sum := by decide
  have hdescent : baseEnd_523758 < baseStart_523758 := by decide
  rcases family_descends (prefixWord ++ tailWord_523758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523761 : List Nat := [1, 2, 2, 2, 3, 4, 2, 7]
def baseStart_523761 : Nat := 118140960795 + 523761 * 2 ^ 59
def prefixEnd_523761 : Nat := 4983230072969 + 3 ^ 40 * 523761 * 2
def baseEnd_523761 : Nat := 9960783002949278384399

theorem tailTrace_523761 : CollatzResearch.WordTrace tailWord_523761 prefixEnd_523761 9960783002949278384399 := by
  unfold tailWord_523761
  simp only [CollatzResearch.WordTrace]
  refine ⟨19103133055510823102331137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12735422037007215401554091 19103133055510823102331137)
  ·
    refine ⟨14327349791633117326748353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19103133055510823102331137 14327349791633117326748353)
    ·
      refine ⟨10745512343724837995061265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14327349791633117326748353 10745512343724837995061265)
      ·
        refine ⟨8059134257793628496295949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10745512343724837995061265 8059134257793628496295949)
        ·
          refine ⟨3022175346672610686110981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8059134257793628496295949 3022175346672610686110981)
          ·
            refine ⟨566657877501114503645809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3022175346672610686110981 566657877501114503645809)
            ·
              refine ⟨424993408125835877734357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 566657877501114503645809 424993408125835877734357)
              ·
                refine ⟨9960783002949278384399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 424993408125835877734357 9960783002949278384399)
                ·
                  rfl

theorem cell23_523761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 2, 7].length) (baseStart_523761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_523761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_523761 prefixEnd_523761 := by exact prefixLift 523761
  have htrace : WordTrace (prefixWord ++ tailWord_523761) baseStart_523761 baseEnd_523761 := by
    simpa [prefixWord, tailWord_523761, baseEnd_523761] using wordTrace_append hprefix tailTrace_523761
  have hstable : (prefixWord ++ tailWord_523761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523761).length < 2 ^ (prefixWord ++ tailWord_523761).sum := by decide
  have hdescent : baseEnd_523761 < baseStart_523761 := by decide
  rcases family_descends (prefixWord ++ tailWord_523761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523781 : List Nat := [1, 3, 1, 1, 2, 2, 1, 2, 5, 3, 2]
def baseStart_523781 : Nat := 118140960795 + 523781 * 2 ^ 59
def prefixEnd_523781 : Nat := 4983230072969 + 3 ^ 40 * 523781 * 2
def baseEnd_523781 : Nat := 268951410692720438128681

theorem tailTrace_523781 : CollatzResearch.WordTrace tailWord_523781 prefixEnd_523781 268951410692720438128681 := by
  unfold tailWord_523781
  simp only [CollatzResearch.WordTrace]
  refine ⟨19103862515438366518059197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12735908343625577678706131 19103862515438366518059197)
  ·
    refine ⟨7163948443289387444272199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19103862515438366518059197 7163948443289387444272199)
    ·
      refine ⟨10745922664934081166408299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7163948443289387444272199 10745922664934081166408299)
      ·
        refine ⟨16118883997401121749612449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10745922664934081166408299 16118883997401121749612449)
        ·
          refine ⟨12089162998050841312209337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16118883997401121749612449 12089162998050841312209337)
          ·
            refine ⟨9066872248538130984157003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12089162998050841312209337 9066872248538130984157003)
            ·
              refine ⟨13600308372807196476235505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9066872248538130984157003 13600308372807196476235505)
              ·
                refine ⟨10200231279605397357176629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13600308372807196476235505 10200231279605397357176629)
                ·
                  refine ⟨956271682463006002235309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10200231279605397357176629 956271682463006002235309)
                  ·
                    refine ⟨358601880923627250838241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 956271682463006002235309 358601880923627250838241)
                    ·
                      refine ⟨268951410692720438128681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 358601880923627250838241 268951410692720438128681)
                      ·
                        rfl

theorem cell23_523781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 2, 5, 3, 2].length) (baseStart_523781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_523781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_523781 prefixEnd_523781 := by exact prefixLift 523781
  have htrace : WordTrace (prefixWord ++ tailWord_523781) baseStart_523781 baseEnd_523781 := by
    simpa [prefixWord, tailWord_523781, baseEnd_523781] using wordTrace_append hprefix tailTrace_523781
  have hstable : (prefixWord ++ tailWord_523781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523781).length < 2 ^ (prefixWord ++ tailWord_523781).sum := by decide
  have hdescent : baseEnd_523781 < baseStart_523781 := by decide
  rcases family_descends (prefixWord ++ tailWord_523781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523804 : List Nat := [2, 2, 3, 1, 2, 1, 2, 1, 1, 8]
def baseStart_523804 : Nat := 118140960795 + 523804 * 2 ^ 59
def prefixEnd_523804 : Nat := 4983230072969 + 3 ^ 40 * 523804 * 2
def baseEnd_523804 : Nat := 89654406915924616047025

theorem tailTrace_523804 : CollatzResearch.WordTrace tailWord_523804 prefixEnd_523804 89654406915924616047025 := by
  unfold tailWord_523804
  simp only [CollatzResearch.WordTrace]
  refine ⟨9552350697177520723073233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12736467596236694297430977 9552350697177520723073233)
  ·
    refine ⟨7164263022883140542304925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9552350697177520723073233 7164263022883140542304925)
    ·
      refine ⟨2686598633581177703364347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7164263022883140542304925 2686598633581177703364347)
      ·
        refine ⟨4029897950371766555046521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2686598633581177703364347 4029897950371766555046521)
        ·
          refine ⟨3022423462778824916284891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4029897950371766555046521 3022423462778824916284891)
          ·
            refine ⟨4533635194168237374427337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3022423462778824916284891 4533635194168237374427337)
            ·
              refine ⟨3400226395626178030820503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4533635194168237374427337 3400226395626178030820503)
              ·
                refine ⟨5100339593439267046230755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3400226395626178030820503 5100339593439267046230755)
                ·
                  refine ⟨7650509390158900569346133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5100339593439267046230755 7650509390158900569346133)
                  ·
                    refine ⟨89654406915924616047025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 7650509390158900569346133 89654406915924616047025)
                    ·
                      rfl

theorem cell23_523804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 1, 1, 8].length) (baseStart_523804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_523804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_523804 prefixEnd_523804 := by exact prefixLift 523804
  have htrace : WordTrace (prefixWord ++ tailWord_523804) baseStart_523804 baseEnd_523804 := by
    simpa [prefixWord, tailWord_523804, baseEnd_523804] using wordTrace_append hprefix tailTrace_523804
  have hstable : (prefixWord ++ tailWord_523804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523804).length < 2 ^ (prefixWord ++ tailWord_523804).sum := by decide
  have hdescent : baseEnd_523804 < baseStart_523804 := by decide
  rcases family_descends (prefixWord ++ tailWord_523804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523806 : List Nat := [4, 3, 3, 1, 2, 1, 1, 2, 1, 1, 4]
def baseStart_523806 : Nat := 118140960795 + 523806 * 2 ^ 59
def prefixEnd_523806 : Nat := 4983230072969 + 3 ^ 40 * 523806 * 2
def baseEnd_523806 : Nat := 268964247709082840316067

theorem tailTrace_523806 : CollatzResearch.WordTrace tailWord_523806 prefixEnd_523806 268964247709082840316067 := by
  unfold tailWord_523806
  simp only [CollatzResearch.WordTrace]
  refine ⟨2388096792543474473464909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12736516226898530525146181 2388096792543474473464909)
  ·
    refine ⟨895536297203802927549341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2388096792543474473464909 895536297203802927549341)
    ·
      refine ⟨335826111451426097831003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 895536297203802927549341 335826111451426097831003)
      ·
        refine ⟨503739167177139146746505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 335826111451426097831003 503739167177139146746505)
        ·
          refine ⟨377804375382854360059879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 503739167177139146746505 377804375382854360059879)
          ·
            refine ⟨566706563074281540089819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 377804375382854360059879 566706563074281540089819)
            ·
              refine ⟨850059844611422310134729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 566706563074281540089819 850059844611422310134729)
              ·
                refine ⟨637544883458566732601047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 850059844611422310134729 637544883458566732601047)
                ·
                  refine ⟨956317325187850098901571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 637544883458566732601047 956317325187850098901571)
                  ·
                    refine ⟨1434475987781775148352357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 956317325187850098901571 1434475987781775148352357)
                    ·
                      refine ⟨268964247709082840316067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1434475987781775148352357 268964247709082840316067)
                      ·
                        rfl

theorem cell23_523806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 1, 2, 1, 1, 4].length) (baseStart_523806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_523806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_523806 prefixEnd_523806 := by exact prefixLift 523806
  have htrace : WordTrace (prefixWord ++ tailWord_523806) baseStart_523806 baseEnd_523806 := by
    simpa [prefixWord, tailWord_523806, baseEnd_523806] using wordTrace_append hprefix tailTrace_523806
  have hstable : (prefixWord ++ tailWord_523806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523806).length < 2 ^ (prefixWord ++ tailWord_523806).sum := by decide
  have hdescent : baseEnd_523806 < baseStart_523806 := by decide
  rcases family_descends (prefixWord ++ tailWord_523806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523824 : List Nat := [2, 1, 1, 1, 2, 3, 1, 2, 4, 2, 4]
def baseStart_523824 : Nat := 118140960795 + 523824 * 2 ^ 59
def prefixEnd_523824 : Nat := 4983230072969 + 3 ^ 40 * 523824 * 2
def baseEnd_523824 : Nat := 268973490360863769890983

theorem tailTrace_523824 : CollatzResearch.WordTrace tailWord_523824 prefixEnd_523824 268973490360863769890983 := by
  unfold tailWord_523824
  simp only [CollatzResearch.WordTrace]
  refine ⟨9552715427141292430937263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12736953902855056574583017 9552715427141292430937263)
  ·
    refine ⟨14329073140711938646405895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9552715427141292430937263 14329073140711938646405895)
    ·
      refine ⟨21493609711067907969608843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14329073140711938646405895 21493609711067907969608843)
      ·
        refine ⟨32240414566601861954413265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21493609711067907969608843 32240414566601861954413265)
        ·
          refine ⟨24180310924951396465809949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32240414566601861954413265 24180310924951396465809949)
          ·
            refine ⟨9067616596856773674678731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24180310924951396465809949 9067616596856773674678731)
            ·
              refine ⟨13601424895285160512018097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9067616596856773674678731 13601424895285160512018097)
              ·
                refine ⟨10201068671463870384013573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13601424895285160512018097 10201068671463870384013573)
                ·
                  refine ⟨1912700375899475697002545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10201068671463870384013573 1912700375899475697002545)
                  ·
                    refine ⟨1434525281924606772751909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1912700375899475697002545 1434525281924606772751909)
                    ·
                      refine ⟨268973490360863769890983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1434525281924606772751909 268973490360863769890983)
                      ·
                        rfl

theorem cell23_523824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 2, 4, 2, 4].length) (baseStart_523824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_523824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_523824 prefixEnd_523824 := by exact prefixLift 523824
  have htrace : WordTrace (prefixWord ++ tailWord_523824) baseStart_523824 baseEnd_523824 := by
    simpa [prefixWord, tailWord_523824, baseEnd_523824] using wordTrace_append hprefix tailTrace_523824
  have hstable : (prefixWord ++ tailWord_523824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523824).length < 2 ^ (prefixWord ++ tailWord_523824).sum := by decide
  have hdescent : baseEnd_523824 < baseStart_523824 := by decide
  rcases family_descends (prefixWord ++ tailWord_523824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523841 : List Nat := [1, 2, 5, 1, 1, 1, 2, 2, 2, 2, 4]
def baseStart_523841 : Nat := 118140960795 + 523841 * 2 ^ 59
def prefixEnd_523841 : Nat := 4983230072969 + 3 ^ 40 * 523841 * 2
def baseEnd_523841 : Nat := 268982219531990203378405

theorem tailTrace_523841 : CollatzResearch.WordTrace tailWord_523841 prefixEnd_523841 268982219531990203378405 := by
  unfold tailWord_523841
  simp only [CollatzResearch.WordTrace]
  refine ⟨19106050895220996765243377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12737367263480664510162251 19106050895220996765243377)
  ·
    refine ⟨14329538171415747573932533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19106050895220996765243377 14329538171415747573932533)
    ·
      refine ⟨1343394203570226335056175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14329538171415747573932533 1343394203570226335056175)
      ·
        refine ⟨2015091305355339502584263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1343394203570226335056175 2015091305355339502584263)
        ·
          refine ⟨3022636958033009253876395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2015091305355339502584263 3022636958033009253876395)
          ·
            refine ⟨4533955437049513880814593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3022636958033009253876395 4533955437049513880814593)
            ·
              refine ⟨3400466577787135410610945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4533955437049513880814593 3400466577787135410610945)
              ·
                refine ⟨2550349933340351557958209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3400466577787135410610945 2550349933340351557958209)
                ·
                  refine ⟨1912762450005263668468657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2550349933340351557958209 1912762450005263668468657)
                  ·
                    refine ⟨1434571837503947751351493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1912762450005263668468657 1434571837503947751351493)
                    ·
                      refine ⟨268982219531990203378405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1434571837503947751351493 268982219531990203378405)
                      ·
                        rfl

theorem cell23_523841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 2, 2, 2, 4].length) (baseStart_523841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_523841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_523841 prefixEnd_523841 := by exact prefixLift 523841
  have htrace : WordTrace (prefixWord ++ tailWord_523841) baseStart_523841 baseEnd_523841 := by
    simpa [prefixWord, tailWord_523841, baseEnd_523841] using wordTrace_append hprefix tailTrace_523841
  have hstable : (prefixWord ++ tailWord_523841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523841).length < 2 ^ (prefixWord ++ tailWord_523841).sum := by decide
  have hdescent : baseEnd_523841 < baseStart_523841 := by decide
  rcases family_descends (prefixWord ++ tailWord_523841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523845 : List Nat := [1, 3, 1, 1, 1, 4, 4, 2, 2, 2, 2]
def baseStart_523845 : Nat := 118140960795 + 523845 * 2 ^ 59
def prefixEnd_523845 : Nat := 4983230072969 + 3 ^ 40 * 523845 * 2
def baseEnd_523845 : Nat := 268984273454608187728387

theorem tailTrace_523845 : CollatzResearch.WordTrace tailWord_523845 prefixEnd_523845 268984273454608187728387 := by
  unfold tailWord_523845
  simp only [CollatzResearch.WordTrace]
  refine ⟨19106196787206505448388989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12737464524804336965592659 19106196787206505448388989)
  ·
    refine ⟨7164823795202439543145871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19106196787206505448388989 7164823795202439543145871)
    ·
      refine ⟨10747235692803659314718807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7164823795202439543145871 10747235692803659314718807)
      ·
        refine ⟨16120853539205488972078211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10747235692803659314718807 16120853539205488972078211)
        ·
          refine ⟨24181280308808233458117317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16120853539205488972078211 24181280308808233458117317)
          ·
            refine ⟨4533990057901543773396997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24181280308808233458117317 4533990057901543773396997)
            ·
              refine ⟨850123135856539457511937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4533990057901543773396997 850123135856539457511937)
              ·
                refine ⟨637592351892404593133953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 850123135856539457511937 637592351892404593133953)
                ·
                  refine ⟨478194263919303444850465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 637592351892404593133953 478194263919303444850465)
                  ·
                    refine ⟨358645697939477583637849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 478194263919303444850465 358645697939477583637849)
                    ·
                      refine ⟨268984273454608187728387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 358645697939477583637849 268984273454608187728387)
                      ·
                        rfl

theorem cell23_523845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 4, 2, 2, 2, 2].length) (baseStart_523845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_523845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_523845 prefixEnd_523845 := by exact prefixLift 523845
  have htrace : WordTrace (prefixWord ++ tailWord_523845) baseStart_523845 baseEnd_523845 := by
    simpa [prefixWord, tailWord_523845, baseEnd_523845] using wordTrace_append hprefix tailTrace_523845
  have hstable : (prefixWord ++ tailWord_523845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523845).length < 2 ^ (prefixWord ++ tailWord_523845).sum := by decide
  have hdescent : baseEnd_523845 < baseStart_523845 := by decide
  rcases family_descends (prefixWord ++ tailWord_523845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523854 : List Nat := [4, 1, 1, 1, 1, 2, 1, 1, 2, 1, 8]
def baseStart_523854 : Nat := 118140960795 + 523854 * 2 ^ 59
def prefixEnd_523854 : Nat := 4983230072969 + 3 ^ 40 * 523854 * 2
def baseEnd_523854 : Nat := 268988894780498652515845

theorem tailTrace_523854 : CollatzResearch.WordTrace tailWord_523854 prefixEnd_523854 268988894780498652515845 := by
  unfold tailWord_523854
  simp only [CollatzResearch.WordTrace]
  refine ⟨2388315630521737498183327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12737683362782599990311077 2388315630521737498183327)
  ·
    refine ⟨3582473445782606247274991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2388315630521737498183327 3582473445782606247274991)
    ·
      refine ⟨5373710168673909370912487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3582473445782606247274991 5373710168673909370912487)
      ·
        refine ⟨8060565253010864056368731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5373710168673909370912487 8060565253010864056368731)
        ·
          refine ⟨12090847879516296084553097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8060565253010864056368731 12090847879516296084553097)
          ·
            refine ⟨9068135909637222063414823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12090847879516296084553097 9068135909637222063414823)
            ·
              refine ⟨13602203864455833095122235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9068135909637222063414823 13602203864455833095122235)
              ·
                refine ⟨20403305796683749642683353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13602203864455833095122235 20403305796683749642683353)
                ·
                  refine ⟨15302479347512812232012515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20403305796683749642683353 15302479347512812232012515)
                  ·
                    refine ⟨22953719021269218348018773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15302479347512812232012515 22953719021269218348018773)
                    ·
                      refine ⟨268988894780498652515845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 22953719021269218348018773 268988894780498652515845)
                      ·
                        rfl

theorem cell23_523854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 1, 2, 1, 8].length) (baseStart_523854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_523854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_523854 prefixEnd_523854 := by exact prefixLift 523854
  have htrace : WordTrace (prefixWord ++ tailWord_523854) baseStart_523854 baseEnd_523854 := by
    simpa [prefixWord, tailWord_523854, baseEnd_523854] using wordTrace_append hprefix tailTrace_523854
  have hstable : (prefixWord ++ tailWord_523854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523854).length < 2 ^ (prefixWord ++ tailWord_523854).sum := by decide
  have hdescent : baseEnd_523854 < baseStart_523854 := by decide
  rcases family_descends (prefixWord ++ tailWord_523854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523864 : List Nat := [2, 1, 2, 2, 1, 2, 1, 4, 1, 7]
def baseStart_523864 : Nat := 118140960795 + 523864 * 2 ^ 59
def prefixEnd_523864 : Nat := 4983230072969 + 3 ^ 40 * 523864 * 2
def baseEnd_523864 : Nat := 89664676529014537796933

theorem tailTrace_523864 : CollatzResearch.WordTrace tailWord_523864 prefixEnd_523864 89664676529014537796933 := by
  unfold tailWord_523864
  simp only [CollatzResearch.WordTrace]
  refine ⟨9553444887068835846665323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12737926516091781128887097 9553444887068835846665323)
  ·
    refine ⟨14330167330603253769997985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9553444887068835846665323 14330167330603253769997985)
    ·
      refine ⟨10747625497952440327498489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14330167330603253769997985 10747625497952440327498489)
      ·
        refine ⟨8060719123464330245623867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10747625497952440327498489 8060719123464330245623867)
        ·
          refine ⟨12091078685196495368435801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8060719123464330245623867 12091078685196495368435801)
          ·
            refine ⟨9068309013897371526326851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12091078685196495368435801 9068309013897371526326851)
            ·
              refine ⟨13602463520846057289490277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9068309013897371526326851 13602463520846057289490277)
              ·
                refine ⟨2550461910158635741779427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13602463520846057289490277 2550461910158635741779427)
                ·
                  refine ⟨3825692865237953612669141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2550461910158635741779427 3825692865237953612669141)
                  ·
                    refine ⟨89664676529014537796933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3825692865237953612669141 89664676529014537796933)
                    ·
                      rfl

theorem cell23_523864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 4, 1, 7].length) (baseStart_523864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_523864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_523864 prefixEnd_523864 := by exact prefixLift 523864
  have htrace : WordTrace (prefixWord ++ tailWord_523864) baseStart_523864 baseEnd_523864 := by
    simpa [prefixWord, tailWord_523864, baseEnd_523864] using wordTrace_append hprefix tailTrace_523864
  have hstable : (prefixWord ++ tailWord_523864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523864).length < 2 ^ (prefixWord ++ tailWord_523864).sum := by decide
  have hdescent : baseEnd_523864 < baseStart_523864 := by decide
  rcases family_descends (prefixWord ++ tailWord_523864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523881 : List Nat := [1, 2, 1, 1, 1, 4, 5, 1, 2, 5]
def baseStart_523881 : Nat := 118140960795 + 523881 * 2 ^ 59
def prefixEnd_523881 : Nat := 4983230072969 + 3 ^ 40 * 523881 * 2
def baseEnd_523881 : Nat := 89667586252723348959407

theorem tailTrace_523881 : CollatzResearch.WordTrace tailWord_523881 prefixEnd_523881 89667586252723348959407 := by
  unfold tailWord_523881
  simp only [CollatzResearch.WordTrace]
  refine ⟨19107509815076083596699497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12738339876717389064466331 19107509815076083596699497)
  ·
    refine ⟨14330632361307062697524623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19107509815076083596699497 14330632361307062697524623)
    ·
      refine ⟨21495948541960594046286935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14330632361307062697524623 21495948541960594046286935)
      ·
        refine ⟨32243922812940891069430403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21495948541960594046286935 32243922812940891069430403)
        ·
          refine ⟨48365884219411336604145605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32243922812940891069430403 48365884219411336604145605)
          ·
            refine ⟨9068603291139625613277301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48365884219411336604145605 9068603291139625613277301)
            ·
              refine ⟨850181558544339901244747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9068603291139625613277301 850181558544339901244747)
              ·
                refine ⟨1275272337816509851867121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 850181558544339901244747 1275272337816509851867121)
                ·
                  refine ⟨956454253362382388900341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1275272337816509851867121 956454253362382388900341)
                  ·
                    refine ⟨89667586252723348959407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 956454253362382388900341 89667586252723348959407)
                    ·
                      rfl

theorem cell23_523881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 5, 1, 2, 5].length) (baseStart_523881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_523881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_523881 prefixEnd_523881 := by exact prefixLift 523881
  have htrace : WordTrace (prefixWord ++ tailWord_523881) baseStart_523881 baseEnd_523881 := by
    simpa [prefixWord, tailWord_523881, baseEnd_523881] using wordTrace_append hprefix tailTrace_523881
  have hstable : (prefixWord ++ tailWord_523881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523881).length < 2 ^ (prefixWord ++ tailWord_523881).sum := by decide
  have hdescent : baseEnd_523881 < baseStart_523881 := by decide
  rcases family_descends (prefixWord ++ tailWord_523881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523885 : List Nat := [1, 5, 1, 1, 4, 1, 2, 3, 5]
def baseStart_523885 : Nat := 118140960795 + 523885 * 2 ^ 59
def prefixEnd_523885 : Nat := 4983230072969 + 3 ^ 40 * 523885 * 2
def baseEnd_523885 : Nat := 29889423631198670136467

theorem tailTrace_523885 : CollatzResearch.WordTrace tailWord_523885 prefixEnd_523885 29889423631198670136467 := by
  unfold tailWord_523885
  simp only [CollatzResearch.WordTrace]
  refine ⟨19107655707061592279845109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12738437138041061519896739 19107655707061592279845109)
  ·
    refine ⟨1791342722537024276235479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 19107655707061592279845109 1791342722537024276235479)
    ·
      refine ⟨2687014083805536414353219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1791342722537024276235479 2687014083805536414353219)
      ·
        refine ⟨4030521125708304621529829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2687014083805536414353219 4030521125708304621529829)
        ·
          refine ⟨755722711070307116536843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4030521125708304621529829 755722711070307116536843)
          ·
            refine ⟨1133584066605460674805265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 755722711070307116536843 1133584066605460674805265)
            ·
              refine ⟨850188049954095506103949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1133584066605460674805265 850188049954095506103949)
              ·
                refine ⟨318820518732785814788981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 850188049954095506103949 318820518732785814788981)
                ·
                  refine ⟨29889423631198670136467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 318820518732785814788981 29889423631198670136467)
                  ·
                    rfl

theorem cell23_523885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 2, 3, 5].length) (baseStart_523885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_523885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_523885 prefixEnd_523885 := by exact prefixLift 523885
  have htrace : WordTrace (prefixWord ++ tailWord_523885) baseStart_523885 baseEnd_523885 := by
    simpa [prefixWord, tailWord_523885, baseEnd_523885] using wordTrace_append hprefix tailTrace_523885
  have hstable : (prefixWord ++ tailWord_523885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523885).length < 2 ^ (prefixWord ++ tailWord_523885).sum := by decide
  have hdescent : baseEnd_523885 < baseStart_523885 := by decide
  rcases family_descends (prefixWord ++ tailWord_523885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523921 : List Nat := [1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 3]
def baseStart_523921 : Nat := 118140960795 + 523921 * 2 ^ 59
def prefixEnd_523921 : Nat := 4983230072969 + 3 ^ 40 * 523921 * 2
def baseEnd_523921 : Nat := 269023297984349890378037

theorem tailTrace_523921 : CollatzResearch.WordTrace tailWord_523921 prefixEnd_523921 269023297984349890378037 := by
  unfold tailWord_523921
  simp only [CollatzResearch.WordTrace]
  refine ⟨19108968734931170428155617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12739312489954113618770411 19108968734931170428155617)
  ·
    refine ⟨14331726551198377821116713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19108968734931170428155617 14331726551198377821116713)
    ·
      refine ⟨10748794913398783365837535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14331726551198377821116713 10748794913398783365837535)
      ·
        refine ⟨16123192370098175048756303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10748794913398783365837535 16123192370098175048756303)
        ·
          refine ⟨24184788555147262573134455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16123192370098175048756303 24184788555147262573134455)
          ·
            refine ⟨36277182832720893859701683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24184788555147262573134455 36277182832720893859701683)
            ·
              refine ⟨54415774249081340789552525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36277182832720893859701683 54415774249081340789552525)
              ·
                refine ⟨20405915343405502796082197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54415774249081340789552525 20405915343405502796082197)
                ·
                  refine ⟨956527281722132943566353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 20405915343405502796082197 956527281722132943566353)
                  ·
                    refine ⟨717395461291599707674765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 956527281722132943566353 717395461291599707674765)
                    ·
                      refine ⟨269023297984349890378037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 717395461291599707674765 269023297984349890378037)
                      ·
                        rfl

theorem cell23_523921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 3].length) (baseStart_523921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_523921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_523921 prefixEnd_523921 := by exact prefixLift 523921
  have htrace : WordTrace (prefixWord ++ tailWord_523921) baseStart_523921 baseEnd_523921 := by
    simpa [prefixWord, tailWord_523921, baseEnd_523921] using wordTrace_append hprefix tailTrace_523921
  have hstable : (prefixWord ++ tailWord_523921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523921).length < 2 ^ (prefixWord ++ tailWord_523921).sum := by decide
  have hdescent : baseEnd_523921 < baseStart_523921 := by decide
  rcases family_descends (prefixWord ++ tailWord_523921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523928 : List Nat := [2, 1, 2, 4, 1, 2, 2, 2, 3, 4]
def baseStart_523928 : Nat := 118140960795 + 523928 * 2 ^ 59
def prefixEnd_523928 : Nat := 4983230072969 + 3 ^ 40 * 523928 * 2
def baseEnd_523928 : Nat := 89675630782977120996835

theorem tailTrace_523928 : CollatzResearch.WordTrace tailWord_523928 prefixEnd_523928 89675630782977120996835 := by
  unfold tailWord_523928
  simp only [CollatzResearch.WordTrace]
  refine ⟨9554612022952905311830219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12739482697270540415773625 9554612022952905311830219)
  ·
    refine ⟨14331918034429357967745329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9554612022952905311830219 14331918034429357967745329)
    ·
      refine ⟨10748938525822018475808997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14331918034429357967745329 10748938525822018475808997)
      ·
        refine ⟨2015425973591628464214187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10748938525822018475808997 2015425973591628464214187)
        ·
          refine ⟨3023138960387442696321281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2015425973591628464214187 3023138960387442696321281)
          ·
            refine ⟨2267354220290582022240961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3023138960387442696321281 2267354220290582022240961)
            ·
              refine ⟨1700515665217936516680721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2267354220290582022240961 1700515665217936516680721)
              ·
                refine ⟨1275386748913452387510541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1700515665217936516680721 1275386748913452387510541)
                ·
                  refine ⟨478270030842544645316453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1275386748913452387510541 478270030842544645316453)
                  ·
                    refine ⟨89675630782977120996835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 478270030842544645316453 89675630782977120996835)
                    ·
                      rfl

theorem cell23_523928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 2, 2, 3, 4].length) (baseStart_523928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_523928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_523928 prefixEnd_523928 := by exact prefixLift 523928
  have htrace : WordTrace (prefixWord ++ tailWord_523928) baseStart_523928 baseEnd_523928 := by
    simpa [prefixWord, tailWord_523928, baseEnd_523928] using wordTrace_append hprefix tailTrace_523928
  have hstable : (prefixWord ++ tailWord_523928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523928).length < 2 ^ (prefixWord ++ tailWord_523928).sum := by decide
  have hdescent : baseEnd_523928 < baseStart_523928 := by decide
  rcases family_descends (prefixWord ++ tailWord_523928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523962 : List Nat := [3, 1, 1, 1, 2, 5, 3, 2, 1, 4]
def baseStart_523962 : Nat := 118140960795 + 523962 * 2 ^ 59
def prefixEnd_523962 : Nat := 4983230072969 + 3 ^ 40 * 523962 * 2
def baseEnd_523962 : Nat := 89681450230394743321783

theorem tailTrace_523962 : CollatzResearch.WordTrace tailWord_523962 prefixEnd_523962 89681450230394743321783 := by
  unfold tailWord_523962
  simp only [CollatzResearch.WordTrace]
  refine ⟨4777616031945658607599535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12740309418521756286932093 4777616031945658607599535)
  ·
    refine ⟨7166424047918487911399303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4777616031945658607599535 7166424047918487911399303)
    ·
      refine ⟨10749636071877731867098955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7166424047918487911399303 10749636071877731867098955)
      ·
        refine ⟨16124454107816597800648433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10749636071877731867098955 16124454107816597800648433)
        ·
          refine ⟨12093340580862448350486325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16124454107816597800648433 12093340580862448350486325)
          ·
            refine ⟨1133750679455854532858093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12093340580862448350486325 1133750679455854532858093)
            ·
              refine ⟨425156504795945449821785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1133750679455854532858093 425156504795945449821785)
              ·
                refine ⟨318867378596959087366339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 425156504795945449821785 318867378596959087366339)
                ·
                  refine ⟨478301067895438631049509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 318867378596959087366339 478301067895438631049509)
                  ·
                    refine ⟨89681450230394743321783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 478301067895438631049509 89681450230394743321783)
                    ·
                      rfl

theorem cell23_523962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 3, 2, 1, 4].length) (baseStart_523962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_523962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_523962 prefixEnd_523962 := by exact prefixLift 523962
  have htrace : WordTrace (prefixWord ++ tailWord_523962) baseStart_523962 baseEnd_523962 := by
    simpa [prefixWord, tailWord_523962, baseEnd_523962] using wordTrace_append hprefix tailTrace_523962
  have hstable : (prefixWord ++ tailWord_523962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523962).length < 2 ^ (prefixWord ++ tailWord_523962).sum := by decide
  have hdescent : baseEnd_523962 < baseStart_523962 := by decide
  rcases family_descends (prefixWord ++ tailWord_523962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524005 : List Nat := [1, 3, 1, 4, 1, 1, 5, 1, 1, 5]
def baseStart_524005 : Nat := 118140960795 + 524005 * 2 ^ 59
def prefixEnd_524005 : Nat := 4983230072969 + 3 ^ 40 * 524005 * 2
def baseEnd_524005 : Nat := 89688810119775853909217

theorem tailTrace_524005 : CollatzResearch.WordTrace tailWord_524005 prefixEnd_524005 89688810119775853909217 := by
  unfold tailWord_524005
  simp only [CollatzResearch.WordTrace]
  refine ⟨19112032466626852774213469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12741354977751235182808979 19112032466626852774213469)
  ·
    refine ⟨7167012174985069790330051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19112032466626852774213469 7167012174985069790330051)
    ·
      refine ⟨10750518262477604685495077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7167012174985069790330051 10750518262477604685495077)
      ·
        refine ⟨2015722174214550878530327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10750518262477604685495077 2015722174214550878530327)
        ·
          refine ⟨3023583261321826317795491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2015722174214550878530327 3023583261321826317795491)
          ·
            refine ⟨4535374891982739476693237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3023583261321826317795491 4535374891982739476693237)
            ·
              refine ⟨425191396123381825939991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4535374891982739476693237 425191396123381825939991)
              ·
                refine ⟨637787094185072738909987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 425191396123381825939991 637787094185072738909987)
                ·
                  refine ⟨956680641277609108364981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 637787094185072738909987 956680641277609108364981)
                  ·
                    refine ⟨89688810119775853909217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 956680641277609108364981 89688810119775853909217)
                    ·
                      rfl

theorem cell23_524005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 5, 1, 1, 5].length) (baseStart_524005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_524005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_524005 prefixEnd_524005 := by exact prefixLift 524005
  have htrace : WordTrace (prefixWord ++ tailWord_524005) baseStart_524005 baseEnd_524005 := by
    simpa [prefixWord, tailWord_524005, baseEnd_524005] using wordTrace_append hprefix tailTrace_524005
  have hstable : (prefixWord ++ tailWord_524005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524005).length < 2 ^ (prefixWord ++ tailWord_524005).sum := by decide
  have hdescent : baseEnd_524005 < baseStart_524005 := by decide
  rcases family_descends (prefixWord ++ tailWord_524005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524028 : List Nat := [2, 2, 2, 1, 3, 1, 1, 1, 5, 2, 3]
def baseStart_524028 : Nat := 118140960795 + 524028 * 2 ^ 59
def prefixEnd_524028 : Nat := 4983230072969 + 3 ^ 40 * 524028 * 2
def baseEnd_524028 : Nat := 269078240414380971740045

theorem tailTrace_524028 : CollatzResearch.WordTrace tailWord_524028 prefixEnd_524028 269078240414380971740045 := by
  unfold tailWord_524028
  simp only [CollatzResearch.WordTrace]
  refine ⟨9556435672771763851150369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12741914230362351801533825 9556435672771763851150369)
  ·
    refine ⟨7167326754578822888362777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9556435672771763851150369 7167326754578822888362777)
    ·
      refine ⟨5375495065934117166272083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7167326754578822888362777 5375495065934117166272083)
      ·
        refine ⟨8063242598901175749408125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5375495065934117166272083 8063242598901175749408125)
        ·
          refine ⟨3023715974587940906028047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8063242598901175749408125 3023715974587940906028047)
          ·
            refine ⟨4535573961881911359042071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3023715974587940906028047 4535573961881911359042071)
            ·
              refine ⟨6803360942822867038563107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4535573961881911359042071 6803360942822867038563107)
              ·
                refine ⟨10205041414234300557844661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6803360942822867038563107 10205041414234300557844661)
                ·
                  refine ⟨956722632584465677297937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10205041414234300557844661 956722632584465677297937)
                  ·
                    refine ⟨717541974438349257973453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 956722632584465677297937 717541974438349257973453)
                    ·
                      refine ⟨269078240414380971740045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 717541974438349257973453 269078240414380971740045)
                      ·
                        rfl

theorem cell23_524028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 1, 5, 2, 3].length) (baseStart_524028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_524028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_524028 prefixEnd_524028 := by exact prefixLift 524028
  have htrace : WordTrace (prefixWord ++ tailWord_524028) baseStart_524028 baseEnd_524028 := by
    simpa [prefixWord, tailWord_524028, baseEnd_524028] using wordTrace_append hprefix tailTrace_524028
  have hstable : (prefixWord ++ tailWord_524028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524028).length < 2 ^ (prefixWord ++ tailWord_524028).sum := by decide
  have hdescent : baseEnd_524028 < baseStart_524028 := by decide
  rcases family_descends (prefixWord ++ tailWord_524028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524031 : List Nat := [1, 1, 2, 2, 1, 3, 5, 8]
def baseStart_524031 : Nat := 118140960795 + 524031 * 2 ^ 59
def prefixEnd_524031 : Nat := 4983230072969 + 3 ^ 40 * 524031 * 2
def baseEnd_524031 : Nat := 9965917809494239259353

theorem tailTrace_524031 : CollatzResearch.WordTrace tailWord_524031 prefixEnd_524031 9965917809494239259353 := by
  unfold tailWord_524031
  simp only [CollatzResearch.WordTrace]
  refine ⟨19112980764532659214659947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12741987176355106143106631 19112980764532659214659947)
  ·
    refine ⟨28669471146798988821989921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19112980764532659214659947 28669471146798988821989921)
    ·
      refine ⟨21502103360099241616492441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28669471146798988821989921 21502103360099241616492441)
      ·
        refine ⟨16126577520074431212369331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21502103360099241616492441 16126577520074431212369331)
        ·
          refine ⟨24189866280111646818553997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16126577520074431212369331 24189866280111646818553997)
          ·
            refine ⟨9071199855041867556957749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24189866280111646818553997 9071199855041867556957749)
            ·
              refine ⟨850424986410175083464789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9071199855041867556957749 850424986410175083464789)
              ·
                refine ⟨9965917809494239259353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 850424986410175083464789 9965917809494239259353)
                ·
                  rfl

theorem cell23_524031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 5, 8].length) (baseStart_524031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_524031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_524031 prefixEnd_524031 := by exact prefixLift 524031
  have htrace : WordTrace (prefixWord ++ tailWord_524031) baseStart_524031 baseEnd_524031 := by
    simpa [prefixWord, tailWord_524031, baseEnd_524031] using wordTrace_append hprefix tailTrace_524031
  have hstable : (prefixWord ++ tailWord_524031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524031).length < 2 ^ (prefixWord ++ tailWord_524031).sum := by decide
  have hdescent : baseEnd_524031 < baseStart_524031 := by decide
  rcases family_descends (prefixWord ++ tailWord_524031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524042 : List Nat := [3, 1, 2, 2, 1, 4, 1, 2, 3, 2, 2]
def baseStart_524042 : Nat := 118140960795 + 524042 * 2 ^ 59
def prefixEnd_524042 : Nat := 4983230072969 + 3 ^ 40 * 524042 * 2
def baseEnd_524042 : Nat := 269085429143543916964981

theorem tailTrace_524042 : CollatzResearch.WordTrace tailWord_524042 prefixEnd_524042 269085429143543916964981 := by
  unfold tailWord_524042
  simp only [CollatzResearch.WordTrace]
  refine ⟨4778345491873202023327595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12742254644995205395540253 4778345491873202023327595)
  ·
    refine ⟨7167518237809803034991393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4778345491873202023327595 7167518237809803034991393)
    ·
      refine ⟨5375638678357352276243545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7167518237809803034991393 5375638678357352276243545)
      ·
        refine ⟨4031729008768014207182659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5375638678357352276243545 4031729008768014207182659)
        ·
          refine ⟨6047593513152021310773989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4031729008768014207182659 6047593513152021310773989)
          ·
            refine ⟨1133923783716003995770123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6047593513152021310773989 1133923783716003995770123)
            ·
              refine ⟨1700885675574005993655185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1133923783716003995770123 1700885675574005993655185)
              ·
                refine ⟨1275664256680504495241389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1700885675574005993655185 1275664256680504495241389)
                ·
                  refine ⟨478374096255189185715521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1275664256680504495241389 478374096255189185715521)
                  ·
                    refine ⟨358780572191391889286641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 478374096255189185715521 358780572191391889286641)
                    ·
                      refine ⟨269085429143543916964981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 358780572191391889286641 269085429143543916964981)
                      ·
                        rfl

theorem cell23_524042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 1, 2, 3, 2, 2].length) (baseStart_524042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_524042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_524042 prefixEnd_524042 := by exact prefixLift 524042
  have htrace : WordTrace (prefixWord ++ tailWord_524042) baseStart_524042 baseEnd_524042 := by
    simpa [prefixWord, tailWord_524042, baseEnd_524042] using wordTrace_append hprefix tailTrace_524042
  have hstable : (prefixWord ++ tailWord_524042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524042).length < 2 ^ (prefixWord ++ tailWord_524042).sum := by decide
  have hdescent : baseEnd_524042 < baseStart_524042 := by decide
  rcases family_descends (prefixWord ++ tailWord_524042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524089 : List Nat := [1, 2, 1, 7, 2, 1, 1, 1, 1, 2, 4]
def baseStart_524089 : Nat := 118140960795 + 524089 * 2 ^ 59
def prefixEnd_524089 : Nat := 4983230072969 + 3 ^ 40 * 524089 * 2
def baseEnd_524089 : Nat := 269109562734305233077265

theorem tailTrace_524089 : CollatzResearch.WordTrace tailWord_524089 prefixEnd_524089 269109562734305233077265 := by
  unfold tailWord_524089
  simp only [CollatzResearch.WordTrace]
  refine ⟨19115096198322535120271321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12743397465548356746847547 19115096198322535120271321)
  ·
    refine ⟨14336322148741901340203491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19115096198322535120271321 14336322148741901340203491)
    ·
      refine ⟨21504483223112852010305237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14336322148741901340203491 21504483223112852010305237)
      ·
        refine ⟨504011325541707468991529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 21504483223112852010305237 504011325541707468991529)
        ·
          refine ⟨378008494156280601743647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 504011325541707468991529 378008494156280601743647)
          ·
            refine ⟨567012741234420902615471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 378008494156280601743647 567012741234420902615471)
            ·
              refine ⟨850519111851631353923207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 567012741234420902615471 850519111851631353923207)
              ·
                refine ⟨1275778667777447030884811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 850519111851631353923207 1275778667777447030884811)
                ·
                  refine ⟨1913668001666170546327217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1275778667777447030884811 1913668001666170546327217)
                  ·
                    refine ⟨1435251001249627909745413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1913668001666170546327217 1435251001249627909745413)
                    ·
                      refine ⟨269109562734305233077265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1435251001249627909745413 269109562734305233077265)
                      ·
                        rfl

theorem cell23_524089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 1, 1, 1, 2, 4].length) (baseStart_524089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_524089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_524089 prefixEnd_524089 := by exact prefixLift 524089
  have htrace : WordTrace (prefixWord ++ tailWord_524089) baseStart_524089 baseEnd_524089 := by
    simpa [prefixWord, tailWord_524089, baseEnd_524089] using wordTrace_append hprefix tailTrace_524089
  have hstable : (prefixWord ++ tailWord_524089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524089).length < 2 ^ (prefixWord ++ tailWord_524089).sum := by decide
  have hdescent : baseEnd_524089 < baseStart_524089 := by decide
  rcases family_descends (prefixWord ++ tailWord_524089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524149 : List Nat := [1, 3, 4, 1, 1, 1, 3, 3, 2, 2, 2]
def baseStart_524149 : Nat := 118140960795 + 524149 * 2 ^ 59
def prefixEnd_524149 : Nat := 4983230072969 + 3 ^ 40 * 524149 * 2
def baseEnd_524149 : Nat := 269140371573574998326989

theorem tailTrace_524149 : CollatzResearch.WordTrace tailWord_524149 prefixEnd_524149 269140371573574998326989 := by
  unfold tailWord_524149
  simp only [CollatzResearch.WordTrace]
  refine ⟨19117284578105165367455501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12744856385403443578303667 19117284578105165367455501)
  ·
    refine ⟨7168981716789437012795813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19117284578105165367455501 7168981716789437012795813)
    ·
      refine ⟨1344184071898019439899215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7168981716789437012795813 1344184071898019439899215)
      ·
        refine ⟨2016276107847029159848823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1344184071898019439899215 2016276107847029159848823)
        ·
          refine ⟨3024414161770543739773235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2016276107847029159848823 3024414161770543739773235)
          ·
            refine ⟨4536621242655815609659853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3024414161770543739773235 4536621242655815609659853)
            ·
              refine ⟨1701232965995930853622445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4536621242655815609659853 1701232965995930853622445)
              ·
                refine ⟨637962362248474070108417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1701232965995930853622445 637962362248474070108417)
                ·
                  refine ⟨478471771686355552581313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 637962362248474070108417 478471771686355552581313)
                  ·
                    refine ⟨358853828764766664435985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 478471771686355552581313 358853828764766664435985)
                    ·
                      refine ⟨269140371573574998326989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 358853828764766664435985 269140371573574998326989)
                      ·
                        rfl

theorem cell23_524149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 3, 3, 2, 2, 2].length) (baseStart_524149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_524149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_524149 prefixEnd_524149 := by exact prefixLift 524149
  have htrace : WordTrace (prefixWord ++ tailWord_524149) baseStart_524149 baseEnd_524149 := by
    simpa [prefixWord, tailWord_524149, baseEnd_524149] using wordTrace_append hprefix tailTrace_524149
  have hstable : (prefixWord ++ tailWord_524149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524149).length < 2 ^ (prefixWord ++ tailWord_524149).sum := by decide
  have hdescent : baseEnd_524149 < baseStart_524149 := by decide
  rcases family_descends (prefixWord ++ tailWord_524149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524189 : List Nat := [1, 4, 2, 1, 2, 4, 2, 2, 5]
def baseStart_524189 : Nat := 118140960795 + 524189 * 2 ^ 59
def prefixEnd_524189 : Nat := 4983230072969 + 3 ^ 40 * 524189 * 2
def baseEnd_524189 : Nat := 29906767866639426869645

theorem tailTrace_524189 : CollatzResearch.WordTrace tailWord_524189 prefixEnd_524189 29906767866639426869645 := by
  unfold tailWord_524189
  simp only [CollatzResearch.WordTrace]
  refine ⟨19118743497960252198911621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12745828998640168132607747 19118743497960252198911621)
  ·
    refine ⟨3584764405867547287295929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19118743497960252198911621 3584764405867547287295929)
    ·
      refine ⟨2688573304400660465471947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3584764405867547287295929 2688573304400660465471947)
      ·
        refine ⟨4032859956600990698207921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2688573304400660465471947 4032859956600990698207921)
        ·
          refine ⟨3024644967450743023655941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4032859956600990698207921 3024644967450743023655941)
          ·
            refine ⟨567120931397014316935489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3024644967450743023655941 567120931397014316935489)
            ·
              refine ⟨425340698547760737701617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 567120931397014316935489 425340698547760737701617)
              ·
                refine ⟨319005523910820553276213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 425340698547760737701617 319005523910820553276213)
                ·
                  refine ⟨29906767866639426869645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 319005523910820553276213 29906767866639426869645)
                  ·
                    rfl

theorem cell23_524189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 2, 2, 5].length) (baseStart_524189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_524189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_524189 prefixEnd_524189 := by exact prefixLift 524189
  have htrace : WordTrace (prefixWord ++ tailWord_524189) baseStart_524189 baseEnd_524189 := by
    simpa [prefixWord, tailWord_524189, baseEnd_524189] using wordTrace_append hprefix tailTrace_524189
  have hstable : (prefixWord ++ tailWord_524189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524189).length < 2 ^ (prefixWord ++ tailWord_524189).sum := by decide
  have hdescent : baseEnd_524189 < baseStart_524189 := by decide
  rcases family_descends (prefixWord ++ tailWord_524189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524218 : List Nat := [3, 1, 1, 1, 2, 1, 2, 1, 1, 6, 4]
def baseStart_524218 : Nat := 118140960795 + 524218 * 2 ^ 59
def prefixEnd_524218 : Nat := 4983230072969 + 3 ^ 40 * 524218 * 2
def baseEnd_524218 : Nat := 269175801738735228364171

theorem tailTrace_524218 : CollatzResearch.WordTrace tailWord_524218 prefixEnd_524218 269175801738735228364171 := by
  unfold tailWord_524218
  simp only [CollatzResearch.WordTrace]
  refine ⟨4779950303713797537929327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12746534143236793434478205 4779950303713797537929327)
  ·
    refine ⟨7169925455570696306893991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4779950303713797537929327 7169925455570696306893991)
    ·
      refine ⟨10754888183356044460340987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7169925455570696306893991 10754888183356044460340987)
      ·
        refine ⟨16132332275034066690511481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10754888183356044460340987 16132332275034066690511481)
        ·
          refine ⟨12099249206275550017883611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16132332275034066690511481 12099249206275550017883611)
          ·
            refine ⟨18148873809413325026825417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12099249206275550017883611 18148873809413325026825417)
            ·
              refine ⟨13611655357059993770119063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18148873809413325026825417 13611655357059993770119063)
              ·
                refine ⟨20417483035589990655178595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13611655357059993770119063 20417483035589990655178595)
                ·
                  refine ⟨30626224553384985982767893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20417483035589990655178595 30626224553384985982767893)
                  ·
                    refine ⟨1435604275939921217942245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30626224553384985982767893 1435604275939921217942245)
                    ·
                      refine ⟨269175801738735228364171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1435604275939921217942245 269175801738735228364171)
                      ·
                        rfl

theorem cell23_524218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 1, 1, 6, 4].length) (baseStart_524218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_524218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_524218 prefixEnd_524218 := by exact prefixLift 524218
  have htrace : WordTrace (prefixWord ++ tailWord_524218) baseStart_524218 baseEnd_524218 := by
    simpa [prefixWord, tailWord_524218, baseEnd_524218] using wordTrace_append hprefix tailTrace_524218
  have hstable : (prefixWord ++ tailWord_524218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524218).length < 2 ^ (prefixWord ++ tailWord_524218).sum := by decide
  have hdescent : baseEnd_524218 < baseStart_524218 := by decide
  rcases family_descends (prefixWord ++ tailWord_524218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524222 : List Nat := [4, 2, 1, 1, 1, 3, 3, 1, 2, 1, 4]
def baseStart_524222 : Nat := 118140960795 + 524222 * 2 ^ 59
def prefixEnd_524222 : Nat := 4983230072969 + 3 ^ 40 * 524222 * 2
def baseEnd_524222 : Nat := 269177855661353212714153

theorem tailTrace_524222 : CollatzResearch.WordTrace tailWord_524222 prefixEnd_524222 269177855661353212714153 := by
  unfold tailWord_524222
  simp only [CollatzResearch.WordTrace]
  refine ⟨2389993388355087354357865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12746631404560465889908613 2389993388355087354357865)
  ·
    refine ⟨1792495041266315515768399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2389993388355087354357865 1792495041266315515768399)
    ·
      refine ⟨2688742561899473273652599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1792495041266315515768399 2688742561899473273652599)
      ·
        refine ⟨4033113842849209910478899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2688742561899473273652599 4033113842849209910478899)
        ·
          refine ⟨6049670764273814865718349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4033113842849209910478899 6049670764273814865718349)
          ·
            refine ⟨2268626536602680574644381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6049670764273814865718349 2268626536602680574644381)
            ·
              refine ⟨850734951226005215491643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2268626536602680574644381 850734951226005215491643)
              ·
                refine ⟨1276102426839007823237465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 850734951226005215491643 1276102426839007823237465)
                ·
                  refine ⟨957076820129255867428099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1276102426839007823237465 957076820129255867428099)
                  ·
                    refine ⟨1435615230193883801142149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 957076820129255867428099 1435615230193883801142149)
                    ·
                      refine ⟨269177855661353212714153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1435615230193883801142149 269177855661353212714153)
                      ·
                        rfl

theorem cell23_524222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 3, 1, 2, 1, 4].length) (baseStart_524222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_524222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_524222 prefixEnd_524222 := by exact prefixLift 524222
  have htrace : WordTrace (prefixWord ++ tailWord_524222) baseStart_524222 baseEnd_524222 := by
    simpa [prefixWord, tailWord_524222, baseEnd_524222] using wordTrace_append hprefix tailTrace_524222
  have hstable : (prefixWord ++ tailWord_524222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524222).length < 2 ^ (prefixWord ++ tailWord_524222).sum := by decide
  have hdescent : baseEnd_524222 < baseStart_524222 := by decide
  rcases family_descends (prefixWord ++ tailWord_524222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524245 : List Nat := [1, 3, 2, 3, 2, 2, 1, 1, 8]
def baseStart_524245 : Nat := 118140960795 + 524245 * 2 ^ 59
def prefixEnd_524245 : Nat := 4983230072969 + 3 ^ 40 * 524245 * 2
def baseEnd_524245 : Nat := 29909962857378513636283

theorem tailTrace_524245 : CollatzResearch.WordTrace tailWord_524245 prefixEnd_524245 29909962857378513636283 := by
  unfold tailWord_524245
  simp only [CollatzResearch.WordTrace]
  refine ⟨19120785985757373762950189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12747190657171582508633459 19120785985757373762950189)
  ·
    refine ⟨7170294744659015161106321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19120785985757373762950189 7170294744659015161106321)
    ·
      refine ⟨5377721058494261370829741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7170294744659015161106321 5377721058494261370829741)
      ·
        refine ⟨2016645396935348014061153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5377721058494261370829741 2016645396935348014061153)
        ·
          refine ⟨1512484047701511010545865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2016645396935348014061153 1512484047701511010545865)
          ·
            refine ⟨1134363035776133257909399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1512484047701511010545865 1134363035776133257909399)
            ·
              refine ⟨1701544553664199886864099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1134363035776133257909399 1701544553664199886864099)
              ·
                refine ⟨2552316830496299830296149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1701544553664199886864099 2552316830496299830296149)
                ·
                  refine ⟨29909962857378513636283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2552316830496299830296149 29909962857378513636283)
                  ·
                    rfl

theorem cell23_524245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 1, 1, 8].length) (baseStart_524245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_524245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_524245 prefixEnd_524245 := by exact prefixLift 524245
  have htrace : WordTrace (prefixWord ++ tailWord_524245) baseStart_524245 baseEnd_524245 := by
    simpa [prefixWord, tailWord_524245, baseEnd_524245] using wordTrace_append hprefix tailTrace_524245
  have hstable : (prefixWord ++ tailWord_524245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524245).length < 2 ^ (prefixWord ++ tailWord_524245).sum := by decide
  have hdescent : baseEnd_524245 < baseStart_524245 := by decide
  rcases family_descends (prefixWord ++ tailWord_524245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524248 : List Nat := [2, 1, 2, 2, 2, 2, 1, 1, 1, 1, 8]
def baseStart_524248 : Nat := 118140960795 + 524248 * 2 ^ 59
def prefixEnd_524248 : Nat := 4983230072969 + 3 ^ 40 * 524248 * 2
def baseEnd_524248 : Nat := 269191206158370110989033

theorem tailTrace_524248 : CollatzResearch.WordTrace tailWord_524248 prefixEnd_524248 269191206158370110989033 := by
  unfold tailWord_524248
  simp only [CollatzResearch.WordTrace]
  refine ⟨9560447702373252637654699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12747263603164336850206265 9560447702373252637654699)
  ·
    refine ⟨14340671553559878956482049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9560447702373252637654699 14340671553559878956482049)
    ·
      refine ⟨10755503665169909217361537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14340671553559878956482049 10755503665169909217361537)
      ·
        refine ⟨8066627748877431913021153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10755503665169909217361537 8066627748877431913021153)
        ·
          refine ⟨6049970811658073934765865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8066627748877431913021153 6049970811658073934765865)
          ·
            refine ⟨4537478108743555451074399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6049970811658073934765865 4537478108743555451074399)
            ·
              refine ⟨6806217163115333176611599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4537478108743555451074399 6806217163115333176611599)
              ·
                refine ⟨10209325744672999764917399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6806217163115333176611599 10209325744672999764917399)
                ·
                  refine ⟨15313988617009499647376099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10209325744672999764917399 15313988617009499647376099)
                  ·
                    refine ⟨22970982925514249471064149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15313988617009499647376099 22970982925514249471064149)
                    ·
                      refine ⟨269191206158370110989033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 22970982925514249471064149 269191206158370110989033)
                      ·
                        rfl

theorem cell23_524248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 1, 1, 1, 8].length) (baseStart_524248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_524248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_524248 prefixEnd_524248 := by exact prefixLift 524248
  have htrace : WordTrace (prefixWord ++ tailWord_524248) baseStart_524248 baseEnd_524248 := by
    simpa [prefixWord, tailWord_524248, baseEnd_524248] using wordTrace_append hprefix tailTrace_524248
  have hstable : (prefixWord ++ tailWord_524248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524248).length < 2 ^ (prefixWord ++ tailWord_524248).sum := by decide
  have hdescent : baseEnd_524248 < baseStart_524248 := by decide
  rcases family_descends (prefixWord ++ tailWord_524248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524268 : List Nat := [2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 7]
def baseStart_524268 : Nat := 118140960795 + 524268 * 2 ^ 59
def prefixEnd_524268 : Nat := 4983230072969 + 3 ^ 40 * 524268 * 2
def baseEnd_524268 : Nat := 269201475771460032738941

theorem tailTrace_524268 : CollatzResearch.WordTrace tailWord_524268 prefixEnd_524268 269201475771460032738941 := by
  unfold tailWord_524268
  simp only [CollatzResearch.WordTrace]
  refine ⟨9560812432337024345518729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12747749909782699127358305 9560812432337024345518729)
  ·
    refine ⟨7170609324252768259139047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9560812432337024345518729 7170609324252768259139047)
    ·
      refine ⟨10755913986379152388708571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7170609324252768259139047 10755913986379152388708571)
      ·
        refine ⟨16133870979568728583062857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10755913986379152388708571 16133870979568728583062857)
        ·
          refine ⟨12100403234676546437297143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16133870979568728583062857 12100403234676546437297143)
          ·
            refine ⟨18150604852014819655945715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12100403234676546437297143 18150604852014819655945715)
            ·
              refine ⟨27225907278022229483918573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18150604852014819655945715 27225907278022229483918573)
              ·
                refine ⟨10209715229258336056469465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27225907278022229483918573 10209715229258336056469465)
                ·
                  refine ⟨7657286421943752042352099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10209715229258336056469465 7657286421943752042352099)
                  ·
                    refine ⟨11485929632915628063528149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7657286421943752042352099 11485929632915628063528149)
                    ·
                      refine ⟨269201475771460032738941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 11485929632915628063528149 269201475771460032738941)
                      ·
                        rfl

theorem cell23_524268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 7].length) (baseStart_524268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_524268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_524268 prefixEnd_524268 := by exact prefixLift 524268
  have htrace : WordTrace (prefixWord ++ tailWord_524268) baseStart_524268 baseEnd_524268 := by
    simpa [prefixWord, tailWord_524268, baseEnd_524268] using wordTrace_append hprefix tailTrace_524268
  have hstable : (prefixWord ++ tailWord_524268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524268).length < 2 ^ (prefixWord ++ tailWord_524268).sum := by decide
  have hdescent : baseEnd_524268 < baseStart_524268 := by decide
  rcases family_descends (prefixWord ++ tailWord_524268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524272 : List Nat := [2, 1, 1, 1, 3, 2, 4, 2, 3, 1, 3]
def baseStart_524272 : Nat := 118140960795 + 524272 * 2 ^ 59
def prefixEnd_524272 : Nat := 4983230072969 + 3 ^ 40 * 524272 * 2
def baseEnd_524272 : Nat := 269203529694078017088923

theorem tailTrace_524272 : CollatzResearch.WordTrace tailWord_524272 prefixEnd_524272 269203529694078017088923 := by
  unfold tailWord_524272
  simp only [CollatzResearch.WordTrace]
  refine ⟨9560885378329778687091535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12747847171106371582788713 9560885378329778687091535)
  ·
    refine ⟨14341328067494668030637303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9560885378329778687091535 14341328067494668030637303)
    ·
      refine ⟨21511992101242002045955955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14341328067494668030637303 21511992101242002045955955)
      ·
        refine ⟨32267988151863003068933933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21511992101242002045955955 32267988151863003068933933)
        ·
          refine ⟨12100495556948626150850225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32267988151863003068933933 12100495556948626150850225)
          ·
            refine ⟨9075371667711469613137669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12100495556948626150850225 9075371667711469613137669)
            ·
              refine ⟨1701632187695900552463313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9075371667711469613137669 1701632187695900552463313)
              ·
                refine ⟨1276224140771925414347485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1701632187695900552463313 1276224140771925414347485)
                ·
                  refine ⟨478584052789472030380307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1276224140771925414347485 478584052789472030380307)
                  ·
                    refine ⟨717876079184208045570461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 478584052789472030380307 717876079184208045570461)
                    ·
                      refine ⟨269203529694078017088923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 717876079184208045570461 269203529694078017088923)
                      ·
                        rfl

theorem cell23_524272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4, 2, 3, 1, 3].length) (baseStart_524272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_524272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_524272 prefixEnd_524272 := by exact prefixLift 524272
  have htrace : WordTrace (prefixWord ++ tailWord_524272) baseStart_524272 baseEnd_524272 := by
    simpa [prefixWord, tailWord_524272, baseEnd_524272] using wordTrace_append hprefix tailTrace_524272
  have hstable : (prefixWord ++ tailWord_524272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524272).length < 2 ^ (prefixWord ++ tailWord_524272).sum := by decide
  have hdescent : baseEnd_524272 < baseStart_524272 := by decide
  rcases family_descends (prefixWord ++ tailWord_524272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524325 : List Nat := [1, 3, 1, 2, 2, 3, 2, 1, 1, 1, 6]
def baseStart_524325 : Nat := 118140960795 + 524325 * 2 ^ 59
def prefixEnd_524325 : Nat := 4983230072969 + 3 ^ 40 * 524325 * 2
def baseEnd_524325 : Nat := 269230744168766309726179

theorem tailTrace_524325 : CollatzResearch.WordTrace tailWord_524325 prefixEnd_524325 269230744168766309726179 := by
  unfold tailWord_524325
  simp only [CollatzResearch.WordTrace]
  refine ⟨19123703825467547425862429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12749135883645031617241619 19123703825467547425862429)
  ·
    refine ⟨7171388934550330284698411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19123703825467547425862429 7171388934550330284698411)
    ·
      refine ⟨10757083401825495427047617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7171388934550330284698411 10757083401825495427047617)
      ·
        refine ⟨8067812551369121570285713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10757083401825495427047617 8067812551369121570285713)
        ·
          refine ⟨6050859413526841177714285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8067812551369121570285713 6050859413526841177714285)
          ·
            refine ⟨2269072280072565441642857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6050859413526841177714285 2269072280072565441642857)
            ·
              refine ⟨1701804210054424081232143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2269072280072565441642857 1701804210054424081232143)
              ·
                refine ⟨2552706315081636121848215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1701804210054424081232143 2552706315081636121848215)
                ·
                  refine ⟨3829059472622454182772323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2552706315081636121848215 3829059472622454182772323)
                  ·
                    refine ⟨5743589208933681274158485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3829059472622454182772323 5743589208933681274158485)
                    ·
                      refine ⟨269230744168766309726179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 5743589208933681274158485 269230744168766309726179)
                      ·
                        rfl

theorem cell23_524325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 2, 1, 1, 1, 6].length) (baseStart_524325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_524325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_524325 prefixEnd_524325 := by exact prefixLift 524325
  have htrace : WordTrace (prefixWord ++ tailWord_524325) baseStart_524325 baseEnd_524325 := by
    simpa [prefixWord, tailWord_524325, baseEnd_524325] using wordTrace_append hprefix tailTrace_524325
  have hstable : (prefixWord ++ tailWord_524325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524325).length < 2 ^ (prefixWord ++ tailWord_524325).sum := by decide
  have hdescent : baseEnd_524325 < baseStart_524325 := by decide
  rcases family_descends (prefixWord ++ tailWord_524325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524332 : List Nat := [2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 3]
def baseStart_524332 : Nat := 118140960795 + 524332 * 2 ^ 59
def prefixEnd_524332 : Nat := 4983230072969 + 3 ^ 40 * 524332 * 2
def baseEnd_524332 : Nat := 269234338533347782338647

theorem tailTrace_524332 : CollatzResearch.WordTrace tailWord_524332 prefixEnd_524332 269234338533347782338647 := by
  unfold tailWord_524332
  simp only [CollatzResearch.WordTrace]
  refine ⟨9561979568221093810683625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12749306090961458414244833 9561979568221093810683625)
  ·
    refine ⟨7171484676165820358012719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9561979568221093810683625 7171484676165820358012719)
    ·
      refine ⟨10757227014248730537019079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7171484676165820358012719 10757227014248730537019079)
      ·
        refine ⟨16135840521373095805528619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10757227014248730537019079 16135840521373095805528619)
        ·
          refine ⟨24203760782059643708292929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16135840521373095805528619 24203760782059643708292929)
          ·
            refine ⟨18152820586544732781219697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24203760782059643708292929 18152820586544732781219697)
            ·
              refine ⟨13614615439908549585914773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18152820586544732781219697 13614615439908549585914773)
              ·
                refine ⟨638185098745713261839755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 13614615439908549585914773 638185098745713261839755)
                ·
                  refine ⟨957277648118569892759633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 638185098745713261839755 957277648118569892759633)
                  ·
                    refine ⟨717958236088927419569725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 957277648118569892759633 717958236088927419569725)
                    ·
                      refine ⟨269234338533347782338647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 717958236088927419569725 269234338533347782338647)
                      ·
                        rfl

theorem cell23_524332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 3].length) (baseStart_524332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_524332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_524332 prefixEnd_524332 := by exact prefixLift 524332
  have htrace : WordTrace (prefixWord ++ tailWord_524332) baseStart_524332 baseEnd_524332 := by
    simpa [prefixWord, tailWord_524332, baseEnd_524332] using wordTrace_append hprefix tailTrace_524332
  have hstable : (prefixWord ++ tailWord_524332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524332).length < 2 ^ (prefixWord ++ tailWord_524332).sum := by decide
  have hdescent : baseEnd_524332 < baseStart_524332 := by decide
  rcases family_descends (prefixWord ++ tailWord_524332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524346 : List Nat := [3, 1, 1, 1, 3, 1, 1, 7, 1, 2, 2]
def baseStart_524346 : Nat := 118140960795 + 524346 * 2 ^ 59
def prefixEnd_524346 : Nat := 4983230072969 + 3 ^ 40 * 524346 * 2
def baseEnd_524346 : Nat := 269241527262510727563583

theorem tailTrace_524346 : CollatzResearch.WordTrace tailWord_524346 prefixEnd_524346 269241527262510727563583 := by
  unfold tailWord_524346
  simp only [CollatzResearch.WordTrace]
  refine ⟨4781117439597867003094223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12749646505594312008251261 4781117439597867003094223)
  ·
    refine ⟨7171676159396800504641335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4781117439597867003094223 7171676159396800504641335)
    ·
      refine ⟨10757514239095200756962003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7171676159396800504641335 10757514239095200756962003)
      ·
        refine ⟨16136271358642801135443005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10757514239095200756962003 16136271358642801135443005)
        ·
          refine ⟨6051101759491050425791127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16136271358642801135443005 6051101759491050425791127)
          ·
            refine ⟨9076652639236575638686691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6051101759491050425791127 9076652639236575638686691)
            ·
              refine ⟨13614978958854863458030037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9076652639236575638686691 13614978958854863458030037)
              ·
                refine ⟨319101069348160862297579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 13614978958854863458030037 319101069348160862297579)
                ·
                  refine ⟨478651604022241293446369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 319101069348160862297579 478651604022241293446369)
                  ·
                    refine ⟨358988703016680970084777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 478651604022241293446369 358988703016680970084777)
                    ·
                      refine ⟨269241527262510727563583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 358988703016680970084777 269241527262510727563583)
                      ·
                        rfl

theorem cell23_524346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 7, 1, 2, 2].length) (baseStart_524346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_524346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_524346 prefixEnd_524346 := by exact prefixLift 524346
  have htrace : WordTrace (prefixWord ++ tailWord_524346) baseStart_524346 baseEnd_524346 := by
    simpa [prefixWord, tailWord_524346, baseEnd_524346] using wordTrace_append hprefix tailTrace_524346
  have hstable : (prefixWord ++ tailWord_524346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524346).length < 2 ^ (prefixWord ++ tailWord_524346).sum := by decide
  have hdescent : baseEnd_524346 < baseStart_524346 := by decide
  rcases family_descends (prefixWord ++ tailWord_524346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524385 : List Nat := [1, 2, 3, 1, 1, 2, 1, 1, 4, 3, 4]
def baseStart_524385 : Nat := 118140960795 + 524385 * 2 ^ 59
def prefixEnd_524385 : Nat := 4983230072969 + 3 ^ 40 * 524385 * 2
def baseEnd_524385 : Nat := 269261553008036074975903

theorem tailTrace_524385 : CollatzResearch.WordTrace tailWord_524385 prefixEnd_524385 269261553008036074975903 := by
  unfold tailWord_524385
  simp only [CollatzResearch.WordTrace]
  refine ⟨19125892205250177673046609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12750594803500118448697739 19125892205250177673046609)
  ·
    refine ⟨14344419153937633254784957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19125892205250177673046609 14344419153937633254784957)
    ·
      refine ⟨5379157182726612470544359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14344419153937633254784957 5379157182726612470544359)
      ·
        refine ⟨8068735774089918705816539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5379157182726612470544359 8068735774089918705816539)
        ·
          refine ⟨12103103661134878058724809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8068735774089918705816539 12103103661134878058724809)
          ·
            refine ⟨9077327745851158544043607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12103103661134878058724809 9077327745851158544043607)
            ·
              refine ⟨13615991618776737816065411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9077327745851158544043607 13615991618776737816065411)
              ·
                refine ⟨20423987428165106724098117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13615991618776737816065411 20423987428165106724098117)
                ·
                  refine ⟨3829497642780957510768397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20423987428165106724098117 3829497642780957510768397)
                  ·
                    refine ⟨1436061616042859066538149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3829497642780957510768397 1436061616042859066538149)
                    ·
                      refine ⟨269261553008036074975903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1436061616042859066538149 269261553008036074975903)
                      ·
                        rfl

theorem cell23_524385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 1, 4, 3, 4].length) (baseStart_524385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_524385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_524385 prefixEnd_524385 := by exact prefixLift 524385
  have htrace : WordTrace (prefixWord ++ tailWord_524385) baseStart_524385 baseEnd_524385 := by
    simpa [prefixWord, tailWord_524385, baseEnd_524385] using wordTrace_append hprefix tailTrace_524385
  have hstable : (prefixWord ++ tailWord_524385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524385).length < 2 ^ (prefixWord ++ tailWord_524385).sum := by decide
  have hdescent : baseEnd_524385 < baseStart_524385 := by decide
  rcases family_descends (prefixWord ++ tailWord_524385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524389 : List Nat := [1, 3, 1, 3, 2, 2, 2, 1, 3, 3, 2]
def baseStart_524389 : Nat := 118140960795 + 524389 * 2 ^ 59
def prefixEnd_524389 : Nat := 4983230072969 + 3 ^ 40 * 524389 * 2
def baseEnd_524389 : Nat := 269263606930654059325885

theorem tailTrace_524389 : CollatzResearch.WordTrace tailWord_524389 prefixEnd_524389 269263606930654059325885 := by
  unfold tailWord_524389
  simp only [CollatzResearch.WordTrace]
  refine ⟨19126038097235686356192221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12750692064823790904128147 19126038097235686356192221)
  ·
    refine ⟨7172264286463382383572083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19126038097235686356192221 7172264286463382383572083)
    ·
      refine ⟨10758396429695073575358125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7172264286463382383572083 10758396429695073575358125)
      ·
        refine ⟨4034398661135652590759297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10758396429695073575358125 4034398661135652590759297)
        ·
          refine ⟨3025798995851739443069473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4034398661135652590759297 3025798995851739443069473)
          ·
            refine ⟨2269349246888804582302105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3025798995851739443069473 2269349246888804582302105)
            ·
              refine ⟨1702011935166603436726579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2269349246888804582302105 1702011935166603436726579)
              ·
                refine ⟨2553017902749905155089869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1702011935166603436726579 2553017902749905155089869)
                ·
                  refine ⟨957381713531214433158701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2553017902749905155089869 957381713531214433158701)
                  ·
                    refine ⟨359018142574205412434513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 957381713531214433158701 359018142574205412434513)
                    ·
                      refine ⟨269263606930654059325885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 359018142574205412434513 269263606930654059325885)
                      ·
                        rfl

theorem cell23_524389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 2, 1, 3, 3, 2].length) (baseStart_524389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_524389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_524389 prefixEnd_524389 := by exact prefixLift 524389
  have htrace : WordTrace (prefixWord ++ tailWord_524389) baseStart_524389 baseEnd_524389 := by
    simpa [prefixWord, tailWord_524389, baseEnd_524389] using wordTrace_append hprefix tailTrace_524389
  have hstable : (prefixWord ++ tailWord_524389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524389).length < 2 ^ (prefixWord ++ tailWord_524389).sum := by decide
  have hdescent : baseEnd_524389 < baseStart_524389 := by decide
  rcases family_descends (prefixWord ++ tailWord_524389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524472 : List Nat := [2, 1, 2, 1, 2, 1, 5, 2, 2, 5]
def baseStart_524472 : Nat := 118140960795 + 524472 * 2 ^ 59
def prefixEnd_524472 : Nat := 4983230072969 + 3 ^ 40 * 524472 * 2
def baseEnd_524472 : Nat := 89768741941659078196001

theorem tailTrace_524472 : CollatzResearch.WordTrace tailWord_524472 prefixEnd_524472 89768741941659078196001 := by
  unfold tailWord_524472
  simp only [CollatzResearch.WordTrace]
  refine ⟨9564532677967495765731835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12752710237289994354309113 9564532677967495765731835)
  ·
    refine ⟨14346799016951243648597753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9564532677967495765731835 14346799016951243648597753)
    ·
      refine ⟨10760099262713432736448315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14346799016951243648597753 10760099262713432736448315)
      ·
        refine ⟨16140148894070149104672473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10760099262713432736448315 16140148894070149104672473)
        ·
          refine ⟨12105111670552611828504355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16140148894070149104672473 12105111670552611828504355)
          ·
            refine ⟨18157667505828917742756533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12105111670552611828504355 18157667505828917742756533)
            ·
              refine ⟨1702281328671461038383425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18157667505828917742756533 1702281328671461038383425)
              ·
                refine ⟨1276710996503595778787569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1702281328671461038383425 1276710996503595778787569)
                ·
                  refine ⟨957533247377696834090677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1276710996503595778787569 957533247377696834090677)
                  ·
                    refine ⟨89768741941659078196001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 957533247377696834090677 89768741941659078196001)
                    ·
                      rfl

theorem cell23_524472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5, 2, 2, 5].length) (baseStart_524472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_524472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_524472 prefixEnd_524472 := by exact prefixLift 524472
  have htrace : WordTrace (prefixWord ++ tailWord_524472) baseStart_524472 baseEnd_524472 := by
    simpa [prefixWord, tailWord_524472, baseEnd_524472] using wordTrace_append hprefix tailTrace_524472
  have hstable : (prefixWord ++ tailWord_524472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524472).length < 2 ^ (prefixWord ++ tailWord_524472).sum := by decide
  have hdescent : baseEnd_524472 < baseStart_524472 := by decide
  rcases family_descends (prefixWord ++ tailWord_524472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524476 : List Nat := [2, 2, 2, 3, 4, 1, 1, 1, 7]
def baseStart_524476 : Nat := 118140960795 + 524476 * 2 ^ 59
def prefixEnd_524476 : Nat := 4983230072969 + 3 ^ 40 * 524476 * 2
def baseEnd_524476 : Nat := 29923142194177246548665

theorem tailTrace_524476 : CollatzResearch.WordTrace tailWord_524476 prefixEnd_524476 29923142194177246548665 := by
  unfold tailWord_524476
  simp only [CollatzResearch.WordTrace]
  refine ⟨9564605623960250107304641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12752807498613666809739521 9564605623960250107304641)
  ·
    refine ⟨7173454217970187580478481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9564605623960250107304641 7173454217970187580478481)
    ·
      refine ⟨5380090663477640685358861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7173454217970187580478481 5380090663477640685358861)
      ·
        refine ⟨2017533998804115257009573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5380090663477640685358861 2017533998804115257009573)
        ·
          refine ⟨378287624775771610689295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2017533998804115257009573 378287624775771610689295)
          ·
            refine ⟨567431437163657416033943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 378287624775771610689295 567431437163657416033943)
            ·
              refine ⟨851147155745486124050915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 567431437163657416033943 851147155745486124050915)
              ·
                refine ⟨1276720733618229186076373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 851147155745486124050915 1276720733618229186076373)
                ·
                  refine ⟨29923142194177246548665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1276720733618229186076373 29923142194177246548665)
                  ·
                    rfl

theorem cell23_524476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 1, 1, 7].length) (baseStart_524476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_524476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_524476 prefixEnd_524476 := by exact prefixLift 524476
  have htrace : WordTrace (prefixWord ++ tailWord_524476) baseStart_524476 baseEnd_524476 := by
    simpa [prefixWord, tailWord_524476, baseEnd_524476] using wordTrace_append hprefix tailTrace_524476
  have hstable : (prefixWord ++ tailWord_524476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524476).length < 2 ^ (prefixWord ++ tailWord_524476).sum := by decide
  have hdescent : baseEnd_524476 < baseStart_524476 := by decide
  rcases family_descends (prefixWord ++ tailWord_524476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524522 : List Nat := [3, 1, 3, 1, 1, 2, 2, 1, 2, 1, 6]
def baseStart_524522 : Nat := 118140960795 + 524522 * 2 ^ 59
def prefixEnd_524522 : Nat := 4983230072969 + 3 ^ 40 * 524522 * 2
def baseEnd_524522 : Nat := 269331899857702038962773

theorem tailTrace_524522 : CollatzResearch.WordTrace tailWord_524522 prefixEnd_524522 269331899857702038962773 := by
  unfold tailWord_524522
  simp only [CollatzResearch.WordTrace]
  refine ⟨4782722251438462517695955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12753926003835900047189213 4782722251438462517695955)
  ·
    refine ⟨7174083377157693776543933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4782722251438462517695955 7174083377157693776543933)
    ·
      refine ⟨2690281266434135166203975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7174083377157693776543933 2690281266434135166203975)
      ·
        refine ⟨4035421899651202749305963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2690281266434135166203975 4035421899651202749305963)
        ·
          refine ⟨6053132849476804123958945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4035421899651202749305963 6053132849476804123958945)
          ·
            refine ⟨4539849637107603092969209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6053132849476804123958945 4539849637107603092969209)
            ·
              refine ⟨3404887227830702319726907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4539849637107603092969209 3404887227830702319726907)
              ·
                refine ⟨5107330841746053479590361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3404887227830702319726907 5107330841746053479590361)
                ·
                  refine ⟨3830498131309540109692771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5107330841746053479590361 3830498131309540109692771)
                  ·
                    refine ⟨5745747196964310164539157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3830498131309540109692771 5745747196964310164539157)
                    ·
                      refine ⟨269331899857702038962773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 5745747196964310164539157 269331899857702038962773)
                      ·
                        rfl

theorem cell23_524522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 1, 2, 1, 6].length) (baseStart_524522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_524522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_524522 prefixEnd_524522 := by exact prefixLift 524522
  have htrace : WordTrace (prefixWord ++ tailWord_524522) baseStart_524522 baseEnd_524522 := by
    simpa [prefixWord, tailWord_524522, baseEnd_524522] using wordTrace_append hprefix tailTrace_524522
  have hstable : (prefixWord ++ tailWord_524522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524522).length < 2 ^ (prefixWord ++ tailWord_524522).sum := by decide
  have hdescent : baseEnd_524522 < baseStart_524522 := by decide
  rcases family_descends (prefixWord ++ tailWord_524522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524529 : List Nat := [1, 2, 2, 2, 2, 1, 4, 2, 2, 2, 3]
def baseStart_524529 : Nat := 118140960795 + 524529 * 2 ^ 59
def prefixEnd_524529 : Nat := 4983230072969 + 3 ^ 40 * 524529 * 2
def baseEnd_524529 : Nat := 269335494222283511575241

theorem tailTrace_524529 : CollatzResearch.WordTrace tailWord_524529 prefixEnd_524529 269335494222283511575241 := by
  unfold tailWord_524529
  simp only [CollatzResearch.WordTrace]
  refine ⟨19131144316728490266288641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12754096211152326844192427 19131144316728490266288641)
  ·
    refine ⟨14348358237546367699716481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19131144316728490266288641 14348358237546367699716481)
    ·
      refine ⟨10761268678159775774787361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14348358237546367699716481 10761268678159775774787361)
      ·
        refine ⟨8070951508619831831090521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10761268678159775774787361 8070951508619831831090521)
        ·
          refine ⟨6053213631464873873317891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8070951508619831831090521 6053213631464873873317891)
          ·
            refine ⟨9079820447197310809976837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6053213631464873873317891 9079820447197310809976837)
            ·
              refine ⟨1702466333849495776870657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9079820447197310809976837 1702466333849495776870657)
              ·
                refine ⟨1276849750387121832652993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1702466333849495776870657 1276849750387121832652993)
                ·
                  refine ⟨957637312790341374489745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1276849750387121832652993 957637312790341374489745)
                  ·
                    refine ⟨718227984592756030867309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 957637312790341374489745 718227984592756030867309)
                    ·
                      refine ⟨269335494222283511575241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 718227984592756030867309 269335494222283511575241)
                      ·
                        rfl

theorem cell23_524529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4, 2, 2, 2, 3].length) (baseStart_524529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_524529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_524529 prefixEnd_524529 := by exact prefixLift 524529
  have htrace : WordTrace (prefixWord ++ tailWord_524529) baseStart_524529 baseEnd_524529 := by
    simpa [prefixWord, tailWord_524529, baseEnd_524529] using wordTrace_append hprefix tailTrace_524529
  have hstable : (prefixWord ++ tailWord_524529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524529).length < 2 ^ (prefixWord ++ tailWord_524529).sum := by decide
  have hdescent : baseEnd_524529 < baseStart_524529 := by decide
  rcases family_descends (prefixWord ++ tailWord_524529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524572 : List Nat := [2, 2, 3, 1, 1, 1, 1, 1, 2, 4, 5]
def baseStart_524572 : Nat := 118140960795 + 524572 * 2 ^ 59
def prefixEnd_524572 : Nat := 4983230072969 + 3 ^ 40 * 524572 * 2
def baseEnd_524572 : Nat := 269357573890426843337543

theorem tailTrace_524572 : CollatzResearch.WordTrace tailWord_524572 prefixEnd_524572 269357573890426843337543 := by
  unfold tailWord_524572
  simp only [CollatzResearch.WordTrace]
  refine ⟨9566356327786354305051985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12755141770381805740069313 9566356327786354305051985)
  ·
    refine ⟨7174767245839765728788989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9566356327786354305051985 7174767245839765728788989)
    ·
      refine ⟨2690537717189912148295871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7174767245839765728788989 2690537717189912148295871)
      ·
        refine ⟨4035806575784868222443807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2690537717189912148295871 4035806575784868222443807)
        ·
          refine ⟨6053709863677302333665711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4035806575784868222443807 6053709863677302333665711)
          ·
            refine ⟨9080564795515953500498567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6053709863677302333665711 9080564795515953500498567)
            ·
              refine ⟨13620847193273930250747851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9080564795515953500498567 13620847193273930250747851)
              ·
                refine ⟨20431270789910895376121777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13620847193273930250747851 20431270789910895376121777)
                ·
                  refine ⟨15323453092433171532091333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20431270789910895376121777 15323453092433171532091333)
                  ·
                    refine ⟨2873147454831219662267125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15323453092433171532091333 2873147454831219662267125)
                    ·
                      refine ⟨269357573890426843337543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2873147454831219662267125 269357573890426843337543)
                      ·
                        rfl

theorem cell23_524572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 1, 2, 4, 5].length) (baseStart_524572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_524572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_524572 prefixEnd_524572 := by exact prefixLift 524572
  have htrace : WordTrace (prefixWord ++ tailWord_524572) baseStart_524572 baseEnd_524572 := by
    simpa [prefixWord, tailWord_524572, baseEnd_524572] using wordTrace_append hprefix tailTrace_524572
  have hstable : (prefixWord ++ tailWord_524572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524572).length < 2 ^ (prefixWord ++ tailWord_524572).sum := by decide
  have hdescent : baseEnd_524572 < baseStart_524572 := by decide
  rcases family_descends (prefixWord ++ tailWord_524572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524579 : List Nat := [1, 1, 1, 4, 2, 2, 3, 3, 1, 5]
def baseStart_524579 : Nat := 118140960795 + 524579 * 2 ^ 59
def prefixEnd_524579 : Nat := 4983230072969 + 3 ^ 40 * 524579 * 2
def baseEnd_524579 : Nat := 89787056085002771983337

theorem tailTrace_524579 : CollatzResearch.WordTrace tailWord_524579 prefixEnd_524579 89787056085002771983337 := by
  unfold tailWord_524579
  simp only [CollatzResearch.WordTrace]
  refine ⟨19132967966547348805608791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12755311977698232537072527 19132967966547348805608791)
  ·
    refine ⟨28699451949821023208413187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19132967966547348805608791 28699451949821023208413187)
    ·
      refine ⟨43049177924731534812619781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28699451949821023208413187 43049177924731534812619781)
      ·
        refine ⟨8071720860887162777366209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43049177924731534812619781 8071720860887162777366209)
        ·
          refine ⟨6053790645665372083024657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8071720860887162777366209 6053790645665372083024657)
          ·
            refine ⟨4540342984249029062268493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6053790645665372083024657 4540342984249029062268493)
            ·
              refine ⟨1702628619093385898350685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4540342984249029062268493 1702628619093385898350685)
              ·
                refine ⟨638485732160019711881507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1702628619093385898350685 638485732160019711881507)
                ·
                  refine ⟨957728598240029567822261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 638485732160019711881507 957728598240029567822261)
                  ·
                    refine ⟨89787056085002771983337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 957728598240029567822261 89787056085002771983337)
                    ·
                      rfl

theorem cell23_524579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3, 3, 1, 5].length) (baseStart_524579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_524579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_524579 prefixEnd_524579 := by exact prefixLift 524579
  have htrace : WordTrace (prefixWord ++ tailWord_524579) baseStart_524579 baseEnd_524579 := by
    simpa [prefixWord, tailWord_524579, baseEnd_524579] using wordTrace_append hprefix tailTrace_524579
  have hstable : (prefixWord ++ tailWord_524579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524579).length < 2 ^ (prefixWord ++ tailWord_524579).sum := by decide
  have hdescent : baseEnd_524579 < baseStart_524579 := by decide
  rcases family_descends (prefixWord ++ tailWord_524579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524583 : List Nat := [1, 1, 8, 1, 1, 1, 1, 1, 8]
def baseStart_524583 : Nat := 118140960795 + 524583 * 2 ^ 59
def prefixEnd_524583 : Nat := 4983230072969 + 3 ^ 40 * 524583 * 2
def baseEnd_524583 : Nat := 29929246908625144477777

theorem tailTrace_524583 : CollatzResearch.WordTrace tailWord_524583 prefixEnd_524583 29929246908625144477777 := by
  unfold tailWord_524583
  simp only [CollatzResearch.WordTrace]
  refine ⟨19133113858532857488754403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12755409239021904992502935 19133113858532857488754403)
  ·
    refine ⟨28699670787799286233131605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19133113858532857488754403 28699670787799286233131605)
    ·
      refine ⟨336324267044522885544511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 28699670787799286233131605 336324267044522885544511)
      ·
        refine ⟨504486400566784328316767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 336324267044522885544511 504486400566784328316767)
        ·
          refine ⟨756729600850176492475151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 504486400566784328316767 756729600850176492475151)
          ·
            refine ⟨1135094401275264738712727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 756729600850176492475151 1135094401275264738712727)
            ·
              refine ⟨1702641601912897108069091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1135094401275264738712727 1702641601912897108069091)
              ·
                refine ⟨2553962402869345662103637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1702641601912897108069091 2553962402869345662103637)
                ·
                  refine ⟨29929246908625144477777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2553962402869345662103637 29929246908625144477777)
                  ·
                    rfl

theorem cell23_524583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 1, 1, 8].length) (baseStart_524583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_524583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_524583 prefixEnd_524583 := by exact prefixLift 524583
  have htrace : WordTrace (prefixWord ++ tailWord_524583) baseStart_524583 baseEnd_524583 := by
    simpa [prefixWord, tailWord_524583, baseEnd_524583] using wordTrace_append hprefix tailTrace_524583
  have hstable : (prefixWord ++ tailWord_524583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524583).length < 2 ^ (prefixWord ++ tailWord_524583).sum := by decide
  have hdescent : baseEnd_524583 < baseStart_524583 := by decide
  rcases family_descends (prefixWord ++ tailWord_524583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524593 : List Nat := [1, 2, 2, 3, 4, 1, 2, 1, 3, 1, 3]
def baseStart_524593 : Nat := 118140960795 + 524593 * 2 ^ 59
def prefixEnd_524593 : Nat := 4983230072969 + 3 ^ 40 * 524593 * 2
def baseEnd_524593 : Nat := 269368356984171261174947

theorem tailTrace_524593 : CollatzResearch.WordTrace tailWord_524593 prefixEnd_524593 269368356984171261174947 := by
  unfold tailWord_524593
  simp only [CollatzResearch.WordTrace]
  refine ⟨19133478588496629196618433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12755652392331086131078955 19133478588496629196618433)
  ·
    refine ⟨14350108941372471897463825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19133478588496629196618433 14350108941372471897463825)
    ·
      refine ⟨10762581706029353923097869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14350108941372471897463825 10762581706029353923097869)
      ·
        refine ⟨4035968139761007721161701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10762581706029353923097869 4035968139761007721161701)
        ·
          refine ⟨756744026205188947717819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4035968139761007721161701 756744026205188947717819)
          ·
            refine ⟨1135116039307783421576729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 756744026205188947717819 1135116039307783421576729)
            ·
              refine ⟨851337029480837566182547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1135116039307783421576729 851337029480837566182547)
              ·
                refine ⟨1277005544221256349273821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 851337029480837566182547 1277005544221256349273821)
                ·
                  refine ⟨478877079082971130977683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1277005544221256349273821 478877079082971130977683)
                  ·
                    refine ⟨718315618624456696466525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 478877079082971130977683 718315618624456696466525)
                    ·
                      refine ⟨269368356984171261174947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 718315618624456696466525 269368356984171261174947)
                      ·
                        rfl

theorem cell23_524593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 2, 1, 3, 1, 3].length) (baseStart_524593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_524593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_524593 prefixEnd_524593 := by exact prefixLift 524593
  have htrace : WordTrace (prefixWord ++ tailWord_524593) baseStart_524593 baseEnd_524593 := by
    simpa [prefixWord, tailWord_524593, baseEnd_524593] using wordTrace_append hprefix tailTrace_524593
  have hstable : (prefixWord ++ tailWord_524593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524593).length < 2 ^ (prefixWord ++ tailWord_524593).sum := by decide
  have hdescent : baseEnd_524593 < baseStart_524593 := by decide
  rcases family_descends (prefixWord ++ tailWord_524593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524650 : List Nat := [3, 1, 3, 3, 1, 1, 3, 1, 3, 2, 2]
def baseStart_524650 : Nat := 118140960795 + 524650 * 2 ^ 59
def prefixEnd_524650 : Nat := 4983230072969 + 3 ^ 40 * 524650 * 2
def baseEnd_524650 : Nat := 269397625381477538162185

theorem tailTrace_524650 : CollatzResearch.WordTrace tailWord_524650 prefixEnd_524650 269397625381477538162185 := by
  unfold tailWord_524650
  simp only [CollatzResearch.WordTrace]
  refine ⟨4783889387322531982860851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12757038366193418620962269 4783889387322531982860851)
  ·
    refine ⟨7175834080983797974291277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4783889387322531982860851 7175834080983797974291277)
    ·
      refine ⟨2690937780368924240359229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7175834080983797974291277 2690937780368924240359229)
      ·
        refine ⟨1009101667638346590134711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2690937780368924240359229 1009101667638346590134711)
        ·
          refine ⟨1513652501457519885202067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1009101667638346590134711 1513652501457519885202067)
          ·
            refine ⟨2270478752186279827803101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1513652501457519885202067 2270478752186279827803101)
            ·
              refine ⟨851429532069854935426163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2270478752186279827803101 851429532069854935426163)
              ·
                refine ⟨1277144298104782403139245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 851429532069854935426163 1277144298104782403139245)
                ·
                  refine ⟨478929111789293401177217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1277144298104782403139245 478929111789293401177217)
                  ·
                    refine ⟨359196833841970050882913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 478929111789293401177217 359196833841970050882913)
                    ·
                      refine ⟨269397625381477538162185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 359196833841970050882913 269397625381477538162185)
                      ·
                        rfl

theorem cell23_524650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 3, 1, 3, 2, 2].length) (baseStart_524650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_524650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_524650 prefixEnd_524650 := by exact prefixLift 524650
  have htrace : WordTrace (prefixWord ++ tailWord_524650) baseStart_524650 baseEnd_524650 := by
    simpa [prefixWord, tailWord_524650, baseEnd_524650] using wordTrace_append hprefix tailTrace_524650
  have hstable : (prefixWord ++ tailWord_524650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524650).length < 2 ^ (prefixWord ++ tailWord_524650).sum := by decide
  have hdescent : baseEnd_524650 < baseStart_524650 := by decide
  rcases family_descends (prefixWord ++ tailWord_524650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524672 : List Nat := [2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 10]
def baseStart_524672 : Nat := 118140960795 + 524672 * 2 ^ 59
def prefixEnd_524672 : Nat := 4983230072969 + 3 ^ 40 * 524672 * 2
def baseEnd_524672 : Nat := 269408921955876452087083

theorem tailTrace_524672 : CollatzResearch.WordTrace tailWord_524672 prefixEnd_524672 269408921955876452087083 := by
  unfold tailWord_524672
  simp only [CollatzResearch.WordTrace]
  refine ⟨9568179977605212844372135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12757573303473617125829513 9568179977605212844372135)
  ·
    refine ⟨14352269966407819266558203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9568179977605212844372135 14352269966407819266558203)
    ·
      refine ⟨21528404949611728899837305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14352269966407819266558203 21528404949611728899837305)
      ·
        refine ⟨16146303712208796674877979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21528404949611728899837305 16146303712208796674877979)
        ·
          refine ⟨24219455568313195012316969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16146303712208796674877979 24219455568313195012316969)
          ·
            refine ⟨18164591676234896259237727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24219455568313195012316969 18164591676234896259237727)
            ·
              refine ⟨27246887514352344388856591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18164591676234896259237727 27246887514352344388856591)
              ·
                refine ⟨40870331271528516583284887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27246887514352344388856591 40870331271528516583284887)
                ·
                  refine ⟨61305496907292774874927331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40870331271528516583284887 61305496907292774874927331)
                  ·
                    refine ⟨91958245360939162312390997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 61305496907292774874927331 91958245360939162312390997)
                    ·
                      refine ⟨269408921955876452087083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 91958245360939162312390997 269408921955876452087083)
                      ·
                        rfl

theorem cell23_524672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 10].length) (baseStart_524672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_524672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_524672 prefixEnd_524672 := by exact prefixLift 524672
  have htrace : WordTrace (prefixWord ++ tailWord_524672) baseStart_524672 baseEnd_524672 := by
    simpa [prefixWord, tailWord_524672, baseEnd_524672] using wordTrace_append hprefix tailTrace_524672
  have hstable : (prefixWord ++ tailWord_524672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524672).length < 2 ^ (prefixWord ++ tailWord_524672).sum := by decide
  have hdescent : baseEnd_524672 < baseStart_524672 := by decide
  rcases family_descends (prefixWord ++ tailWord_524672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524694 : List Nat := [5, 3, 1, 2, 1, 1, 2, 2, 2, 4]
def baseStart_524694 : Nat := 118140960795 + 524694 * 2 ^ 59
def prefixEnd_524694 : Nat := 4983230072969 + 3 ^ 40 * 524694 * 2
def baseEnd_524694 : Nat := 89806739510091788670661

theorem tailTrace_524694 : CollatzResearch.WordTrace tailWord_524694 prefixEnd_524694 89806739510091788670661 := by
  unfold tailWord_524694
  simp only [CollatzResearch.WordTrace]
  refine ⟨1196072647570670215377821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12758108240753815630696757 1196072647570670215377821)
  ·
    refine ⟨448527242839001330766683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1196072647570670215377821 448527242839001330766683)
    ·
      refine ⟨672790864258501996150025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 448527242839001330766683 672790864258501996150025)
      ·
        refine ⟨504593148193876497112519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 672790864258501996150025 504593148193876497112519)
        ·
          refine ⟨756889722290814745668779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 504593148193876497112519 756889722290814745668779)
          ·
            refine ⟨1135334583436222118503169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 756889722290814745668779 1135334583436222118503169)
            ·
              refine ⟨851500937577166588877377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1135334583436222118503169 851500937577166588877377)
              ·
                refine ⟨638625703182874941658033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 851500937577166588877377 638625703182874941658033)
                ·
                  refine ⟨478969277387156206243525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 638625703182874941658033 478969277387156206243525)
                  ·
                    refine ⟨89806739510091788670661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 478969277387156206243525 89806739510091788670661)
                    ·
                      rfl

theorem cell23_524694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 2, 2, 2, 4].length) (baseStart_524694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_524694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_524694 prefixEnd_524694 := by exact prefixLift 524694
  have htrace : WordTrace (prefixWord ++ tailWord_524694) baseStart_524694 baseEnd_524694 := by
    simpa [prefixWord, tailWord_524694, baseEnd_524694] using wordTrace_append hprefix tailTrace_524694
  have hstable : (prefixWord ++ tailWord_524694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524694).length < 2 ^ (prefixWord ++ tailWord_524694).sum := by decide
  have hdescent : baseEnd_524694 < baseStart_524694 := by decide
  rcases family_descends (prefixWord ++ tailWord_524694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524701 : List Nat := [1, 4, 2, 1, 5, 1, 2, 2, 1, 2, 2]
def baseStart_524701 : Nat := 118140960795 + 524701 * 2 ^ 59
def prefixEnd_524701 : Nat := 4983230072969 + 3 ^ 40 * 524701 * 2
def baseEnd_524701 : Nat := 269423812894856838624451

theorem tailTrace_524701 : CollatzResearch.WordTrace tailWord_524701 prefixEnd_524701 269423812894856838624451 := by
  unfold tailWord_524701
  simp only [CollatzResearch.WordTrace]
  refine ⟨19137417672105363641549957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12758278448070242427699971 19137417672105363641549957)
  ·
    refine ⟨3588265813519755682790617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19137417672105363641549957 3588265813519755682790617)
    ·
      refine ⟨2691199360139816762092963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3588265813519755682790617 2691199360139816762092963)
      ·
        refine ⟨4036799040209725143139445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2691199360139816762092963 4036799040209725143139445)
        ·
          refine ⟨378449910019661732169323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4036799040209725143139445 378449910019661732169323)
          ·
            refine ⟨567674865029492598253985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 378449910019661732169323 567674865029492598253985)
            ·
              refine ⟨425756148772119448690489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 567674865029492598253985 425756148772119448690489)
              ·
                refine ⟨319317111579089586517867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 425756148772119448690489 319317111579089586517867)
                ·
                  refine ⟨478975667368634379776801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 319317111579089586517867 478975667368634379776801)
                  ·
                    refine ⟨359231750526475784832601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 478975667368634379776801 359231750526475784832601)
                    ·
                      refine ⟨269423812894856838624451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 359231750526475784832601 269423812894856838624451)
                      ·
                        rfl

theorem cell23_524701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 2, 2, 1, 2, 2].length) (baseStart_524701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_524701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_524701 prefixEnd_524701 := by exact prefixLift 524701
  have htrace : WordTrace (prefixWord ++ tailWord_524701) baseStart_524701 baseEnd_524701 := by
    simpa [prefixWord, tailWord_524701, baseEnd_524701] using wordTrace_append hprefix tailTrace_524701
  have hstable : (prefixWord ++ tailWord_524701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524701).length < 2 ^ (prefixWord ++ tailWord_524701).sum := by decide
  have hdescent : baseEnd_524701 < baseStart_524701 := by decide
  rcases family_descends (prefixWord ++ tailWord_524701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524709 : List Nat := [1, 3, 1, 2, 1, 1, 3, 1, 1, 6, 3]
def baseStart_524709 : Nat := 118140960795 + 524709 * 2 ^ 59
def prefixEnd_524709 : Nat := 4983230072969 + 3 ^ 40 * 524709 * 2
def baseEnd_524709 : Nat := 269427920740092807324413

theorem tailTrace_524709 : CollatzResearch.WordTrace tailWord_524709 prefixEnd_524709 269427920740092807324413 := by
  unfold tailWord_524709
  simp only [CollatzResearch.WordTrace]
  refine ⟨19137709456076381007841181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12758472970717587338560787 19137709456076381007841181)
  ·
    refine ⟨7176641046028642877940443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19137709456076381007841181 7176641046028642877940443)
    ·
      refine ⟨10764961569042964316910665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7176641046028642877940443 10764961569042964316910665)
      ·
        refine ⟨8073721176782223237682999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10764961569042964316910665 8073721176782223237682999)
        ·
          refine ⟨12110581765173334856524499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8073721176782223237682999 12110581765173334856524499)
          ·
            refine ⟨18165872647760002284786749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12110581765173334856524499 18165872647760002284786749)
            ·
              refine ⟨6812202242910000856795031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18165872647760002284786749 6812202242910000856795031)
              ·
                refine ⟨10218303364365001285192547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6812202242910000856795031 10218303364365001285192547)
                ·
                  refine ⟨15327455046547501927788821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10218303364365001285192547 15327455046547501927788821)
                  ·
                    refine ⟨718474455306914152865101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15327455046547501927788821 718474455306914152865101)
                    ·
                      refine ⟨269427920740092807324413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 718474455306914152865101 269427920740092807324413)
                      ·
                        rfl

theorem cell23_524709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 1, 1, 6, 3].length) (baseStart_524709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_524709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_524709 prefixEnd_524709 := by exact prefixLift 524709
  have htrace : WordTrace (prefixWord ++ tailWord_524709) baseStart_524709 baseEnd_524709 := by
    simpa [prefixWord, tailWord_524709, baseEnd_524709] using wordTrace_append hprefix tailTrace_524709
  have hstable : (prefixWord ++ tailWord_524709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524709).length < 2 ^ (prefixWord ++ tailWord_524709).sum := by decide
  have hdescent : baseEnd_524709 < baseStart_524709 := by decide
  rcases family_descends (prefixWord ++ tailWord_524709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524729 : List Nat := [1, 2, 1, 4, 3, 1, 1, 1, 9]
def baseStart_524729 : Nat := 118140960795 + 524729 * 2 ^ 59
def prefixEnd_524729 : Nat := 4983230072969 + 3 ^ 40 * 524729 * 2
def baseEnd_524729 : Nat := 29937576705909192119369

theorem tailTrace_524729 : CollatzResearch.WordTrace tailWord_524729 prefixEnd_524729 29937576705909192119369 := by
  unfold tailWord_524729
  simp only [CollatzResearch.WordTrace]
  refine ⟨19138438916003924423569241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12758959277335949615712827 19138438916003924423569241)
  ·
    refine ⟨14353829187002943317676931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19138438916003924423569241 14353829187002943317676931)
    ·
      refine ⟨21530743780504414976515397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14353829187002943317676931 21530743780504414976515397)
      ·
        refine ⟨4037014458844577808096637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21530743780504414976515397 4037014458844577808096637)
        ·
          refine ⟨1513880422066716678036239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4037014458844577808096637 1513880422066716678036239)
          ·
            refine ⟨2270820633100075017054359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1513880422066716678036239 2270820633100075017054359)
            ·
              refine ⟨3406230949650112525581539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2270820633100075017054359 3406230949650112525581539)
              ·
                refine ⟨5109346424475168788372309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3406230949650112525581539 5109346424475168788372309)
                ·
                  refine ⟨29937576705909192119369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 5109346424475168788372309 29937576705909192119369)
                  ·
                    rfl

theorem cell23_524729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 1, 9].length) (baseStart_524729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_524729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_524729 prefixEnd_524729 := by exact prefixLift 524729
  have htrace : WordTrace (prefixWord ++ tailWord_524729) baseStart_524729 baseEnd_524729 := by
    simpa [prefixWord, tailWord_524729, baseEnd_524729] using wordTrace_append hprefix tailTrace_524729
  have hstable : (prefixWord ++ tailWord_524729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524729).length < 2 ^ (prefixWord ++ tailWord_524729).sum := by decide
  have hdescent : baseEnd_524729 < baseStart_524729 := by decide
  rcases family_descends (prefixWord ++ tailWord_524729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524739 : List Nat := [1, 1, 1, 3, 1, 1, 3, 1, 3, 5, 3]
def baseStart_524739 : Nat := 118140960795 + 524739 * 2 ^ 59
def prefixEnd_524739 : Nat := 4983230072969 + 3 ^ 40 * 524739 * 2
def baseEnd_524739 : Nat := 269443325159727689949275

theorem tailTrace_524739 : CollatzResearch.WordTrace tailWord_524739 prefixEnd_524739 269443325159727689949275 := by
  unfold tailWord_524739
  simp only [CollatzResearch.WordTrace]
  refine ⟨19138803645967696131433271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12759202430645130754288847 19138803645967696131433271)
  ·
    refine ⟨28708205468951544197149907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19138803645967696131433271 28708205468951544197149907)
    ·
      refine ⟨43062308203427316295724861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28708205468951544197149907 43062308203427316295724861)
      ·
        refine ⟨16148365576285243610896823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43062308203427316295724861 16148365576285243610896823)
        ·
          refine ⟨24222548364427865416345235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16148365576285243610896823 24222548364427865416345235)
          ·
            refine ⟨36333822546641798124517853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24222548364427865416345235 36333822546641798124517853)
            ·
              refine ⟨13625183454990674296694195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36333822546641798124517853 13625183454990674296694195)
              ·
                refine ⟨20437775182486011445041293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13625183454990674296694195 20437775182486011445041293)
                ·
                  refine ⟨7664165693432254291890485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20437775182486011445041293 7664165693432254291890485)
                  ·
                    refine ⟨718515533759273839864733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7664165693432254291890485 718515533759273839864733)
                    ·
                      refine ⟨269443325159727689949275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 718515533759273839864733 269443325159727689949275)
                      ·
                        rfl

theorem cell23_524739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 1, 3, 5, 3].length) (baseStart_524739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_524739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_524739 prefixEnd_524739 := by exact prefixLift 524739
  have htrace : WordTrace (prefixWord ++ tailWord_524739) baseStart_524739 baseEnd_524739 := by
    simpa [prefixWord, tailWord_524739, baseEnd_524739] using wordTrace_append hprefix tailTrace_524739
  have hstable : (prefixWord ++ tailWord_524739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524739).length < 2 ^ (prefixWord ++ tailWord_524739).sum := by decide
  have hdescent : baseEnd_524739 < baseStart_524739 := by decide
  rcases family_descends (prefixWord ++ tailWord_524739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524757 : List Nat := [1, 3, 2, 3, 1, 4, 1, 2, 2, 2, 2]
def baseStart_524757 : Nat := 118140960795 + 524757 * 2 ^ 59
def prefixEnd_524757 : Nat := 4983230072969 + 3 ^ 40 * 524757 * 2
def baseEnd_524757 : Nat := 269452567811508619524193

theorem tailTrace_524757 : CollatzResearch.WordTrace tailWord_524757 prefixEnd_524757 269452567811508619524193 := by
  unfold tailWord_524757
  simp only [CollatzResearch.WordTrace]
  refine ⟨19139460159902485205588525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12759640106601656803725683 19139460159902485205588525)
  ·
    refine ⟨7177297559963431952095697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19139460159902485205588525 7177297559963431952095697)
    ·
      refine ⟨5382973169972573964071773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7177297559963431952095697 5382973169972573964071773)
      ·
        refine ⟨2018614938739715236526915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5382973169972573964071773 2018614938739715236526915)
        ·
          refine ⟨3027922408109572854790373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2018614938739715236526915 3027922408109572854790373)
          ·
            refine ⟨567735451520544910273195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3027922408109572854790373 567735451520544910273195)
            ·
              refine ⟨851603177280817365409793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 567735451520544910273195 851603177280817365409793)
              ·
                refine ⟨638702382960613024057345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 851603177280817365409793 638702382960613024057345)
                ·
                  refine ⟨479026787220459768043009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 638702382960613024057345 479026787220459768043009)
                  ·
                    refine ⟨359270090415344826032257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 479026787220459768043009 359270090415344826032257)
                    ·
                      refine ⟨269452567811508619524193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 359270090415344826032257 269452567811508619524193)
                      ·
                        rfl

theorem cell23_524757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 1, 2, 2, 2, 2].length) (baseStart_524757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_524757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_524757 prefixEnd_524757 := by exact prefixLift 524757
  have htrace : WordTrace (prefixWord ++ tailWord_524757) baseStart_524757 baseEnd_524757 := by
    simpa [prefixWord, tailWord_524757, baseEnd_524757] using wordTrace_append hprefix tailTrace_524757
  have hstable : (prefixWord ++ tailWord_524757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524757).length < 2 ^ (prefixWord ++ tailWord_524757).sum := by decide
  have hdescent : baseEnd_524757 < baseStart_524757 := by decide
  rcases family_descends (prefixWord ++ tailWord_524757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524769 : List Nat := [1, 2, 3, 1, 2, 2, 2, 1, 1, 1, 7]
def baseStart_524769 : Nat := 118140960795 + 524769 * 2 ^ 59
def prefixEnd_524769 : Nat := 4983230072969 + 3 ^ 40 * 524769 * 2
def baseEnd_524769 : Nat := 269458729579362572574137

theorem tailTrace_524769 : CollatzResearch.WordTrace tailWord_524769 prefixEnd_524769 269458729579362572574137 := by
  unfold tailWord_524769
  simp only [CollatzResearch.WordTrace]
  refine ⟨19139897835859011255025361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12759931890572674170016907 19139897835859011255025361)
  ·
    refine ⟨14354923376894258441269021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19139897835859011255025361 14354923376894258441269021)
    ·
      refine ⟨5383096266335346915475883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14354923376894258441269021 5383096266335346915475883)
      ·
        refine ⟨8074644399503020373213825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5383096266335346915475883 8074644399503020373213825)
        ·
          refine ⟨6055983299627265279910369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8074644399503020373213825 6055983299627265279910369)
          ·
            refine ⟨4541987474720448959932777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6055983299627265279910369 4541987474720448959932777)
            ·
              refine ⟨3406490606040336719949583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4541987474720448959932777 3406490606040336719949583)
              ·
                refine ⟨5109735909060505079924375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3406490606040336719949583 5109735909060505079924375)
                ·
                  refine ⟨7664603863590757619886563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5109735909060505079924375 7664603863590757619886563)
                  ·
                    refine ⟨11496905795386136429829845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7664603863590757619886563 11496905795386136429829845)
                    ·
                      refine ⟨269458729579362572574137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 11496905795386136429829845 269458729579362572574137)
                      ·
                        rfl

theorem cell23_524769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 1, 1, 1, 7].length) (baseStart_524769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_524769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_524769 prefixEnd_524769 := by exact prefixLift 524769
  have htrace : WordTrace (prefixWord ++ tailWord_524769) baseStart_524769 baseEnd_524769 := by
    simpa [prefixWord, tailWord_524769, baseEnd_524769] using wordTrace_append hprefix tailTrace_524769
  have hstable : (prefixWord ++ tailWord_524769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524769).length < 2 ^ (prefixWord ++ tailWord_524769).sum := by decide
  have hdescent : baseEnd_524769 < baseStart_524769 := by decide
  rcases family_descends (prefixWord ++ tailWord_524769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524779 : List Nat := [1, 1, 1, 1, 2, 3, 3, 1, 3, 3, 4]
def baseStart_524779 : Nat := 118140960795 + 524779 * 2 ^ 59
def prefixEnd_524779 : Nat := 4983230072969 + 3 ^ 40 * 524779 * 2
def baseEnd_524779 : Nat := 269463864385907533449091

theorem tailTrace_524779 : CollatzResearch.WordTrace tailWord_524779 prefixEnd_524779 269463864385907533449091 := by
  unfold tailWord_524779
  simp only [CollatzResearch.WordTrace]
  refine ⟨19140262565822782962889391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12760175043881855308592927 19140262565822782962889391)
  ·
    refine ⟨28710393848734174444334087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19140262565822782962889391 28710393848734174444334087)
    ·
      refine ⟨43065590773101261666501131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28710393848734174444334087 43065590773101261666501131)
      ·
        refine ⟨64598386159651892499751697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43065590773101261666501131 64598386159651892499751697)
        ·
          refine ⟨48448789619738919374813773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64598386159651892499751697 48448789619738919374813773)
          ·
            refine ⟨18168296107402094765555165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48448789619738919374813773 18168296107402094765555165)
            ·
              refine ⟨6813111040275785537083187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18168296107402094765555165 6813111040275785537083187)
              ·
                refine ⟨10219666560413678305624781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6813111040275785537083187 10219666560413678305624781)
                ·
                  refine ⟨3832374960155129364609293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10219666560413678305624781 3832374960155129364609293)
                  ·
                    refine ⟨1437140610058173511728485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3832374960155129364609293 1437140610058173511728485)
                    ·
                      refine ⟨269463864385907533449091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1437140610058173511728485 269463864385907533449091)
                      ·
                        rfl

theorem cell23_524779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 1, 3, 3, 4].length) (baseStart_524779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_524779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_524779 prefixEnd_524779 := by exact prefixLift 524779
  have htrace : WordTrace (prefixWord ++ tailWord_524779) baseStart_524779 baseEnd_524779 := by
    simpa [prefixWord, tailWord_524779, baseEnd_524779] using wordTrace_append hprefix tailTrace_524779
  have hstable : (prefixWord ++ tailWord_524779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524779).length < 2 ^ (prefixWord ++ tailWord_524779).sum := by decide
  have hdescent : baseEnd_524779 < baseStart_524779 := by decide
  rcases family_descends (prefixWord ++ tailWord_524779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524796 : List Nat := [2, 2, 2, 1, 2, 1, 1, 5, 2, 1, 4]
def baseStart_524796 : Nat := 118140960795 + 524796 * 2 ^ 59
def prefixEnd_524796 : Nat := 4983230072969 + 3 ^ 40 * 524796 * 2
def baseEnd_524796 : Nat := 269472593557033966936513

theorem tailTrace_524796 : CollatzResearch.WordTrace tailWord_524796 prefixEnd_524796 269472593557033966936513 := by
  unfold tailWord_524796
  simp only [CollatzResearch.WordTrace]
  refine ⟨9570441303380597433129121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12760588404507463244172161 9570441303380597433129121)
  ·
    refine ⟨7177830977535448074846841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9570441303380597433129121 7177830977535448074846841)
    ·
      refine ⟨5383373233151586056135131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7177830977535448074846841 5383373233151586056135131)
      ·
        refine ⟨8075059849727379084202697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5383373233151586056135131 8075059849727379084202697)
        ·
          refine ⟨6056294887295534313152023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8075059849727379084202697 6056294887295534313152023)
          ·
            refine ⟨9084442330943301469728035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6056294887295534313152023 9084442330943301469728035)
            ·
              refine ⟨13626663496414952204592053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9084442330943301469728035 13626663496414952204592053)
              ·
                refine ⟨1277499702788901769180505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13626663496414952204592053 1277499702788901769180505)
                ·
                  refine ⟨958124777091676326885379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1277499702788901769180505 958124777091676326885379)
                  ·
                    refine ⟨1437187165637514490328069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 958124777091676326885379 1437187165637514490328069)
                    ·
                      refine ⟨269472593557033966936513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1437187165637514490328069 269472593557033966936513)
                      ·
                        rfl

theorem cell23_524796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 5, 2, 1, 4].length) (baseStart_524796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_524796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_524796 prefixEnd_524796 := by exact prefixLift 524796
  have htrace : WordTrace (prefixWord ++ tailWord_524796) baseStart_524796 baseEnd_524796 := by
    simpa [prefixWord, tailWord_524796, baseEnd_524796] using wordTrace_append hprefix tailTrace_524796
  have hstable : (prefixWord ++ tailWord_524796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524796).length < 2 ^ (prefixWord ++ tailWord_524796).sum := by decide
  have hdescent : baseEnd_524796 < baseStart_524796 := by decide
  rcases family_descends (prefixWord ++ tailWord_524796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524809 : List Nat := [1, 2, 1, 1, 3, 1, 2, 3, 2, 1, 6]
def baseStart_524809 : Nat := 118140960795 + 524809 * 2 ^ 59
def prefixEnd_524809 : Nat := 4983230072969 + 3 ^ 40 * 524809 * 2
def baseEnd_524809 : Nat := 269479268805542416073953

theorem tailTrace_524809 : CollatzResearch.WordTrace tailWord_524809 prefixEnd_524809 269479268805542416073953 := by
  unfold tailWord_524809
  simp only [CollatzResearch.WordTrace]
  refine ⟨19141356755714098086481481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12760904503809398724320987 19141356755714098086481481)
  ·
    refine ⟨14356017566785573564861111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19141356755714098086481481 14356017566785573564861111)
    ·
      refine ⟨21534026350178360347291667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14356017566785573564861111 21534026350178360347291667)
      ·
        refine ⟨32301039525267540520937501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21534026350178360347291667 32301039525267540520937501)
        ·
          refine ⟨12112889821975327695351563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32301039525267540520937501 12112889821975327695351563)
          ·
            refine ⟨18169334732962991543027345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12112889821975327695351563 18169334732962991543027345)
            ·
              refine ⟨13627001049722243657270509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18169334732962991543027345 13627001049722243657270509)
              ·
                refine ⟨5110125393645841371476441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13627001049722243657270509 5110125393645841371476441)
                ·
                  refine ⟨3832594045234381028607331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5110125393645841371476441 3832594045234381028607331)
                  ·
                    refine ⟨5748891067851571542910997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3832594045234381028607331 5748891067851571542910997)
                    ·
                      refine ⟨269479268805542416073953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 5748891067851571542910997 269479268805542416073953)
                      ·
                        rfl

theorem cell23_524809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 3, 2, 1, 6].length) (baseStart_524809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_524809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_524809 prefixEnd_524809 := by exact prefixLift 524809
  have htrace : WordTrace (prefixWord ++ tailWord_524809) baseStart_524809 baseEnd_524809 := by
    simpa [prefixWord, tailWord_524809, baseEnd_524809] using wordTrace_append hprefix tailTrace_524809
  have hstable : (prefixWord ++ tailWord_524809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524809).length < 2 ^ (prefixWord ++ tailWord_524809).sum := by decide
  have hdescent : baseEnd_524809 < baseStart_524809 := by decide
  rcases family_descends (prefixWord ++ tailWord_524809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524819 : List Nat := [1, 1, 1, 2, 1, 5, 1, 3, 8]
def baseStart_524819 : Nat := 118140960795 + 524819 * 2 ^ 59
def prefixEnd_524819 : Nat := 4983230072969 + 3 ^ 40 * 524819 * 2
def baseEnd_524819 : Nat := 29942711512454152994323

theorem tailTrace_524819 : CollatzResearch.WordTrace tailWord_524819 prefixEnd_524819 29942711512454152994323 := by
  unfold tailWord_524819
  simp only [CollatzResearch.WordTrace]
  refine ⟨19141721485677869794345511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12761147657118579862897007 19141721485677869794345511)
  ·
    refine ⟨28712582228516804691518267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19141721485677869794345511 28712582228516804691518267)
    ·
      refine ⟨43068873342775207037277401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28712582228516804691518267 43068873342775207037277401)
      ·
        refine ⟨32301655007081405277958051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43068873342775207037277401 32301655007081405277958051)
        ·
          refine ⟨48452482510622107916937077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32301655007081405277958051 48452482510622107916937077)
          ·
            refine ⟨4542420235370822617212851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 48452482510622107916937077 4542420235370822617212851)
            ·
              refine ⟨6813630353056233925819277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4542420235370822617212851 6813630353056233925819277)
              ·
                refine ⟨2555111382396087722182229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6813630353056233925819277 2555111382396087722182229)
                ·
                  refine ⟨29942711512454152994323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2555111382396087722182229 29942711512454152994323)
                  ·
                    rfl

theorem cell23_524819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 3, 8].length) (baseStart_524819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_524819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_524819 prefixEnd_524819 := by exact prefixLift 524819
  have htrace : WordTrace (prefixWord ++ tailWord_524819) baseStart_524819 baseEnd_524819 := by
    simpa [prefixWord, tailWord_524819, baseEnd_524819] using wordTrace_append hprefix tailTrace_524819
  have hstable : (prefixWord ++ tailWord_524819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524819).length < 2 ^ (prefixWord ++ tailWord_524819).sum := by decide
  have hdescent : baseEnd_524819 < baseStart_524819 := by decide
  rcases family_descends (prefixWord ++ tailWord_524819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524870 : List Nat := [6, 1, 1, 1, 2, 1, 1, 4, 6]
def baseStart_524870 : Nat := 118140960795 + 524870 * 2 ^ 59
def prefixEnd_524870 : Nat := 4983230072969 + 3 ^ 40 * 524870 * 2
def baseEnd_524870 : Nat := 29945621236162964156797

theorem tailTrace_524870 : CollatzResearch.WordTrace tailWord_524870 prefixEnd_524870 29945621236162964156797 := by
  unfold tailWord_524870
  simp only [CollatzResearch.WordTrace]
  refine ⟨598236925265409547014127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 12762387738995403669634709 598236925265409547014127)
  ·
    refine ⟨897355387898114320521191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 598236925265409547014127 897355387898114320521191)
    ·
      refine ⟨1346033081847171480781787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 897355387898114320521191 1346033081847171480781787)
      ·
        refine ⟨2019049622770757221172681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1346033081847171480781787 2019049622770757221172681)
        ·
          refine ⟨1514287217078067915879511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2019049622770757221172681 1514287217078067915879511)
          ·
            refine ⟨2271430825617101873819267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1514287217078067915879511 2271430825617101873819267)
            ·
              refine ⟨3407146238425652810728901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2271430825617101873819267 3407146238425652810728901)
              ·
                refine ⟨638839919704809902011669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3407146238425652810728901 638839919704809902011669)
                ·
                  refine ⟨29945621236162964156797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 638839919704809902011669 29945621236162964156797)
                  ·
                    rfl

theorem cell23_524870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 4, 6].length) (baseStart_524870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_524870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_524870 prefixEnd_524870 := by exact prefixLift 524870
  have htrace : WordTrace (prefixWord ++ tailWord_524870) baseStart_524870 baseEnd_524870 := by
    simpa [prefixWord, tailWord_524870, baseEnd_524870] using wordTrace_append hprefix tailTrace_524870
  have hstable : (prefixWord ++ tailWord_524870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524870).length < 2 ^ (prefixWord ++ tailWord_524870).sum := by decide
  have hdescent : baseEnd_524870 < baseStart_524870 := by decide
  rcases family_descends (prefixWord ++ tailWord_524870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524896 : List Nat := [2, 1, 1, 3, 2, 1, 3, 3, 1, 6]
def baseStart_524896 : Nat := 118140960795 + 524896 * 2 ^ 59
def prefixEnd_524896 : Nat := 4983230072969 + 3 ^ 40 * 524896 * 2
def baseEnd_524896 : Nat := 89841313874161191895351

theorem tailTrace_524896 : CollatzResearch.WordTrace tailWord_524896 prefixEnd_524896 89841313874161191895351 := by
  unfold tailWord_524896
  simp only [CollatzResearch.WordTrace]
  refine ⟨9572264953199455972449271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12763019937599274629932361 9572264953199455972449271)
  ·
    refine ⟨14358397429799183958673907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9572264953199455972449271 14358397429799183958673907)
    ·
      refine ⟨21537596144698775938010861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14358397429799183958673907 21537596144698775938010861)
      ·
        refine ⟨8076598554262040976754073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21537596144698775938010861 8076598554262040976754073)
        ·
          refine ⟨6057448915696530732565555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8076598554262040976754073 6057448915696530732565555)
          ·
            refine ⟨9086173373544796098848333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6057448915696530732565555 9086173373544796098848333)
            ·
              refine ⟨3407315015079298537068125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9086173373544796098848333 3407315015079298537068125)
              ·
                refine ⟨1277743130654736951400547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3407315015079298537068125 1277743130654736951400547)
                ·
                  refine ⟨1916614695982105427100821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1277743130654736951400547 1916614695982105427100821)
                  ·
                    refine ⟨89841313874161191895351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1916614695982105427100821 89841313874161191895351)
                    ·
                      rfl

theorem cell23_524896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 3, 1, 6].length) (baseStart_524896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_524896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_524896 prefixEnd_524896 := by exact prefixLift 524896
  have htrace : WordTrace (prefixWord ++ tailWord_524896) baseStart_524896 baseEnd_524896 := by
    simpa [prefixWord, tailWord_524896, baseEnd_524896] using wordTrace_append hprefix tailTrace_524896
  have hstable : (prefixWord ++ tailWord_524896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524896).length < 2 ^ (prefixWord ++ tailWord_524896).sum := by decide
  have hdescent : baseEnd_524896 < baseStart_524896 := by decide
  rcases family_descends (prefixWord ++ tailWord_524896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524903 : List Nat := [1, 1, 5, 1, 1, 1, 1, 6, 1, 1, 4]
def baseStart_524903 : Nat := 118140960795 + 524903 * 2 ^ 59
def prefixEnd_524903 : Nat := 4983230072969 + 3 ^ 40 * 524903 * 2
def baseEnd_524903 : Nat := 269527535987065048298521

theorem tailTrace_524903 : CollatzResearch.WordTrace tailWord_524903 prefixEnd_524903 269527535987065048298521 := by
  unfold tailWord_524903
  simp only [CollatzResearch.WordTrace]
  refine ⟨19144785217373552140403363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12763190144915701426935575 19144785217373552140403363)
  ·
    refine ⟨28717177826060328210605045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19144785217373552140403363 28717177826060328210605045)
    ·
      refine ⟨2692235421193155769744223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 28717177826060328210605045 2692235421193155769744223)
      ·
        refine ⟨4038353131789733654616335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2692235421193155769744223 4038353131789733654616335)
        ·
          refine ⟨6057529697684600481924503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4038353131789733654616335 6057529697684600481924503)
          ·
            refine ⟨9086294546526900722886755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6057529697684600481924503 9086294546526900722886755)
            ·
              refine ⟨13629441819790351084330133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9086294546526900722886755 13629441819790351084330133)
              ·
                refine ⟨638880085302672707077975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 13629441819790351084330133 638880085302672707077975)
                ·
                  refine ⟨958320127954009060616963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 638880085302672707077975 958320127954009060616963)
                  ·
                    refine ⟨1437480191931013590925445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 958320127954009060616963 1437480191931013590925445)
                    ·
                      refine ⟨269527535987065048298521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1437480191931013590925445 269527535987065048298521)
                      ·
                        rfl

theorem cell23_524903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 6, 1, 1, 4].length) (baseStart_524903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_524903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_524903 prefixEnd_524903 := by exact prefixLift 524903
  have htrace : WordTrace (prefixWord ++ tailWord_524903) baseStart_524903 baseEnd_524903 := by
    simpa [prefixWord, tailWord_524903, baseEnd_524903] using wordTrace_append hprefix tailTrace_524903
  have hstable : (prefixWord ++ tailWord_524903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524903).length < 2 ^ (prefixWord ++ tailWord_524903).sum := by decide
  have hdescent : baseEnd_524903 < baseStart_524903 := by decide
  rcases family_descends (prefixWord ++ tailWord_524903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524914 : List Nat := [3, 2, 1, 2, 4, 1, 2, 3, 1, 1, 3]
def baseStart_524914 : Nat := 118140960795 + 524914 * 2 ^ 59
def prefixEnd_524914 : Nat := 4983230072969 + 3 ^ 40 * 524914 * 2
def baseEnd_524914 : Nat := 269533184274264505260971

theorem tailTrace_524914 : CollatzResearch.WordTrace tailWord_524914 prefixEnd_524914 269533184274264505260971 := by
  unfold tailWord_524914
  simp only [CollatzResearch.WordTrace]
  refine ⟨4786296605083425254763449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12763457613555800679369197 4786296605083425254763449)
  ·
    refine ⟨3589722453812568941072587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4786296605083425254763449 3589722453812568941072587)
    ·
      refine ⟨5384583680718853411608881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3589722453812568941072587 5384583680718853411608881)
      ·
        refine ⟨4038437760539140058706661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5384583680718853411608881 4038437760539140058706661)
        ·
          refine ⟨757207080101088761007499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4038437760539140058706661 757207080101088761007499)
          ·
            refine ⟨1135810620151633141511249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 757207080101088761007499 1135810620151633141511249)
            ·
              refine ⟨851857965113724856133437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1135810620151633141511249 851857965113724856133437)
              ·
                refine ⟨319446736917646821050039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 851857965113724856133437 319446736917646821050039)
                ·
                  refine ⟨479170105376470231575059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 319446736917646821050039 479170105376470231575059)
                  ·
                    refine ⟨718755158064705347362589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 479170105376470231575059 718755158064705347362589)
                    ·
                      refine ⟨269533184274264505260971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 718755158064705347362589 269533184274264505260971)
                      ·
                        rfl

theorem cell23_524914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 2, 3, 1, 1, 3].length) (baseStart_524914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_524914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_524914 prefixEnd_524914 := by exact prefixLift 524914
  have htrace : WordTrace (prefixWord ++ tailWord_524914) baseStart_524914 baseEnd_524914 := by
    simpa [prefixWord, tailWord_524914, baseEnd_524914] using wordTrace_append hprefix tailTrace_524914
  have hstable : (prefixWord ++ tailWord_524914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524914).length < 2 ^ (prefixWord ++ tailWord_524914).sum := by decide
  have hdescent : baseEnd_524914 < baseStart_524914 := by decide
  rcases family_descends (prefixWord ++ tailWord_524914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524960 : List Nat := [2, 1, 1, 4, 4, 2, 2, 7]
def baseStart_524960 : Nat := 118140960795 + 524960 * 2 ^ 59
def prefixEnd_524960 : Nat := 4983230072969 + 3 ^ 40 * 524960 * 2
def baseEnd_524960 : Nat := 9983585347569308343917

theorem tailTrace_524960 : CollatzResearch.WordTrace tailWord_524960 prefixEnd_524960 9983585347569308343917 := by
  unfold tailWord_524960
  simp only [CollatzResearch.WordTrace]
  refine ⟨9573432089083525437614167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12764576118778033916818889 9573432089083525437614167)
  ·
    refine ⟨14360148133625288156421251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9573432089083525437614167 14360148133625288156421251)
    ·
      refine ⟨21540222200437932234631877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14360148133625288156421251 21540222200437932234631877)
      ·
        refine ⟨4038791662582112293993477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21540222200437932234631877 4038791662582112293993477)
        ·
          refine ⟨757273436734146055123777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4038791662582112293993477 757273436734146055123777)
          ·
            refine ⟨567955077550609541342833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 757273436734146055123777 567955077550609541342833)
            ·
              refine ⟨425966308162957156007125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 567955077550609541342833 425966308162957156007125)
              ·
                refine ⟨9983585347569308343917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 425966308162957156007125 9983585347569308343917)
                ·
                  rfl

theorem cell23_524960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 2, 7].length) (baseStart_524960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_524960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_524960 prefixEnd_524960 := by exact prefixLift 524960
  have htrace : WordTrace (prefixWord ++ tailWord_524960) baseStart_524960 baseEnd_524960 := by
    simpa [prefixWord, tailWord_524960, baseEnd_524960] using wordTrace_append hprefix tailTrace_524960
  have hstable : (prefixWord ++ tailWord_524960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524960).length < 2 ^ (prefixWord ++ tailWord_524960).sum := by decide
  have hdescent : baseEnd_524960 < baseStart_524960 := by decide
  rcases family_descends (prefixWord ++ tailWord_524960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524976 : List Nat := [2, 1, 1, 1, 2, 1, 3, 2, 1, 5, 4]
def baseStart_524976 : Nat := 118140960795 + 524976 * 2 ^ 59
def prefixEnd_524976 : Nat := 4983230072969 + 3 ^ 40 * 524976 * 2
def baseEnd_524976 : Nat := 269565020074843262685685

theorem tailTrace_524976 : CollatzResearch.WordTrace tailWord_524976 prefixEnd_524976 269565020074843262685685 := by
  unfold tailWord_524976
  simp only [CollatzResearch.WordTrace]
  refine ⟨9573723873054542803905391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12764965164072723738540521 9573723873054542803905391)
  ·
    refine ⟨14360585809581814205858087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9573723873054542803905391 14360585809581814205858087)
    ·
      refine ⟨21540878714372721308787131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14360585809581814205858087 21540878714372721308787131)
      ·
        refine ⟨32311318071559081963180697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21540878714372721308787131 32311318071559081963180697)
        ·
          refine ⟨24233488553669311472385523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32311318071559081963180697 24233488553669311472385523)
          ·
            refine ⟨36350232830503967208578285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24233488553669311472385523 36350232830503967208578285)
            ·
              refine ⟨13631337311438987703216857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36350232830503967208578285 13631337311438987703216857)
              ·
                refine ⟨10223502983579240777412643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13631337311438987703216857 10223502983579240777412643)
                ·
                  refine ⟨15335254475368861166118965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10223502983579240777412643 15335254475368861166118965)
                  ·
                    refine ⟨1437680107065830734323653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15335254475368861166118965 1437680107065830734323653)
                    ·
                      refine ⟨269565020074843262685685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1437680107065830734323653 269565020074843262685685)
                      ·
                        rfl

theorem cell23_524976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 2, 1, 5, 4].length) (baseStart_524976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_524976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_524976 prefixEnd_524976 := by exact prefixLift 524976
  have htrace : WordTrace (prefixWord ++ tailWord_524976) baseStart_524976 baseEnd_524976 := by
    simpa [prefixWord, tailWord_524976, baseEnd_524976] using wordTrace_append hprefix tailTrace_524976
  have hstable : (prefixWord ++ tailWord_524976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524976).length < 2 ^ (prefixWord ++ tailWord_524976).sum := by decide
  have hdescent : baseEnd_524976 < baseStart_524976 := by decide
  rcases family_descends (prefixWord ++ tailWord_524976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524998 : List Nat := [6, 1, 2, 1, 2, 2, 2, 1, 2, 4]
def baseStart_524998 : Nat := 118140960795 + 524998 * 2 ^ 59
def prefixEnd_524998 : Nat := 4983230072969 + 3 ^ 40 * 524998 * 2
def baseEnd_524998 : Nat := 89858772216414058870195

theorem tailTrace_524998 : CollatzResearch.WordTrace tailWord_524998 prefixEnd_524998 89858772216414058870195 := by
  unfold tailWord_524998
  simp only [CollatzResearch.WordTrace]
  refine ⟨598382817250918230159739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 12765500101352922243407765 598382817250918230159739)
  ·
    refine ⟨897574225876377345239609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 598382817250918230159739 897574225876377345239609)
    ·
      refine ⟨673180669407283008929707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 897574225876377345239609 673180669407283008929707)
      ·
        refine ⟨1009771004110924513394561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 673180669407283008929707 1009771004110924513394561)
        ·
          refine ⟨757328253083193385045921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1009771004110924513394561 757328253083193385045921)
          ·
            refine ⟨567996189812395038784441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 757328253083193385045921 567996189812395038784441)
            ·
              refine ⟨425997142359296279088331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 567996189812395038784441 425997142359296279088331)
              ·
                refine ⟨638995713538944418632497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 425997142359296279088331 638995713538944418632497)
                ·
                  refine ⟨479246785154208313974373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 638995713538944418632497 479246785154208313974373)
                  ·
                    refine ⟨89858772216414058870195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 479246785154208313974373 89858772216414058870195)
                    ·
                      rfl

theorem cell23_524998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 2, 1, 2, 4].length) (baseStart_524998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_524998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_524998 prefixEnd_524998 := by exact prefixLift 524998
  have htrace : WordTrace (prefixWord ++ tailWord_524998) baseStart_524998 baseEnd_524998 := by
    simpa [prefixWord, tailWord_524998, baseEnd_524998] using wordTrace_append hprefix tailTrace_524998
  have hstable : (prefixWord ++ tailWord_524998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524998).length < 2 ^ (prefixWord ++ tailWord_524998).sum := by decide
  have hdescent : baseEnd_524998 < baseStart_524998 := by decide
  rcases family_descends (prefixWord ++ tailWord_524998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_525004 : List Nat := [2, 2, 1, 5, 1, 1, 4, 1, 2, 1, 3]
def baseStart_525004 : Nat := 118140960795 + 525004 * 2 ^ 59
def prefixEnd_525004 : Nat := 4983230072969 + 3 ^ 40 * 525004 * 2
def baseEnd_525004 : Nat := 269579397533169153135557

theorem tailTrace_525004 : CollatzResearch.WordTrace tailWord_525004 prefixEnd_525004 269579397533169153135557 := by
  unfold tailWord_525004
  simp only [CollatzResearch.WordTrace]
  refine ⟨9574234495003823194915033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12765645993338430926553377 9574234495003823194915033)
  ·
    refine ⟨7180675871252867396186275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9574234495003823194915033 7180675871252867396186275)
    ·
      refine ⟨10771013806879301094279413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7180675871252867396186275 10771013806879301094279413)
      ·
        refine ⟨1009782544394934477588695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10771013806879301094279413 1009782544394934477588695)
        ·
          refine ⟨1514673816592401716383043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1009782544394934477588695 1514673816592401716383043)
          ·
            refine ⟨2272010724888602574574565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1514673816592401716383043 2272010724888602574574565)
            ·
              refine ⟨426002010916612982732731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2272010724888602574574565 426002010916612982732731)
              ·
                refine ⟨639003016374919474099097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 426002010916612982732731 639003016374919474099097)
                ·
                  refine ⟨479252262281189605574323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 639003016374919474099097 479252262281189605574323)
                  ·
                    refine ⟨718878393421784408361485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 479252262281189605574323 718878393421784408361485)
                    ·
                      refine ⟨269579397533169153135557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 718878393421784408361485 269579397533169153135557)
                      ·
                        rfl

theorem cell23_525004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 4, 1, 2, 1, 3].length) (baseStart_525004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_525004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_525004 prefixEnd_525004 := by exact prefixLift 525004
  have htrace : WordTrace (prefixWord ++ tailWord_525004) baseStart_525004 baseEnd_525004 := by
    simpa [prefixWord, tailWord_525004, baseEnd_525004] using wordTrace_append hprefix tailTrace_525004
  have hstable : (prefixWord ++ tailWord_525004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_525004).length < 2 ^ (prefixWord ++ tailWord_525004).sum := by decide
  have hdescent : baseEnd_525004 < baseStart_525004 := by decide
  rcases family_descends (prefixWord ++ tailWord_525004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_525027 : List Nat := [1, 1, 1, 7, 1, 2, 1, 2, 1, 4, 2]
def baseStart_525027 : Nat := 118140960795 + 525027 * 2 ^ 59
def prefixEnd_525027 : Nat := 4983230072969 + 3 ^ 40 * 525027 * 2
def baseEnd_525027 : Nat := 269591207588222563147951

theorem tailTrace_525027 : CollatzResearch.WordTrace tailWord_525027 prefixEnd_525027 269591207588222563147951 := by
  unfold tailWord_525027
  simp only [CollatzResearch.WordTrace]
  refine ⟨19149307868924321317917335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12766205245949547545278223 19149307868924321317917335)
  ·
    refine ⟨28723961803386481976876003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19149307868924321317917335 28723961803386481976876003)
    ·
      refine ⟨43085942705079722965314005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28723961803386481976876003 43085942705079722965314005)
      ·
        refine ⟨1009826782150306006999547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 43085942705079722965314005 1009826782150306006999547)
        ·
          refine ⟨1514740173225459010499321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1009826782150306006999547 1514740173225459010499321)
          ·
            refine ⟨1136055129919094257874491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1514740173225459010499321 1136055129919094257874491)
            ·
              refine ⟨1704082694878641386811737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1136055129919094257874491 1704082694878641386811737)
              ·
                refine ⟨1278062021158981040108803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1704082694878641386811737 1278062021158981040108803)
                ·
                  refine ⟨1917093031738471560163205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1278062021158981040108803 1917093031738471560163205)
                  ·
                    refine ⟨359454943450963417530601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1917093031738471560163205 359454943450963417530601)
                    ·
                      refine ⟨269591207588222563147951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 359454943450963417530601 269591207588222563147951)
                      ·
                        rfl

theorem cell23_525027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 1, 2, 1, 4, 2].length) (baseStart_525027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_525027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_525027 prefixEnd_525027 := by exact prefixLift 525027
  have htrace : WordTrace (prefixWord ++ tailWord_525027) baseStart_525027 baseEnd_525027 := by
    simpa [prefixWord, tailWord_525027, baseEnd_525027] using wordTrace_append hprefix tailTrace_525027
  have hstable : (prefixWord ++ tailWord_525027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_525027).length < 2 ^ (prefixWord ++ tailWord_525027).sum := by decide
  have hdescent : baseEnd_525027 < baseStart_525027 := by decide
  rcases family_descends (prefixWord ++ tailWord_525027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_525043 : List Nat := [1, 1, 1, 2, 2, 3, 1, 4, 2, 3, 3]
def baseStart_525043 : Nat := 118140960795 + 525043 * 2 ^ 59
def prefixEnd_525043 : Nat := 4983230072969 + 3 ^ 40 * 525043 * 2
def baseEnd_525043 : Nat := 269599423278694500547877

theorem tailTrace_525043 : CollatzResearch.WordTrace tailWord_525043 prefixEnd_525043 269599423278694500547877 := by
  unfold tailWord_525043
  simp only [CollatzResearch.WordTrace]
  refine ⟨19149891436866356050499783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12766594291244237366999855 19149891436866356050499783)
  ·
    refine ⟨28724837155299534075749675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19149891436866356050499783 28724837155299534075749675)
    ·
      refine ⟨43087255732949301113624513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28724837155299534075749675 43087255732949301113624513)
      ·
        refine ⟨32315441799711975835218385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43087255732949301113624513 32315441799711975835218385)
        ·
          refine ⟨24236581349783981876413789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32315441799711975835218385 24236581349783981876413789)
          ·
            refine ⟨9088718006168993203655171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24236581349783981876413789 9088718006168993203655171)
            ·
              refine ⟨13633077009253489805482757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9088718006168993203655171 13633077009253489805482757)
              ·
                refine ⟨2556201939235029338528017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13633077009253489805482757 2556201939235029338528017)
                ·
                  refine ⟨1917151454426272003896013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2556201939235029338528017 1917151454426272003896013)
                  ·
                    refine ⟨718931795409852001461005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1917151454426272003896013 718931795409852001461005)
                    ·
                      refine ⟨269599423278694500547877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 718931795409852001461005 269599423278694500547877)
                      ·
                        rfl

theorem cell23_525043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 4, 2, 3, 3].length) (baseStart_525043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_525043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_525043 prefixEnd_525043 := by exact prefixLift 525043
  have htrace : WordTrace (prefixWord ++ tailWord_525043) baseStart_525043 baseEnd_525043 := by
    simpa [prefixWord, tailWord_525043, baseEnd_525043] using wordTrace_append hprefix tailTrace_525043
  have hstable : (prefixWord ++ tailWord_525043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_525043).length < 2 ^ (prefixWord ++ tailWord_525043).sum := by decide
  have hdescent : baseEnd_525043 < baseStart_525043 := by decide
  rcases family_descends (prefixWord ++ tailWord_525043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_525060 : List Nat := [2, 3, 2, 2, 1, 1, 3, 1, 2, 3, 3]
def baseStart_525060 : Nat := 118140960795 + 525060 * 2 ^ 59
def prefixEnd_525060 : Nat := 4983230072969 + 3 ^ 40 * 525060 * 2
def baseEnd_525060 : Nat := 269608152449820934035299

theorem tailTrace_525060 : CollatzResearch.WordTrace tailWord_525060 prefixEnd_525060 269608152449820934035299 := by
  unfold tailWord_525060
  simp only [CollatzResearch.WordTrace]
  refine ⟨9575255738902383976934317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12767007651869845302579089 9575255738902383976934317)
  ·
    refine ⟨3590720902088393991350369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9575255738902383976934317 3590720902088393991350369)
    ·
      refine ⟨2693040676566295493512777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3590720902088393991350369 2693040676566295493512777)
      ·
        refine ⟨2019780507424721620134583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2693040676566295493512777 2019780507424721620134583)
        ·
          refine ⟨3029670761137082430201875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2019780507424721620134583 3029670761137082430201875)
          ·
            refine ⟨4544506141705623645302813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3029670761137082430201875 4544506141705623645302813)
            ·
              refine ⟨1704189803139608866988555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4544506141705623645302813 1704189803139608866988555)
              ·
                refine ⟨2556284704709413300482833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1704189803139608866988555 2556284704709413300482833)
                ·
                  refine ⟨1917213528532059975362125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2556284704709413300482833 1917213528532059975362125)
                  ·
                    refine ⟨718955073199522490760797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1917213528532059975362125 718955073199522490760797)
                    ·
                      refine ⟨269608152449820934035299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 718955073199522490760797 269608152449820934035299)
                      ·
                        rfl

theorem cell23_525060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 3, 1, 2, 3, 3].length) (baseStart_525060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_525060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_525060 prefixEnd_525060 := by exact prefixLift 525060
  have htrace : WordTrace (prefixWord ++ tailWord_525060) baseStart_525060 baseEnd_525060 := by
    simpa [prefixWord, tailWord_525060, baseEnd_525060] using wordTrace_append hprefix tailTrace_525060
  have hstable : (prefixWord ++ tailWord_525060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_525060).length < 2 ^ (prefixWord ++ tailWord_525060).sum := by decide
  have hdescent : baseEnd_525060 < baseStart_525060 := by decide
  rcases family_descends (prefixWord ++ tailWord_525060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_525070 : List Nat := [4, 1, 1, 2, 1, 1, 1, 1, 4, 5, 2]
def baseStart_525070 : Nat := 118140960795 + 525070 * 2 ^ 59
def prefixEnd_525070 : Nat := 4983230072969 + 3 ^ 40 * 525070 * 2
def baseEnd_525070 : Nat := 269613287256365894910253

theorem tailTrace_525070 : CollatzResearch.WordTrace tailWord_525070 prefixEnd_525070 269613287256365894910253 := by
  unfold tailWord_525070
  simp only [CollatzResearch.WordTrace]
  refine ⟨2393859525971067457716583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12767250805179026441155109 2393859525971067457716583)
  ·
    refine ⟨3590789288956601186574875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2393859525971067457716583 3590789288956601186574875)
    ·
      refine ⟨5386183933434901779862313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3590789288956601186574875 5386183933434901779862313)
      ·
        refine ⟨4039637950076176334896735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5386183933434901779862313 4039637950076176334896735)
        ·
          refine ⟨6059456925114264502345103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4039637950076176334896735 6059456925114264502345103)
          ·
            refine ⟨9089185387671396753517655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6059456925114264502345103 9089185387671396753517655)
            ·
              refine ⟨13633778081507095130276483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9089185387671396753517655 13633778081507095130276483)
              ·
                refine ⟨20450667122260642695414725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13633778081507095130276483 20450667122260642695414725)
                ·
                  refine ⟨3834500085423870505390261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20450667122260642695414725 3834500085423870505390261)
                  ·
                    refine ⟨359484383008487859880337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3834500085423870505390261 359484383008487859880337)
                    ·
                      refine ⟨269613287256365894910253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 359484383008487859880337 269613287256365894910253)
                      ·
                        rfl

theorem cell23_525070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 1, 4, 5, 2].length) (baseStart_525070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_525070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_525070 prefixEnd_525070 := by exact prefixLift 525070
  have htrace : WordTrace (prefixWord ++ tailWord_525070) baseStart_525070 baseEnd_525070 := by
    simpa [prefixWord, tailWord_525070, baseEnd_525070] using wordTrace_append hprefix tailTrace_525070
  have hstable : (prefixWord ++ tailWord_525070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_525070).length < 2 ^ (prefixWord ++ tailWord_525070).sum := by decide
  have hdescent : baseEnd_525070 < baseStart_525070 := by decide
  rcases family_descends (prefixWord ++ tailWord_525070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_525100 : List Nat := [2, 2, 1, 1, 1, 4, 1, 1, 4, 4, 2]
def baseStart_525100 : Nat := 118140960795 + 525100 * 2 ^ 59
def prefixEnd_525100 : Nat := 4983230072969 + 3 ^ 40 * 525100 * 2
def baseEnd_525100 : Nat := 269628691676000777535115

theorem tailTrace_525100 : CollatzResearch.WordTrace tailWord_525100 prefixEnd_525100 269628691676000777535115 := by
  unfold tailWord_525100
  simp only [CollatzResearch.WordTrace]
  refine ⟨9575985198829927392662377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12767980265106569856883169 9575985198829927392662377)
  ·
    refine ⟨7181988899122445544496783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9575985198829927392662377 7181988899122445544496783)
    ·
      refine ⟨10772983348683668316745175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7181988899122445544496783 10772983348683668316745175)
      ·
        refine ⟨16159475023025502475117763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10772983348683668316745175 16159475023025502475117763)
        ·
          refine ⟨24239212534538253712676645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16159475023025502475117763 24239212534538253712676645)
          ·
            refine ⟨4544852350225922571126871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24239212534538253712676645 4544852350225922571126871)
            ·
              refine ⟨6817278525338883856690307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4544852350225922571126871 6817278525338883856690307)
              ·
                refine ⟨10225917788008325785035461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6817278525338883856690307 10225917788008325785035461)
                ·
                  refine ⟨1917359585251561084694149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10225917788008325785035461 1917359585251561084694149)
                  ·
                    refine ⟨359504922234667703380153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1917359585251561084694149 359504922234667703380153)
                    ·
                      refine ⟨269628691676000777535115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 359504922234667703380153 269628691676000777535115)
                      ·
                        rfl

theorem cell23_525100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 4, 2].length) (baseStart_525100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_525100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_525100 prefixEnd_525100 := by exact prefixLift 525100
  have htrace : WordTrace (prefixWord ++ tailWord_525100) baseStart_525100 baseEnd_525100 := by
    simpa [prefixWord, tailWord_525100, baseEnd_525100] using wordTrace_append hprefix tailTrace_525100
  have hstable : (prefixWord ++ tailWord_525100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_525100).length < 2 ^ (prefixWord ++ tailWord_525100).sum := by decide
  have hdescent : baseEnd_525100 < baseStart_525100 := by decide
  rcases family_descends (prefixWord ++ tailWord_525100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_525103 : List Nat := [1, 1, 2, 1, 2, 1, 2, 1, 5, 4, 3]
def baseStart_525103 : Nat := 118140960795 + 525103 * 2 ^ 59
def prefixEnd_525103 : Nat := 4983230072969 + 3 ^ 40 * 525103 * 2
def baseEnd_525103 : Nat := 269630232117964265797601

theorem tailTrace_525103 : CollatzResearch.WordTrace tailWord_525103 prefixEnd_525103 269630232117964265797601 := by
  unfold tailWord_525103
  simp only [CollatzResearch.WordTrace]
  refine ⟨19152079816648986297683963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12768053211099324198455975 19152079816648986297683963)
  ·
    refine ⟨28728119724973479446525945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19152079816648986297683963 28728119724973479446525945)
    ·
      refine ⟨21546089793730109584894459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28728119724973479446525945 21546089793730109584894459)
      ·
        refine ⟨32319134690595164377341689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21546089793730109584894459 32319134690595164377341689)
        ·
          refine ⟨24239351017946373283006267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32319134690595164377341689 24239351017946373283006267)
          ·
            refine ⟨36359026526919559924509401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24239351017946373283006267 36359026526919559924509401)
            ·
              refine ⟨27269269895189669943382051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36359026526919559924509401 27269269895189669943382051)
              ·
                refine ⟨40903904842784504915073077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27269269895189669943382051 40903904842784504915073077)
                ·
                  refine ⟨3834741079011047335788101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40903904842784504915073077 3834741079011047335788101)
                  ·
                    refine ⟨719013952314571375460269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3834741079011047335788101 719013952314571375460269)
                    ·
                      refine ⟨269630232117964265797601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 719013952314571375460269 269630232117964265797601)
                      ·
                        rfl

theorem cell23_525103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 5, 4, 3].length) (baseStart_525103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_525103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_525103 prefixEnd_525103 := by exact prefixLift 525103
  have htrace : WordTrace (prefixWord ++ tailWord_525103) baseStart_525103 baseEnd_525103 := by
    simpa [prefixWord, tailWord_525103, baseEnd_525103] using wordTrace_append hprefix tailTrace_525103
  have hstable : (prefixWord ++ tailWord_525103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_525103).length < 2 ^ (prefixWord ++ tailWord_525103).sum := by decide
  have hdescent : baseEnd_525103 < baseStart_525103 := by decide
  rcases family_descends (prefixWord ++ tailWord_525103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_525154 : List Nat := [3, 3, 2, 1, 3, 1, 1, 2, 2, 2, 3]
def baseStart_525154 : Nat := 118140960795 + 525154 * 2 ^ 59
def prefixEnd_525154 : Nat := 4983230072969 + 3 ^ 40 * 525154 * 2
def baseEnd_525154 : Nat := 269656419631343566259867

theorem tailTrace_525154 : CollatzResearch.WordTrace tailWord_525154 prefixEnd_525154 269656419631343566259867 := by
  unfold tailWord_525154
  simp only [CollatzResearch.WordTrace]
  refine ⟨4788484984866055501947629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12769293292976148005193677 4788484984866055501947629)
  ·
    refine ⟨1795681869324770813230361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4788484984866055501947629 1795681869324770813230361)
    ·
      refine ⟨1346761401993578109922771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1795681869324770813230361 1346761401993578109922771)
      ·
        refine ⟨2020142102990367164884157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1346761401993578109922771 2020142102990367164884157)
        ·
          refine ⟨757553288621387686831559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2020142102990367164884157 757553288621387686831559)
          ·
            refine ⟨1136329932932081530247339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 757553288621387686831559 1136329932932081530247339)
            ·
              refine ⟨1704494899398122295371009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1136329932932081530247339 1704494899398122295371009)
              ·
                refine ⟨1278371174548591721528257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1704494899398122295371009 1278371174548591721528257)
                ·
                  refine ⟨958778380911443791146193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1278371174548591721528257 958778380911443791146193)
                  ·
                    refine ⟨719083785683582843359645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 958778380911443791146193 719083785683582843359645)
                    ·
                      refine ⟨269656419631343566259867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 719083785683582843359645 269656419631343566259867)
                      ·
                        rfl

theorem cell23_525154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 1, 2, 2, 2, 3].length) (baseStart_525154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_525154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_525154 prefixEnd_525154 := by exact prefixLift 525154
  have htrace : WordTrace (prefixWord ++ tailWord_525154) baseStart_525154 baseEnd_525154 := by
    simpa [prefixWord, tailWord_525154, baseEnd_525154] using wordTrace_append hprefix tailTrace_525154
  have hstable : (prefixWord ++ tailWord_525154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_525154).length < 2 ^ (prefixWord ++ tailWord_525154).sum := by decide
  have hdescent : baseEnd_525154 < baseStart_525154 := by decide
  rcases family_descends (prefixWord ++ tailWord_525154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_525174 : List Nat := [5, 1, 1, 3, 1, 1, 4, 1, 6]
def baseStart_525174 : Nat := 118140960795 + 525174 * 2 ^ 59
def prefixEnd_525174 : Nat := 4983230072969 + 3 ^ 40 * 525174 * 2
def baseEnd_525174 : Nat := 29962965471603720889975

theorem tailTrace_525174 : CollatzResearch.WordTrace tailWord_525174 prefixEnd_525174 29962965471603720889975 := by
  unfold tailWord_525174
  simp only [CollatzResearch.WordTrace]
  refine ⟨1197166837461985338969911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12769779599594510282345717 1197166837461985338969911)
  ·
    refine ⟨1795750256192978008454867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1197166837461985338969911 1795750256192978008454867)
    ·
      refine ⟨2693625384289467012682301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1795750256192978008454867 2693625384289467012682301)
      ·
        refine ⟨1010109519108550129755863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2693625384289467012682301 1010109519108550129755863)
        ·
          refine ⟨1515164278662825194633795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1010109519108550129755863 1515164278662825194633795)
          ·
            refine ⟨2272746417994237791950693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1515164278662825194633795 2272746417994237791950693)
            ·
              refine ⟨426139953373919585990755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2272746417994237791950693 426139953373919585990755)
              ·
                refine ⟨639209930060879378986133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 426139953373919585990755 639209930060879378986133)
                ·
                  refine ⟨29962965471603720889975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 639209930060879378986133 29962965471603720889975)
                  ·
                    rfl

theorem cell23_525174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 4, 1, 6].length) (baseStart_525174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_525174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_525174 prefixEnd_525174 := by exact prefixLift 525174
  have htrace : WordTrace (prefixWord ++ tailWord_525174) baseStart_525174 baseEnd_525174 := by
    simpa [prefixWord, tailWord_525174, baseEnd_525174] using wordTrace_append hprefix tailTrace_525174
  have hstable : (prefixWord ++ tailWord_525174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_525174).length < 2 ^ (prefixWord ++ tailWord_525174).sum := by decide
  have hdescent : baseEnd_525174 < baseStart_525174 := by decide
  rcases family_descends (prefixWord ++ tailWord_525174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_525194 : List Nat := [3, 1, 2, 4, 1, 1, 1, 3, 2, 3, 2]
def baseStart_525194 : Nat := 118140960795 + 525194 * 2 ^ 59
def prefixEnd_525194 : Nat := 4983230072969 + 3 ^ 40 * 525194 * 2
def baseEnd_525194 : Nat := 269676958857523409759683

theorem tailTrace_525194 : CollatzResearch.WordTrace tailWord_525194 prefixEnd_525194 269676958857523409759683 := by
  unfold tailWord_525194
  simp only [CollatzResearch.WordTrace]
  refine ⟨4788849714829827209811659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12770265906212872559497757 4788849714829827209811659)
  ·
    refine ⟨7183274572244740814717489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4788849714829827209811659 7183274572244740814717489)
    ·
      refine ⟨5387455929183555611038117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7183274572244740814717489 5387455929183555611038117)
      ·
        refine ⟨1010147986721916677069647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5387455929183555611038117 1010147986721916677069647)
        ·
          refine ⟨1515221980082875015604471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1010147986721916677069647 1515221980082875015604471)
          ·
            refine ⟨2272832970124312523406707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1515221980082875015604471 2272832970124312523406707)
            ·
              refine ⟨3409249455186468785110061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2272832970124312523406707 3409249455186468785110061)
              ·
                refine ⟨1278468545694925794416273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3409249455186468785110061 1278468545694925794416273)
                ·
                  refine ⟨958851409271194345812205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1278468545694925794416273 958851409271194345812205)
                  ·
                    refine ⟨359569278476697879679577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 958851409271194345812205 359569278476697879679577)
                    ·
                      refine ⟨269676958857523409759683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 359569278476697879679577 269676958857523409759683)
                      ·
                        rfl

theorem cell23_525194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 3, 2, 3, 2].length) (baseStart_525194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_525194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_525194 prefixEnd_525194 := by exact prefixLift 525194
  have htrace : WordTrace (prefixWord ++ tailWord_525194) baseStart_525194 baseEnd_525194 := by
    simpa [prefixWord, tailWord_525194, baseEnd_525194] using wordTrace_append hprefix tailTrace_525194
  have hstable : (prefixWord ++ tailWord_525194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_525194).length < 2 ^ (prefixWord ++ tailWord_525194).sum := by decide
  have hdescent : baseEnd_525194 < baseStart_525194 := by decide
  rcases family_descends (prefixWord ++ tailWord_525194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_525203 : List Nat := [1, 1, 1, 2, 1, 2, 1, 4, 3, 1, 6]
def baseStart_525203 : Nat := 118140960795 + 525203 * 2 ^ 59
def prefixEnd_525203 : Nat := 4983230072969 + 3 ^ 40 * 525203 * 2
def baseEnd_525203 : Nat := 269681580183413874547141

theorem tailTrace_525203 : CollatzResearch.WordTrace tailWord_525203 prefixEnd_525203 269681580183413874547141 := by
  unfold tailWord_525203
  simp only [CollatzResearch.WordTrace]
  refine ⟨19155727116286703376324263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12770484744191135584216175 19155727116286703376324263)
  ·
    refine ⟨28733590674430055064486395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19155727116286703376324263 28733590674430055064486395)
    ·
      refine ⟨43100386011645082596729593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28733590674430055064486395 43100386011645082596729593)
      ·
        refine ⟨32325289508733811947547195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43100386011645082596729593 32325289508733811947547195)
        ·
          refine ⟨48487934263100717921320793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32325289508733811947547195 48487934263100717921320793)
          ·
            refine ⟨36365950697325538440990595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48487934263100717921320793 36365950697325538440990595)
            ·
              refine ⟨54548926045988307661485893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36365950697325538440990595 54548926045988307661485893)
              ·
                refine ⟨10227923633622807686528605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54548926045988307661485893 10227923633622807686528605)
                ·
                  refine ⟨3835471362608552882448227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10227923633622807686528605 3835471362608552882448227)
                  ·
                    refine ⟨5753207043912829323672341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3835471362608552882448227 5753207043912829323672341)
                    ·
                      refine ⟨269681580183413874547141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 5753207043912829323672341 269681580183413874547141)
                      ·
                        rfl

theorem cell23_525203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 4, 3, 1, 6].length) (baseStart_525203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_525203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_525203 prefixEnd_525203 := by exact prefixLift 525203
  have htrace : WordTrace (prefixWord ++ tailWord_525203) baseStart_525203 baseEnd_525203 := by
    simpa [prefixWord, tailWord_525203, baseEnd_525203] using wordTrace_append hprefix tailTrace_525203
  have hstable : (prefixWord ++ tailWord_525203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_525203).length < 2 ^ (prefixWord ++ tailWord_525203).sum := by decide
  have hdescent : baseEnd_525203 < baseStart_525203 := by decide
  rcases family_descends (prefixWord ++ tailWord_525203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_525204 : List Nat := [2, 4, 2, 1, 1, 1, 5, 1, 1, 5]
def baseStart_525204 : Nat := 118140960795 + 525204 * 2 ^ 59
def prefixEnd_525204 : Nat := 4983230072969 + 3 ^ 40 * 525204 * 2
def baseEnd_525204 : Nat := 89894031221356123544879

theorem tailTrace_525204 : CollatzResearch.WordTrace tailWord_525204 prefixEnd_525204 89894031221356123544879 := by
  unfold tailWord_525204
  simp only [CollatzResearch.WordTrace]
  refine ⟨9577881794641540273555333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12770509059522053698073777 9577881794641540273555333)
  ·
    refine ⟨1795852836495288801291625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9577881794641540273555333 1795852836495288801291625)
    ·
      refine ⟨1346889627371466600968719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1795852836495288801291625 1346889627371466600968719)
      ·
        refine ⟨2020334441057199901453079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1346889627371466600968719 2020334441057199901453079)
        ·
          refine ⟨3030501661585799852179619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2020334441057199901453079 3030501661585799852179619)
          ·
            refine ⟨4545752492378699778269429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3030501661585799852179619 4545752492378699778269429)
            ·
              refine ⟨426164296160503104212759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4545752492378699778269429 426164296160503104212759)
              ·
                refine ⟨639246444240754656319139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 426164296160503104212759 639246444240754656319139)
                ·
                  refine ⟨958869666361131984478709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 639246444240754656319139 958869666361131984478709)
                  ·
                    refine ⟨89894031221356123544879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 958869666361131984478709 89894031221356123544879)
                    ·
                      rfl

theorem cell23_525204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 5, 1, 1, 5].length) (baseStart_525204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_525204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_525204 prefixEnd_525204 := by exact prefixLift 525204
  have htrace : WordTrace (prefixWord ++ tailWord_525204) baseStart_525204 baseEnd_525204 := by
    simpa [prefixWord, tailWord_525204, baseEnd_525204] using wordTrace_append hprefix tailTrace_525204
  have hstable : (prefixWord ++ tailWord_525204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_525204).length < 2 ^ (prefixWord ++ tailWord_525204).sum := by decide
  have hdescent : baseEnd_525204 < baseStart_525204 := by decide
  rcases family_descends (prefixWord ++ tailWord_525204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_525218 : List Nat := [3, 3, 1, 2, 2, 1, 4, 2, 1, 1, 3]
def baseStart_525218 : Nat := 118140960795 + 525218 * 2 ^ 59
def prefixEnd_525218 : Nat := 4983230072969 + 3 ^ 40 * 525218 * 2
def baseEnd_525218 : Nat := 269689282393231315859573

theorem tailTrace_525218 : CollatzResearch.WordTrace tailWord_525218 prefixEnd_525218 269689282393231315859573 := by
  unfold tailWord_525218
  simp only [CollatzResearch.WordTrace]
  refine ⟨4789068552808090234530077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12770849474154907292080205 4789068552808090234530077)
  ·
    refine ⟨1795900707303033837948779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4789068552808090234530077 1795900707303033837948779)
    ·
      refine ⟨2693851060954550756923169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1795900707303033837948779 2693851060954550756923169)
      ·
        refine ⟨2020388295715913067692377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2693851060954550756923169 2020388295715913067692377)
        ·
          refine ⟨1515291221786934800769283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2020388295715913067692377 1515291221786934800769283)
          ·
            refine ⟨2272936832680402201153925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1515291221786934800769283 2272936832680402201153925)
            ·
              refine ⟨426175656127575412716361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2272936832680402201153925 426175656127575412716361)
              ·
                refine ⟨319631742095681559537271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 426175656127575412716361 319631742095681559537271)
                ·
                  refine ⟨479447613143522339305907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 319631742095681559537271 479447613143522339305907)
                  ·
                    refine ⟨719171419715283508958861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 479447613143522339305907 719171419715283508958861)
                    ·
                      refine ⟨269689282393231315859573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 719171419715283508958861 269689282393231315859573)
                      ·
                        rfl

theorem cell23_525218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 4, 2, 1, 1, 3].length) (baseStart_525218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_525218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_525218 prefixEnd_525218 := by exact prefixLift 525218
  have htrace : WordTrace (prefixWord ++ tailWord_525218) baseStart_525218 baseEnd_525218 := by
    simpa [prefixWord, tailWord_525218, baseEnd_525218] using wordTrace_append hprefix tailTrace_525218
  have hstable : (prefixWord ++ tailWord_525218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_525218).length < 2 ^ (prefixWord ++ tailWord_525218).sum := by decide
  have hdescent : baseEnd_525218 < baseStart_525218 := by decide
  rcases family_descends (prefixWord ++ tailWord_525218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_525220 : List Nat := [2, 3, 1, 2, 1, 2, 1, 2, 3, 2, 4]
def baseStart_525220 : Nat := 118140960795 + 525220 * 2 ^ 59
def prefixEnd_525220 : Nat := 4983230072969 + 3 ^ 40 * 525220 * 2
def baseEnd_525220 : Nat := 269690309354540308034563

theorem tailTrace_525220 : CollatzResearch.WordTrace tailWord_525220 prefixEnd_525220 269690309354540308034563 := by
  unfold tailWord_525220
  simp only [CollatzResearch.WordTrace]
  refine ⟨9578173578612557639846557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12770898104816743519795409 9578173578612557639846557)
  ·
    refine ⟨3591815091979709114942459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9578173578612557639846557 3591815091979709114942459)
    ·
      refine ⟨5387722637969563672413689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3591815091979709114942459 5387722637969563672413689)
      ·
        refine ⟨4040791978477172754310267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5387722637969563672413689 4040791978477172754310267)
        ·
          refine ⟨6061187967715759131465401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4040791978477172754310267 6061187967715759131465401)
          ·
            refine ⟨4545890975786819348599051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6061187967715759131465401 4545890975786819348599051)
            ·
              refine ⟨6818836463680229022898577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4545890975786819348599051 6818836463680229022898577)
              ·
                refine ⟨5114127347760171767173933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6818836463680229022898577 5114127347760171767173933)
                ·
                  refine ⟨1917797755410064412690225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5114127347760171767173933 1917797755410064412690225)
                  ·
                    refine ⟨1438348316557548309517669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1917797755410064412690225 1438348316557548309517669)
                    ·
                      refine ⟨269690309354540308034563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1438348316557548309517669 269690309354540308034563)
                      ·
                        rfl

theorem cell23_525220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 2, 3, 2, 4].length) (baseStart_525220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_525220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_525220 prefixEnd_525220 := by exact prefixLift 525220
  have htrace : WordTrace (prefixWord ++ tailWord_525220) baseStart_525220 baseEnd_525220 := by
    simpa [prefixWord, tailWord_525220, baseEnd_525220] using wordTrace_append hprefix tailTrace_525220
  have hstable : (prefixWord ++ tailWord_525220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_525220).length < 2 ^ (prefixWord ++ tailWord_525220).sum := by decide
  have hdescent : baseEnd_525220 < baseStart_525220 := by decide
  rcases family_descends (prefixWord ++ tailWord_525220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_525237 : List Nat := [1, 3, 3, 2, 1, 1, 4, 1, 1, 2, 4]
def baseStart_525237 : Nat := 118140960795 + 525237 * 2 ^ 59
def prefixEnd_525237 : Nat := 4983230072969 + 3 ^ 40 * 525237 * 2
def baseEnd_525237 : Nat := 269699038525666741521985

theorem tailTrace_525237 : CollatzResearch.WordTrace tailWord_525237 prefixEnd_525237 269699038525666741521985 := by
  unfold tailWord_525237
  simp only [CollatzResearch.WordTrace]
  refine ⟨19156967198163527183061965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12771311465442351455374643 19156967198163527183061965)
  ·
    refine ⟨7183862699311322693648237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19156967198163527183061965 7183862699311322693648237)
    ·
      refine ⟨2693948512241746010118089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7183862699311322693648237 2693948512241746010118089)
      ·
        refine ⟨2020461384181309507588567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2693948512241746010118089 2020461384181309507588567)
        ·
          refine ⟨3030692076271964261382851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2020461384181309507588567 3030692076271964261382851)
          ·
            refine ⟨4546038114407946392074277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3030692076271964261382851 4546038114407946392074277)
            ·
              refine ⟨852382146451489948513927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4546038114407946392074277 852382146451489948513927)
              ·
                refine ⟨1278573219677234922770891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 852382146451489948513927 1278573219677234922770891)
                ·
                  refine ⟨1917859829515852384156337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1278573219677234922770891 1917859829515852384156337)
                  ·
                    refine ⟨1438394872136889288117253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1917859829515852384156337 1438394872136889288117253)
                    ·
                      refine ⟨269699038525666741521985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1438394872136889288117253 269699038525666741521985)
                      ·
                        rfl

theorem cell23_525237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 4, 1, 1, 2, 4].length) (baseStart_525237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_525237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_525237 prefixEnd_525237 := by exact prefixLift 525237
  have htrace : WordTrace (prefixWord ++ tailWord_525237) baseStart_525237 baseEnd_525237 := by
    simpa [prefixWord, tailWord_525237, baseEnd_525237] using wordTrace_append hprefix tailTrace_525237
  have hstable : (prefixWord ++ tailWord_525237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_525237).length < 2 ^ (prefixWord ++ tailWord_525237).sum := by decide
  have hdescent : baseEnd_525237 < baseStart_525237 := by decide
  rcases family_descends (prefixWord ++ tailWord_525237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_525243 : List Nat := [1, 1, 1, 1, 1, 2, 2, 2, 3, 9]
def baseStart_525243 : Nat := 118140960795 + 525243 * 2 ^ 59
def prefixEnd_525243 : Nat := 4983230072969 + 3 ^ 40 * 525243 * 2
def baseEnd_525243 : Nat := 89900706469864572682319

theorem tailTrace_525243 : CollatzResearch.WordTrace tailWord_525243 prefixEnd_525243 89900706469864572682319 := by
  unfold tailWord_525243
  simp only [CollatzResearch.WordTrace]
  refine ⟨19157186036141790207780383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12771457357427860138520255 19157186036141790207780383)
  ·
    refine ⟨28735779054212685311670575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19157186036141790207780383 28735779054212685311670575)
    ·
      refine ⟨43103668581319027967505863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28735779054212685311670575 43103668581319027967505863)
      ·
        refine ⟨64655502871978541951258795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43103668581319027967505863 64655502871978541951258795)
        ·
          refine ⟨96983254307967812926888193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64655502871978541951258795 96983254307967812926888193)
          ·
            refine ⟨72737440730975859695166145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96983254307967812926888193 72737440730975859695166145)
            ·
              refine ⟨54553080548231894771374609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72737440730975859695166145 54553080548231894771374609)
              ·
                refine ⟨40914810411173921078530957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54553080548231894771374609 40914810411173921078530957)
                ·
                  refine ⟨15343053904190220404449109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40914810411173921078530957 15343053904190220404449109)
                  ·
                    refine ⟨89900706469864572682319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 15343053904190220404449109 89900706469864572682319)
                    ·
                      rfl

theorem cell23_525243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 9].length) (baseStart_525243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_525243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_525243 prefixEnd_525243 := by exact prefixLift 525243
  have htrace : WordTrace (prefixWord ++ tailWord_525243) baseStart_525243 baseEnd_525243 := by
    simpa [prefixWord, tailWord_525243, baseEnd_525243] using wordTrace_append hprefix tailTrace_525243
  have hstable : (prefixWord ++ tailWord_525243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_525243).length < 2 ^ (prefixWord ++ tailWord_525243).sum := by decide
  have hdescent : baseEnd_525243 < baseStart_525243 := by decide
  rcases family_descends (prefixWord ++ tailWord_525243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_525274 : List Nat := [3, 1, 1, 2, 4, 2, 1, 1, 4, 1, 3]
def baseStart_525274 : Nat := 118140960795 + 525274 * 2 ^ 59
def prefixEnd_525274 : Nat := 4983230072969 + 3 ^ 40 * 525274 * 2
def baseEnd_525274 : Nat := 269718037309883096759315

theorem tailTrace_525274 : CollatzResearch.WordTrace tailWord_525274 prefixEnd_525274 269718037309883096759315 := by
  unfold tailWord_525274
  simp only [CollatzResearch.WordTrace]
  refine ⟨4789579174757370625539719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12772211132686321668105917 4789579174757370625539719)
  ·
    refine ⟨7184368762136055938309579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4789579174757370625539719 7184368762136055938309579)
    ·
      refine ⟨10776553143204083907464369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7184368762136055938309579 10776553143204083907464369)
      ·
        refine ⟨8082414857403062930598277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10776553143204083907464369 8082414857403062930598277)
        ·
          refine ⟨1515452785763074299487177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8082414857403062930598277 1515452785763074299487177)
          ·
            refine ⟨1136589589322305724615383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1515452785763074299487177 1136589589322305724615383)
            ·
              refine ⟨1704884383983458586923075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1136589589322305724615383 1704884383983458586923075)
              ·
                refine ⟨2557326575975187880384613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1704884383983458586923075 2557326575975187880384613)
                ·
                  refine ⟨479498732995347727572115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2557326575975187880384613 479498732995347727572115)
                  ·
                    refine ⟨719248099493021591358173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 479498732995347727572115 719248099493021591358173)
                    ·
                      refine ⟨269718037309883096759315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 719248099493021591358173 269718037309883096759315)
                      ·
                        rfl

theorem cell23_525274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 1, 1, 4, 1, 3].length) (baseStart_525274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_525274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_525274 prefixEnd_525274 := by exact prefixLift 525274
  have htrace : WordTrace (prefixWord ++ tailWord_525274) baseStart_525274 baseEnd_525274 := by
    simpa [prefixWord, tailWord_525274, baseEnd_525274] using wordTrace_append hprefix tailTrace_525274
  have hstable : (prefixWord ++ tailWord_525274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_525274).length < 2 ^ (prefixWord ++ tailWord_525274).sum := by decide
  have hdescent : baseEnd_525274 < baseStart_525274 := by decide
  rcases family_descends (prefixWord ++ tailWord_525274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_525337 : List Nat := [1, 2, 1, 2, 1, 1, 4, 6, 5]
def baseStart_525337 : Nat := 118140960795 + 525337 * 2 ^ 59
def prefixEnd_525337 : Nat := 4983230072969 + 3 ^ 40 * 525337 * 2
def baseEnd_525337 : Nat := 29972265176790705585725

theorem tailTrace_525337 : CollatzResearch.WordTrace tailWord_525337 prefixEnd_525337 29972265176790705585725 := by
  unfold tailWord_525337
  simp only [CollatzResearch.WordTrace]
  refine ⟨19160614497801244261702265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12773742998534162841134843 19160614497801244261702265)
  ·
    refine ⟨14370460873350933196276699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19160614497801244261702265 14370460873350933196276699)
    ·
      refine ⟨21555691310026399794415049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14370460873350933196276699 21555691310026399794415049)
      ·
        refine ⟨16166768482519799845811287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21555691310026399794415049 16166768482519799845811287)
        ·
          refine ⟨24250152723779699768716931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16166768482519799845811287 24250152723779699768716931)
          ·
            refine ⟨36375229085669549653075397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24250152723779699768716931 36375229085669549653075397)
            ·
              refine ⟨6820355453563040559951637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36375229085669549653075397 6820355453563040559951637)
              ·
                refine ⟨319704161885767526247733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 6820355453563040559951637 319704161885767526247733)
                ·
                  refine ⟨29972265176790705585725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 319704161885767526247733 29972265176790705585725)
                  ·
                    rfl

theorem cell23_525337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 6, 5].length) (baseStart_525337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_525337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_525337 prefixEnd_525337 := by exact prefixLift 525337
  have htrace : WordTrace (prefixWord ++ tailWord_525337) baseStart_525337 baseEnd_525337 := by
    simpa [prefixWord, tailWord_525337, baseEnd_525337] using wordTrace_append hprefix tailTrace_525337
  have hstable : (prefixWord ++ tailWord_525337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_525337).length < 2 ^ (prefixWord ++ tailWord_525337).sum := by decide
  have hdescent : baseEnd_525337 < baseStart_525337 := by decide
  rcases family_descends (prefixWord ++ tailWord_525337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_525348 : List Nat := [2, 3, 1, 4, 1, 2, 1, 3, 2, 2, 2]
def baseStart_525348 : Nat := 118140960795 + 525348 * 2 ^ 59
def prefixEnd_525348 : Nat := 4983230072969 + 3 ^ 40 * 525348 * 2
def baseEnd_525348 : Nat := 269756034878315807233975

theorem tailTrace_525348 : CollatzResearch.WordTrace tailWord_525348 prefixEnd_525348 269756034878315807233975 := by
  unfold tailWord_525348
  simp only [CollatzResearch.WordTrace]
  refine ⟨9580507850380696570176349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12774010467174262093568465 9580507850380696570176349)
  ·
    refine ⟨3592690443892761213816131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9580507850380696570176349 3592690443892761213816131)
    ·
      refine ⟨5389035665839141820724197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3592690443892761213816131 5389035665839141820724197)
      ·
        refine ⟨1010444187344839091385787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5389035665839141820724197 1010444187344839091385787)
        ·
          refine ⟨1515666281017258637078681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1010444187344839091385787 1515666281017258637078681)
          ·
            refine ⟨1136749710762943977809011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1515666281017258637078681 1136749710762943977809011)
            ·
              refine ⟨1705124566144415966713517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1136749710762943977809011 1705124566144415966713517)
              ·
                refine ⟨639421712304155987517569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1705124566144415966713517 639421712304155987517569)
                ·
                  refine ⟨479566284228116990638177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 639421712304155987517569 479566284228116990638177)
                  ·
                    refine ⟨359674713171087742978633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 479566284228116990638177 359674713171087742978633)
                    ·
                      refine ⟨269756034878315807233975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 359674713171087742978633 269756034878315807233975)
                      ·
                        rfl

theorem cell23_525348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 1, 3, 2, 2, 2].length) (baseStart_525348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_525348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_525348 prefixEnd_525348 := by exact prefixLift 525348
  have htrace : WordTrace (prefixWord ++ tailWord_525348) baseStart_525348 baseEnd_525348 := by
    simpa [prefixWord, tailWord_525348, baseEnd_525348] using wordTrace_append hprefix tailTrace_525348
  have hstable : (prefixWord ++ tailWord_525348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_525348).length < 2 ^ (prefixWord ++ tailWord_525348).sum := by decide
  have hdescent : baseEnd_525348 < baseStart_525348 := by decide
  rcases family_descends (prefixWord ++ tailWord_525348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_525360 : List Nat := [2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 7]
def baseStart_525360 : Nat := 118140960795 + 525360 * 2 ^ 59
def prefixEnd_525360 : Nat := 4983230072969 + 3 ^ 40 * 525360 * 2
def baseEnd_525360 : Nat := 269762196646169760283919

theorem tailTrace_525360 : CollatzResearch.WordTrace tailWord_525360 prefixEnd_525360 269762196646169760283919 := by
  unfold tailWord_525360
  simp only [CollatzResearch.WordTrace]
  refine ⟨9580726688358959594894767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12774302251145279459859689 9580726688358959594894767)
  ·
    refine ⟨14371090032538439392342151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9580726688358959594894767 14371090032538439392342151)
    ·
      refine ⟨21556635048807659088513227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14371090032538439392342151 21556635048807659088513227)
      ·
        refine ⟨32334952573211488632769841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21556635048807659088513227 32334952573211488632769841)
        ·
          refine ⟨24251214429908616474577381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32334952573211488632769841 24251214429908616474577381)
          ·
            refine ⟨4547102705607865588983259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24251214429908616474577381 4547102705607865588983259)
            ·
              refine ⟨6820654058411798383474889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4547102705607865588983259 6820654058411798383474889)
              ·
                refine ⟨5115490543808848787606167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6820654058411798383474889 5115490543808848787606167)
                ·
                  refine ⟨7673235815713273181409251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5115490543808848787606167 7673235815713273181409251)
                  ·
                    refine ⟨11509853723569909772113877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7673235815713273181409251 11509853723569909772113877)
                    ·
                      refine ⟨269762196646169760283919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 11509853723569909772113877 269762196646169760283919)
                      ·
                        rfl

theorem cell23_525360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 7].length) (baseStart_525360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_525360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_525360 prefixEnd_525360 := by exact prefixLift 525360
  have htrace : WordTrace (prefixWord ++ tailWord_525360) baseStart_525360 baseEnd_525360 := by
    simpa [prefixWord, tailWord_525360, baseEnd_525360] using wordTrace_append hprefix tailTrace_525360
  have hstable : (prefixWord ++ tailWord_525360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_525360).length < 2 ^ (prefixWord ++ tailWord_525360).sum := by decide
  have hdescent : baseEnd_525360 < baseStart_525360 := by decide
  rcases family_descends (prefixWord ++ tailWord_525360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_525398 : List Nat := [5, 2, 2, 1, 2, 1, 1, 1, 2, 3, 3]
def baseStart_525398 : Nat := 118140960795 + 525398 * 2 ^ 59
def prefixEnd_525398 : Nat := 4983230072969 + 3 ^ 40 * 525398 * 2
def baseEnd_525398 : Nat := 269781708911040611608745

theorem tailTrace_525398 : CollatzResearch.WordTrace tailWord_525398 prefixEnd_525398 269781708911040611608745 := by
  unfold tailWord_525398
  simp only [CollatzResearch.WordTrace]
  refine ⟨1197677459411265729979553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12775226233720167786448565 1197677459411265729979553)
  ·
    refine ⟨898258094558449297484665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1197677459411265729979553 898258094558449297484665)
    ·
      refine ⟨673693570918836973113499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 898258094558449297484665 673693570918836973113499)
      ·
        refine ⟨1010540356378255459670249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 673693570918836973113499 1010540356378255459670249)
        ·
          refine ⟨757905267283691594752687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1010540356378255459670249 757905267283691594752687)
          ·
            refine ⟨1136857900925537392129031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 757905267283691594752687 1136857900925537392129031)
            ·
              refine ⟨1705286851388306088193547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1136857900925537392129031 1705286851388306088193547)
              ·
                refine ⟨2557930277082459132290321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1705286851388306088193547 2557930277082459132290321)
                ·
                  refine ⟨1918447707811844349217741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2557930277082459132290321 1918447707811844349217741)
                  ·
                    refine ⟨719417890429441630956653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1918447707811844349217741 719417890429441630956653)
                    ·
                      refine ⟨269781708911040611608745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 719417890429441630956653 269781708911040611608745)
                      ·
                        rfl

theorem cell23_525398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 1, 1, 2, 3, 3].length) (baseStart_525398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_525398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_525398 prefixEnd_525398 := by exact prefixLift 525398
  have htrace : WordTrace (prefixWord ++ tailWord_525398) baseStart_525398 baseEnd_525398 := by
    simpa [prefixWord, tailWord_525398, baseEnd_525398] using wordTrace_append hprefix tailTrace_525398
  have hstable : (prefixWord ++ tailWord_525398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_525398).length < 2 ^ (prefixWord ++ tailWord_525398).sum := by decide
  have hdescent : baseEnd_525398 < baseStart_525398 := by decide
  rcases family_descends (prefixWord ++ tailWord_525398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_525407 : List Nat := [1, 1, 2, 3, 1, 1, 4, 2, 1, 4, 3]
def baseStart_525407 : Nat := 118140960795 + 525407 * 2 ^ 59
def prefixEnd_525407 : Nat := 4983230072969 + 3 ^ 40 * 525407 * 2
def baseEnd_525407 : Nat := 269786330236931076396203

theorem tailTrace_525407 : CollatzResearch.WordTrace tailWord_525407 prefixEnd_525407 269786330236931076396203 := by
  unfold tailWord_525407
  simp only [CollatzResearch.WordTrace]
  refine ⟨19163167607547646216750475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12775445071698430811166983 19163167607547646216750475)
  ·
    refine ⟨28744751411321469325125713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19163167607547646216750475 28744751411321469325125713)
    ·
      refine ⟨21558563558491101993844285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28744751411321469325125713 21558563558491101993844285)
      ·
        refine ⟨8084461334434163247691607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21558563558491101993844285 8084461334434163247691607)
        ·
          refine ⟨12126692001651244871537411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8084461334434163247691607 12126692001651244871537411)
          ·
            refine ⟨18190038002476867307306117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12126692001651244871537411 18190038002476867307306117)
            ·
              refine ⟨3410632125464412620119897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18190038002476867307306117 3410632125464412620119897)
              ·
                refine ⟨2557974094098309465089923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3410632125464412620119897 2557974094098309465089923)
                ·
                  refine ⟨3836961141147464197634885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2557974094098309465089923 3836961141147464197634885)
                  ·
                    refine ⟨719430213965149537056541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3836961141147464197634885 719430213965149537056541)
                    ·
                      refine ⟨269786330236931076396203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 719430213965149537056541 269786330236931076396203)
                      ·
                        rfl

theorem cell23_525407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 2, 1, 4, 3].length) (baseStart_525407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_525407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_525407 prefixEnd_525407 := by exact prefixLift 525407
  have htrace : WordTrace (prefixWord ++ tailWord_525407) baseStart_525407 baseEnd_525407 := by
    simpa [prefixWord, tailWord_525407, baseEnd_525407] using wordTrace_append hprefix tailTrace_525407
  have hstable : (prefixWord ++ tailWord_525407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_525407).length < 2 ^ (prefixWord ++ tailWord_525407).sum := by decide
  have hdescent : baseEnd_525407 < baseStart_525407 := by decide
  rcases family_descends (prefixWord ++ tailWord_525407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_525421 : List Nat := [1, 5, 1, 1, 2, 4, 1, 1, 2, 1, 4]
def baseStart_525421 : Nat := 118140960795 + 525421 * 2 ^ 59
def prefixEnd_525421 : Nat := 4983230072969 + 3 ^ 40 * 525421 * 2
def baseEnd_525421 : Nat := 269793518966094021621139

theorem tailTrace_525421 : CollatzResearch.WordTrace tailWord_525421 prefixEnd_525421 269793518966094021621139 := by
  unfold tailWord_525421
  simp only [CollatzResearch.WordTrace]
  refine ⟨19163678229496926607760117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12775785486331284405173411 19163678229496926607760117)
  ·
    refine ⟨1796594834015336869477511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 19163678229496926607760117 1796594834015336869477511)
    ·
      refine ⟨2694892251023005304216267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1796594834015336869477511 2694892251023005304216267)
      ·
        refine ⟨4042338376534507956324401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2694892251023005304216267 4042338376534507956324401)
        ·
          refine ⟨3031753782400880967243301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4042338376534507956324401 3031753782400880967243301)
          ·
            refine ⟨568453834200165181358119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3031753782400880967243301 568453834200165181358119)
            ·
              refine ⟨852680751300247772037179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 568453834200165181358119 852680751300247772037179)
              ·
                refine ⟨1279021126950371658055769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 852680751300247772037179 1279021126950371658055769)
                ·
                  refine ⟨959265845212778743541827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1279021126950371658055769 959265845212778743541827)
                  ·
                    refine ⟨1438898767819168115312741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 959265845212778743541827 1438898767819168115312741)
                    ·
                      refine ⟨269793518966094021621139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1438898767819168115312741 269793518966094021621139)
                      ·
                        rfl

theorem cell23_525421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 1, 1, 2, 1, 4].length) (baseStart_525421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_525421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_525421 prefixEnd_525421 := by exact prefixLift 525421
  have htrace : WordTrace (prefixWord ++ tailWord_525421) baseStart_525421 baseEnd_525421 := by
    simpa [prefixWord, tailWord_525421, baseEnd_525421] using wordTrace_append hprefix tailTrace_525421
  have hstable : (prefixWord ++ tailWord_525421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_525421).length < 2 ^ (prefixWord ++ tailWord_525421).sum := by decide
  have hdescent : baseEnd_525421 < baseStart_525421 := by decide
  rcases family_descends (prefixWord ++ tailWord_525421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_525431 : List Nat := [1, 1, 3, 1, 1, 4, 4, 3, 1, 4]
def baseStart_525431 : Nat := 118140960795 + 525431 * 2 ^ 59
def prefixEnd_525431 : Nat := 4983230072969 + 3 ^ 40 * 525431 * 2
def baseEnd_525431 : Nat := 89932884590879660832031

theorem tailTrace_525431 : CollatzResearch.WordTrace tailWord_525431 prefixEnd_525431 89932884590879660832031 := by
  unfold tailWord_525431
  simp only [CollatzResearch.WordTrace]
  refine ⟨19164042959460698315624147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12776028639640465543749431 19164042959460698315624147)
  ·
    refine ⟨28746064439191047473436221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19164042959460698315624147 28746064439191047473436221)
    ·
      refine ⟨10779774164696642802538583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28746064439191047473436221 10779774164696642802538583)
      ·
        refine ⟨16169661247044964203807875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10779774164696642802538583 16169661247044964203807875)
        ·
          refine ⟨24254491870567446305711813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16169661247044964203807875 24254491870567446305711813)
          ·
            refine ⟨4547717225731396182320965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24254491870567446305711813 4547717225731396182320965)
            ·
              refine ⟨852696979824636784185181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4547717225731396182320965 852696979824636784185181)
              ·
                refine ⟨319761367434238794069443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 852696979824636784185181 319761367434238794069443)
                ·
                  refine ⟨479642051151358191104165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 319761367434238794069443 479642051151358191104165)
                  ·
                    refine ⟨89932884590879660832031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 479642051151358191104165 89932884590879660832031)
                    ·
                      rfl

theorem cell23_525431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 4, 3, 1, 4].length) (baseStart_525431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_525431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_525431 prefixEnd_525431 := by exact prefixLift 525431
  have htrace : WordTrace (prefixWord ++ tailWord_525431) baseStart_525431 baseEnd_525431 := by
    simpa [prefixWord, tailWord_525431, baseEnd_525431] using wordTrace_append hprefix tailTrace_525431
  have hstable : (prefixWord ++ tailWord_525431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_525431).length < 2 ^ (prefixWord ++ tailWord_525431).sum := by decide
  have hdescent : baseEnd_525431 < baseStart_525431 := by decide
  rcases family_descends (prefixWord ++ tailWord_525431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_525444 : List Nat := [2, 3, 2, 1, 2, 2, 3, 2, 6]
def baseStart_525444 : Nat := 118140960795 + 525444 * 2 ^ 59
def prefixEnd_525444 : Nat := 4983230072969 + 3 ^ 40 * 525444 * 2
def baseEnd_525444 : Nat := 29978369891238603514837

theorem tailTrace_525444 : CollatzResearch.WordTrace tailWord_525444 prefixEnd_525444 29978369891238603514837 := by
  unfold tailWord_525444
  simp only [CollatzResearch.WordTrace]
  refine ⟨9582258554206800767923693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12776344738942401023898257 9582258554206800767923693)
  ·
    refine ⟨3593346957827550287971385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9582258554206800767923693 3593346957827550287971385)
    ·
      refine ⟨2695010218370662715978539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3593346957827550287971385 2695010218370662715978539)
      ·
        refine ⟨4042515327555994073967809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2695010218370662715978539 4042515327555994073967809)
        ·
          refine ⟨3031886495666995555475857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4042515327555994073967809 3031886495666995555475857)
          ·
            refine ⟨2273914871750246666606893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3031886495666995555475857 2273914871750246666606893)
            ·
              refine ⟨852718076906342499977585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2273914871750246666606893 852718076906342499977585)
              ·
                refine ⟨639538557679756874983189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 852718076906342499977585 639538557679756874983189)
                ·
                  refine ⟨29978369891238603514837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 639538557679756874983189 29978369891238603514837)
                  ·
                    rfl

theorem cell23_525444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 3, 2, 6].length) (baseStart_525444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_525444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_525444 prefixEnd_525444 := by exact prefixLift 525444
  have htrace : WordTrace (prefixWord ++ tailWord_525444) baseStart_525444 baseEnd_525444 := by
    simpa [prefixWord, tailWord_525444, baseEnd_525444] using wordTrace_append hprefix tailTrace_525444
  have hstable : (prefixWord ++ tailWord_525444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_525444).length < 2 ^ (prefixWord ++ tailWord_525444).sum := by decide
  have hdescent : baseEnd_525444 < baseStart_525444 := by decide
  rcases family_descends (prefixWord ++ tailWord_525444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_525487 : List Nat := [1, 1, 2, 1, 2, 3, 2, 4, 1, 6]
def baseStart_525487 : Nat := 118140960795 + 525487 * 2 ^ 59
def prefixEnd_525487 : Nat := 4983230072969 + 3 ^ 40 * 525487 * 2
def baseEnd_525487 : Nat := 89942469563096921131945

theorem tailTrace_525487 : CollatzResearch.WordTrace tailWord_525487 prefixEnd_525487 89942469563096921131945 := by
  unfold tailWord_525487
  simp only [CollatzResearch.WordTrace]
  refine ⟨19166085447257819879662715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12777390298171879919775143 19166085447257819879662715)
  ·
    refine ⟨28749128170886729819494073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19166085447257819879662715 28749128170886729819494073)
    ·
      refine ⟨21561846128165047364620555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28749128170886729819494073 21561846128165047364620555)
      ·
        refine ⟨32342769192247571046930833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21561846128165047364620555 32342769192247571046930833)
        ·
          refine ⟨24257076894185678285198125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32342769192247571046930833 24257076894185678285198125)
          ·
            refine ⟨9096403835319629356949297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24257076894185678285198125 9096403835319629356949297)
            ·
              refine ⟨6822302876489722017711973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9096403835319629356949297 6822302876489722017711973)
              ·
                refine ⟨1279181789341822878320995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6822302876489722017711973 1279181789341822878320995)
                ·
                  refine ⟨1918772684012734317481493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1279181789341822878320995 1918772684012734317481493)
                  ·
                    refine ⟨89942469563096921131945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1918772684012734317481493 89942469563096921131945)
                    ·
                      rfl

theorem cell23_525487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 4, 1, 6].length) (baseStart_525487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_525487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_525487 prefixEnd_525487 := by exact prefixLift 525487
  have htrace : WordTrace (prefixWord ++ tailWord_525487) baseStart_525487 baseEnd_525487 := by
    simpa [prefixWord, tailWord_525487, baseEnd_525487] using wordTrace_append hprefix tailTrace_525487
  have hstable : (prefixWord ++ tailWord_525487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_525487).length < 2 ^ (prefixWord ++ tailWord_525487).sum := by decide
  have hdescent : baseEnd_525487 < baseStart_525487 := by decide
  rcases family_descends (prefixWord ++ tailWord_525487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_525505 : List Nat := [1, 2, 6, 1, 1, 3, 1, 1, 3, 1, 3]
def baseStart_525505 : Nat := 118140960795 + 525505 * 2 ^ 59
def prefixEnd_525505 : Nat := 4983230072969 + 3 ^ 40 * 525505 * 2
def baseEnd_525505 : Nat := 269836651341071692970753

theorem tailTrace_525505 : CollatzResearch.WordTrace tailWord_525505 prefixEnd_525505 269836651341071692970753 := by
  unfold tailWord_525505
  simp only [CollatzResearch.WordTrace]
  refine ⟨19166741961192608953817969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12777827974128405969211979 19166741961192608953817969)
  ·
    refine ⟨14375056470894456715363477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19166741961192608953817969 14375056470894456715363477)
    ·
      refine ⟨673830772073177658532663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 14375056470894456715363477 673830772073177658532663)
      ·
        refine ⟨1010746158109766487798995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 673830772073177658532663 1010746158109766487798995)
        ·
          refine ⟨1516119237164649731698493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1010746158109766487798995 1516119237164649731698493)
          ·
            refine ⟨568544713936743649386935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1516119237164649731698493 568544713936743649386935)
            ·
              refine ⟨852817070905115474080403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 568544713936743649386935 852817070905115474080403)
              ·
                refine ⟨1279225606357673211120605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 852817070905115474080403 1279225606357673211120605)
                ·
                  refine ⟨479709602384127454170227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1279225606357673211120605 479709602384127454170227)
                  ·
                    refine ⟨719564403576191181255341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 479709602384127454170227 719564403576191181255341)
                    ·
                      refine ⟨269836651341071692970753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 719564403576191181255341 269836651341071692970753)
                      ·
                        rfl

theorem cell23_525505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 1, 1, 3, 1, 3].length) (baseStart_525505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_525505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_525505 prefixEnd_525505 := by exact prefixLift 525505
  have htrace : WordTrace (prefixWord ++ tailWord_525505) baseStart_525505 baseEnd_525505 := by
    simpa [prefixWord, tailWord_525505, baseEnd_525505] using wordTrace_append hprefix tailTrace_525505
  have hstable : (prefixWord ++ tailWord_525505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_525505).length < 2 ^ (prefixWord ++ tailWord_525505).sum := by decide
  have hdescent : baseEnd_525505 < baseStart_525505 := by decide
  rcases family_descends (prefixWord ++ tailWord_525505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_525507 : List Nat := [1, 1, 1, 3, 1, 1, 1, 3, 5, 2, 4]
def baseStart_525507 : Nat := 118140960795 + 525507 * 2 ^ 59
def prefixEnd_525507 : Nat := 4983230072969 + 3 ^ 40 * 525507 * 2
def baseEnd_525507 : Nat := 269837678302380685145743

theorem tailTrace_525507 : CollatzResearch.WordTrace tailWord_525507 prefixEnd_525507 269837678302380685145743 := by
  unfold tailWord_525507
  simp only [CollatzResearch.WordTrace]
  refine ⟨19166814907185363295390775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12777876604790242196927183 19166814907185363295390775)
  ·
    refine ⟨28750222360778044943086163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19166814907185363295390775 28750222360778044943086163)
    ·
      refine ⟨43125333541167067414629245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28750222360778044943086163 43125333541167067414629245)
      ·
        refine ⟨16172000077937650280485967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43125333541167067414629245 16172000077937650280485967)
        ·
          refine ⟨24258000116906475420728951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16172000077937650280485967 24258000116906475420728951)
          ·
            refine ⟨36387000175359713131093427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24258000116906475420728951 36387000175359713131093427)
            ·
              refine ⟨54580500263039569696640141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36387000175359713131093427 54580500263039569696640141)
              ·
                refine ⟨20467687598639838636240053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54580500263039569696640141 20467687598639838636240053)
                ·
                  refine ⟨1918845712372484872147505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20467687598639838636240053 1918845712372484872147505)
                  ·
                    refine ⟨1439134284279363654110629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1918845712372484872147505 1439134284279363654110629)
                    ·
                      refine ⟨269837678302380685145743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1439134284279363654110629 269837678302380685145743)
                      ·
                        rfl

theorem cell23_525507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 3, 5, 2, 4].length) (baseStart_525507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_525507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_525507 prefixEnd_525507 := by exact prefixLift 525507
  have htrace : WordTrace (prefixWord ++ tailWord_525507) baseStart_525507 baseEnd_525507 := by
    simpa [prefixWord, tailWord_525507, baseEnd_525507] using wordTrace_append hprefix tailTrace_525507
  have hstable : (prefixWord ++ tailWord_525507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_525507).length < 2 ^ (prefixWord ++ tailWord_525507).sum := by decide
  have hdescent : baseEnd_525507 < baseStart_525507 := by decide
  rcases family_descends (prefixWord ++ tailWord_525507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_525514 : List Nat := [3, 1, 2, 1, 3, 2, 2, 2, 1, 1, 5]
def baseStart_525514 : Nat := 118140960795 + 525514 * 2 ^ 59
def prefixEnd_525514 : Nat := 4983230072969 + 3 ^ 40 * 525514 * 2
def baseEnd_525514 : Nat := 269841272666962157758211

theorem tailTrace_525514 : CollatzResearch.WordTrace tailWord_525514 prefixEnd_525514 269841272666962157758211 := by
  unfold tailWord_525514
  simp only [CollatzResearch.WordTrace]
  refine ⟨4791767554540000872723899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12778046812106668993930397 4791767554540000872723899)
  ·
    refine ⟨7187651331810001309085849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4791767554540000872723899 7187651331810001309085849)
    ·
      refine ⟨5390738498857500981814387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7187651331810001309085849 5390738498857500981814387)
      ·
        refine ⟨8086107748286251472721581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5390738498857500981814387 8086107748286251472721581)
        ·
          refine ⟨3032290405607344302270593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8086107748286251472721581 3032290405607344302270593)
          ·
            refine ⟨2274217804205508226702945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3032290405607344302270593 2274217804205508226702945)
            ·
              refine ⟨1705663353154131170027209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2274217804205508226702945 1705663353154131170027209)
              ·
                refine ⟨1279247514865598377520407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1705663353154131170027209 1279247514865598377520407)
                ·
                  refine ⟨1918871272298397566280611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1279247514865598377520407 1918871272298397566280611)
                  ·
                    refine ⟨2878306908447596349420917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1918871272298397566280611 2878306908447596349420917)
                    ·
                      refine ⟨269841272666962157758211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2878306908447596349420917 269841272666962157758211)
                      ·
                        rfl

theorem cell23_525514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 2, 2, 1, 1, 5].length) (baseStart_525514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_525514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_525514 prefixEnd_525514 := by exact prefixLift 525514
  have htrace : WordTrace (prefixWord ++ tailWord_525514) baseStart_525514 baseEnd_525514 := by
    simpa [prefixWord, tailWord_525514, baseEnd_525514] using wordTrace_append hprefix tailTrace_525514
  have hstable : (prefixWord ++ tailWord_525514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_525514).length < 2 ^ (prefixWord ++ tailWord_525514).sum := by decide
  have hdescent : baseEnd_525514 < baseStart_525514 := by decide
  rcases family_descends (prefixWord ++ tailWord_525514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_525528 : List Nat := [2, 1, 2, 2, 5, 2, 1, 2, 1, 1, 4]
def baseStart_525528 : Nat := 118140960795 + 525528 * 2 ^ 59
def prefixEnd_525528 : Nat := 4983230072969 + 3 ^ 40 * 525528 * 2
def baseEnd_525528 : Nat := 269848461396125102983147

theorem tailTrace_525528 : CollatzResearch.WordTrace tailWord_525528 prefixEnd_525528 269848461396125102983147 := by
  unfold tailWord_525528
  simp only [CollatzResearch.WordTrace]
  refine ⟨9583790420054641940952619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12778387226739522587936825 9583790420054641940952619)
  ·
    refine ⟨14375685630081962911428929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9583790420054641940952619 14375685630081962911428929)
    ·
      refine ⟨10781764222561472183571697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14375685630081962911428929 10781764222561472183571697)
      ·
        refine ⟨8086323166921104137678773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10781764222561472183571697 8086323166921104137678773)
        ·
          refine ⟨758092796898853512907385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8086323166921104137678773 758092796898853512907385)
          ·
            refine ⟨568569597674140134680539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 758092796898853512907385 568569597674140134680539)
            ·
              refine ⟨852854396511210202020809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 568569597674140134680539 852854396511210202020809)
              ·
                refine ⟨639640797383407651515607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 852854396511210202020809 639640797383407651515607)
                ·
                  refine ⟨959461196075111477273411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 639640797383407651515607 959461196075111477273411)
                  ·
                    refine ⟨1439191794112667215910117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 959461196075111477273411 1439191794112667215910117)
                    ·
                      refine ⟨269848461396125102983147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1439191794112667215910117 269848461396125102983147)
                      ·
                        rfl

theorem cell23_525528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 1, 2, 1, 1, 4].length) (baseStart_525528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_525528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_525528 prefixEnd_525528 := by exact prefixLift 525528
  have htrace : WordTrace (prefixWord ++ tailWord_525528) baseStart_525528 baseEnd_525528 := by
    simpa [prefixWord, tailWord_525528, baseEnd_525528] using wordTrace_append hprefix tailTrace_525528
  have hstable : (prefixWord ++ tailWord_525528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_525528).length < 2 ^ (prefixWord ++ tailWord_525528).sum := by decide
  have hdescent : baseEnd_525528 < baseStart_525528 := by decide
  rcases family_descends (prefixWord ++ tailWord_525528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_525541 : List Nat := [1, 3, 1, 4, 3, 1, 1, 2, 1, 2, 4]
def baseStart_525541 : Nat := 118140960795 + 525541 * 2 ^ 59
def prefixEnd_525541 : Nat := 4983230072969 + 3 ^ 40 * 525541 * 2
def baseEnd_525541 : Nat := 269855136644633552120587

theorem tailTrace_525541 : CollatzResearch.WordTrace tailWord_525541 prefixEnd_525541 269855136644633552120587 := by
  unfold tailWord_525541
  simp only [CollatzResearch.WordTrace]
  refine ⟨19168054989062187102128477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12778703326041458068085651 19168054989062187102128477)
  ·
    refine ⟨7188020620898320163298179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19168054989062187102128477 7188020620898320163298179)
    ·
      refine ⟨10782030931347480244947269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7188020620898320163298179 10782030931347480244947269)
      ·
        refine ⟨2021630799627652545927613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10782030931347480244947269 2021630799627652545927613)
        ·
          refine ⟨758111549860369704722855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2021630799627652545927613 758111549860369704722855)
          ·
            refine ⟨1137167324790554557084283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 758111549860369704722855 1137167324790554557084283)
            ·
              refine ⟨1705750987185831835626425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1137167324790554557084283 1705750987185831835626425)
              ·
                refine ⟨1279313240389373876719819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1705750987185831835626425 1279313240389373876719819)
                ·
                  refine ⟨1918969860584060815079729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1279313240389373876719819 1918969860584060815079729)
                  ·
                    refine ⟨1439227395438045611309797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1918969860584060815079729 1439227395438045611309797)
                    ·
                      refine ⟨269855136644633552120587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1439227395438045611309797 269855136644633552120587)
                      ·
                        rfl

theorem cell23_525541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 1, 2, 1, 2, 4].length) (baseStart_525541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_525541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_525541 prefixEnd_525541 := by exact prefixLift 525541
  have htrace : WordTrace (prefixWord ++ tailWord_525541) baseStart_525541 baseEnd_525541 := by
    simpa [prefixWord, tailWord_525541, baseEnd_525541] using wordTrace_append hprefix tailTrace_525541
  have hstable : (prefixWord ++ tailWord_525541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_525541).length < 2 ^ (prefixWord ++ tailWord_525541).sum := by decide
  have hdescent : baseEnd_525541 < baseStart_525541 := by decide
  rcases family_descends (prefixWord ++ tailWord_525541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_525548 : List Nat := [2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 3]
def baseStart_525548 : Nat := 118140960795 + 525548 * 2 ^ 59
def prefixEnd_525548 : Nat := 4983230072969 + 3 ^ 40 * 525548 * 2
def baseEnd_525548 : Nat := 269858731009215024733055

theorem tailTrace_525548 : CollatzResearch.WordTrace tailWord_525548 prefixEnd_525548 269858731009215024733055 := by
  unfold tailWord_525548
  simp only [CollatzResearch.WordTrace]
  refine ⟨9584155150018413648816649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12778873533357884865088865 9584155150018413648816649)
  ·
    refine ⟨7188116362513810236612487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9584155150018413648816649 7188116362513810236612487)
    ·
      refine ⟨10782174543770715354918731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7188116362513810236612487 10782174543770715354918731)
      ·
        refine ⟨16173261815656073032378097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10782174543770715354918731 16173261815656073032378097)
        ·
          refine ⟨12129946361742054774283573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16173261815656073032378097 12129946361742054774283573)
          ·
            refine ⟨1137182471413317635089085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12129946361742054774283573 1137182471413317635089085)
            ·
              refine ⟨426443426779994113158407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1137182471413317635089085 426443426779994113158407)
              ·
                refine ⟨639665140169991169737611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 426443426779994113158407 639665140169991169737611)
                ·
                  refine ⟨959497710254986754606417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 639665140169991169737611 959497710254986754606417)
                  ·
                    refine ⟨719623282691240065954813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 959497710254986754606417 719623282691240065954813)
                    ·
                      refine ⟨269858731009215024733055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 719623282691240065954813 269858731009215024733055)
                      ·
                        rfl

theorem cell23_525548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 3].length) (baseStart_525548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_525548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_525548 prefixEnd_525548 := by exact prefixLift 525548
  have htrace : WordTrace (prefixWord ++ tailWord_525548) baseStart_525548 baseEnd_525548 := by
    simpa [prefixWord, tailWord_525548, baseEnd_525548] using wordTrace_append hprefix tailTrace_525548
  have hstable : (prefixWord ++ tailWord_525548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_525548).length < 2 ^ (prefixWord ++ tailWord_525548).sum := by decide
  have hdescent : baseEnd_525548 < baseStart_525548 := by decide
  rcases family_descends (prefixWord ++ tailWord_525548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_525571 : List Nat := [1, 1, 1, 3, 2, 4, 1, 2, 3, 3, 2]
def baseStart_525571 : Nat := 118140960795 + 525571 * 2 ^ 59
def prefixEnd_525571 : Nat := 4983230072969 + 3 ^ 40 * 525571 * 2
def baseEnd_525571 : Nat := 269870541064268434745449

theorem tailTrace_525571 : CollatzResearch.WordTrace tailWord_525571 prefixEnd_525571 269870541064268434745449 := by
  unfold tailWord_525571
  simp only [CollatzResearch.WordTrace]
  refine ⟨19169149178953502225720567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12779432785969001483813711 19169149178953502225720567)
  ·
    refine ⟨28753723768430253338580851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19169149178953502225720567 28753723768430253338580851)
    ·
      refine ⟨43130585652645380007871277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28753723768430253338580851 43130585652645380007871277)
      ·
        refine ⟨16173969619742017502951729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43130585652645380007871277 16173969619742017502951729)
        ·
          refine ⟨12130477214806513127213797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16173969619742017502951729 12130477214806513127213797)
          ·
            refine ⟨2274464477776221211352587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12130477214806513127213797 2274464477776221211352587)
            ·
              refine ⟨3411696716664331817028881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2274464477776221211352587 3411696716664331817028881)
              ·
                refine ⟨2558772537498248862771661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3411696716664331817028881 2558772537498248862771661)
                ·
                  refine ⟨959539701561843323539373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2558772537498248862771661 959539701561843323539373)
                  ·
                    refine ⟨359827388085691246327265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 959539701561843323539373 359827388085691246327265)
                    ·
                      refine ⟨269870541064268434745449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 359827388085691246327265 269870541064268434745449)
                      ·
                        rfl

theorem cell23_525571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 2, 3, 3, 2].length) (baseStart_525571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_525571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_525571 prefixEnd_525571 := by exact prefixLift 525571
  have htrace : WordTrace (prefixWord ++ tailWord_525571) baseStart_525571 baseEnd_525571 := by
    simpa [prefixWord, tailWord_525571, baseEnd_525571] using wordTrace_append hprefix tailTrace_525571
  have hstable : (prefixWord ++ tailWord_525571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_525571).length < 2 ^ (prefixWord ++ tailWord_525571).sum := by decide
  have hdescent : baseEnd_525571 < baseStart_525571 := by decide
  rcases family_descends (prefixWord ++ tailWord_525571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_525604 : List Nat := [2, 3, 1, 3, 1, 1, 2, 1, 1, 3, 5]
def baseStart_525604 : Nat := 118140960795 + 525604 * 2 ^ 59
def prefixEnd_525604 : Nat := 4983230072969 + 3 ^ 40 * 525604 * 2
def baseEnd_525604 : Nat := 269887485925866805632797

theorem tailTrace_525604 : CollatzResearch.WordTrace tailWord_525604 prefixEnd_525604 269887485925866805632797 := by
  unfold tailWord_525604
  simp only [CollatzResearch.WordTrace]
  refine ⟨9585176393916974430835933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12780235191889299241114577 9585176393916974430835933)
  ·
    refine ⟨3594441147718865411563475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9585176393916974430835933 3594441147718865411563475)
    ·
      refine ⟨5391661721578298117345213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3594441147718865411563475 5391661721578298117345213)
      ·
        refine ⟨2021873145591861794004455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5391661721578298117345213 2021873145591861794004455)
        ·
          refine ⟨3032809718387792691006683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2021873145591861794004455 3032809718387792691006683)
          ·
            refine ⟨4549214577581689036510025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3032809718387792691006683 4549214577581689036510025)
            ·
              refine ⟨3411910933186266777382519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4549214577581689036510025 3411910933186266777382519)
              ·
                refine ⟨5117866399779400166073779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3411910933186266777382519 5117866399779400166073779)
                ·
                  refine ⟨7676799599669100249110669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5117866399779400166073779 7676799599669100249110669)
                  ·
                    refine ⟨2878799849875912593416501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7676799599669100249110669 2878799849875912593416501)
                    ·
                      refine ⟨269887485925866805632797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2878799849875912593416501 269887485925866805632797)
                      ·
                        rfl

theorem cell23_525604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 1, 1, 3, 5].length) (baseStart_525604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_525604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_525604 prefixEnd_525604 := by exact prefixLift 525604
  have htrace : WordTrace (prefixWord ++ tailWord_525604) baseStart_525604 baseEnd_525604 := by
    simpa [prefixWord, tailWord_525604, baseEnd_525604] using wordTrace_append hprefix tailTrace_525604
  have hstable : (prefixWord ++ tailWord_525604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_525604).length < 2 ^ (prefixWord ++ tailWord_525604).sum := by decide
  have hdescent : baseEnd_525604 < baseStart_525604 := by decide
  rcases family_descends (prefixWord ++ tailWord_525604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_525605 : List Nat := [1, 3, 1, 2, 4, 1, 4, 1, 1, 3, 2]
def baseStart_525605 : Nat := 118140960795 + 525605 * 2 ^ 59
def prefixEnd_525605 : Nat := 4983230072969 + 3 ^ 40 * 525605 * 2
def baseEnd_525605 : Nat := 269887999406521301720293

theorem tailTrace_525605 : CollatzResearch.WordTrace tailWord_525605 prefixEnd_525605 269887999406521301720293 := by
  unfold tailWord_525605
  simp only [CollatzResearch.WordTrace]
  refine ⟨19170389260830326032458269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12780259507220217354972179 19170389260830326032458269)
  ·
    refine ⟨7188895972811372262171851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19170389260830326032458269 7188895972811372262171851)
    ·
      refine ⟨10783343959217058393257777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7188895972811372262171851 10783343959217058393257777)
      ·
        refine ⟨8087507969412793794943333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10783343959217058393257777 8087507969412793794943333)
        ·
          refine ⟨1516407744264898836551875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8087507969412793794943333 1516407744264898836551875)
          ·
            refine ⟨2274611616397348254827813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1516407744264898836551875 2274611616397348254827813)
            ·
              refine ⟨426489678074502797780215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2274611616397348254827813 426489678074502797780215)
              ·
                refine ⟨639734517111754196670323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 426489678074502797780215 639734517111754196670323)
                ·
                  refine ⟨959601775667631295005485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 639734517111754196670323 959601775667631295005485)
                  ·
                    refine ⟨359850665875361735627057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 959601775667631295005485 359850665875361735627057)
                    ·
                      refine ⟨269887999406521301720293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 359850665875361735627057 269887999406521301720293)
                      ·
                        rfl

theorem cell23_525605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 4, 1, 1, 3, 2].length) (baseStart_525605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_525605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_525605 prefixEnd_525605 := by exact prefixLift 525605
  have htrace : WordTrace (prefixWord ++ tailWord_525605) baseStart_525605 baseEnd_525605 := by
    simpa [prefixWord, tailWord_525605, baseEnd_525605] using wordTrace_append hprefix tailTrace_525605
  have hstable : (prefixWord ++ tailWord_525605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_525605).length < 2 ^ (prefixWord ++ tailWord_525605).sum := by decide
  have hdescent : baseEnd_525605 < baseStart_525605 := by decide
  rcases family_descends (prefixWord ++ tailWord_525605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_525691 : List Nat := [1, 1, 1, 1, 1, 6, 2, 1, 1, 6, 2]
def baseStart_525691 : Nat := 118140960795 + 525691 * 2 ^ 59
def prefixEnd_525691 : Nat := 4983230072969 + 3 ^ 40 * 525691 * 2
def baseEnd_525691 : Nat := 269932158742807965244897

theorem tailTrace_525691 : CollatzResearch.WordTrace tailWord_525691 prefixEnd_525691 269932158742807965244897 := by
  unfold tailWord_525691
  simp only [CollatzResearch.WordTrace]
  refine ⟨19173525938518762720088927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12782350625679175146725951 19173525938518762720088927)
  ·
    refine ⟨28760288907778144080133391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19173525938518762720088927 28760288907778144080133391)
    ·
      refine ⟨43140433361667216120200087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28760288907778144080133391 43140433361667216120200087)
      ·
        refine ⟨64710650042500824180300131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43140433361667216120200087 64710650042500824180300131)
        ·
          refine ⟨97065975063751236270450197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64710650042500824180300131 97065975063751236270450197)
          ·
            refine ⟨4549967581113339200177353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 97065975063751236270450197 4549967581113339200177353)
            ·
              refine ⟨3412475685835004400133015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4549967581113339200177353 3412475685835004400133015)
              ·
                refine ⟨5118713528752506600199523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3412475685835004400133015 5118713528752506600199523)
                ·
                  refine ⟨7678070293128759900299285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5118713528752506600199523 7678070293128759900299285)
                  ·
                    refine ⟨359909544990410620326529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7678070293128759900299285 359909544990410620326529)
                    ·
                      refine ⟨269932158742807965244897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 359909544990410620326529 269932158742807965244897)
                      ·
                        rfl

theorem cell23_525691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 1, 1, 6, 2].length) (baseStart_525691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_525691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_525691 prefixEnd_525691 := by exact prefixLift 525691
  have htrace : WordTrace (prefixWord ++ tailWord_525691) baseStart_525691 baseEnd_525691 := by
    simpa [prefixWord, tailWord_525691, baseEnd_525691] using wordTrace_append hprefix tailTrace_525691
  have hstable : (prefixWord ++ tailWord_525691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_525691).length < 2 ^ (prefixWord ++ tailWord_525691).sum := by decide
  have hdescent : baseEnd_525691 < baseStart_525691 := by decide
  rcases family_descends (prefixWord ++ tailWord_525691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_525701 : List Nat := [1, 3, 1, 1, 3, 1, 2, 4, 3, 4]
def baseStart_525701 : Nat := 118140960795 + 525701 * 2 ^ 59
def prefixEnd_525701 : Nat := 4983230072969 + 3 ^ 40 * 525701 * 2
def baseEnd_525701 : Nat := 89979097849784308706617

theorem tailTrace_525701 : CollatzResearch.WordTrace tailWord_525701 prefixEnd_525701 89979097849784308706617 := by
  unfold tailWord_525701
  simp only [CollatzResearch.WordTrace]
  refine ⟨19173890668482534427952957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12782593778988356285301971 19173890668482534427952957)
  ·
    refine ⟨7190209000680950410482359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19173890668482534427952957 7190209000680950410482359)
    ·
      refine ⟨10785313501021425615723539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7190209000680950410482359 10785313501021425615723539)
      ·
        refine ⟨16177970251532138423585309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10785313501021425615723539 16177970251532138423585309)
        ·
          refine ⟨6066738844324551908844491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16177970251532138423585309 6066738844324551908844491)
          ·
            refine ⟨9100108266486827863266737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6066738844324551908844491 9100108266486827863266737)
            ·
              refine ⟨6825081199865120897450053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9100108266486827863266737 6825081199865120897450053)
              ·
                refine ⟨1279702724974710168271885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6825081199865120897450053 1279702724974710168271885)
                ·
                  refine ⟨479888521865516313101957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1279702724974710168271885 479888521865516313101957)
                  ·
                    refine ⟨89979097849784308706617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 479888521865516313101957 89979097849784308706617)
                    ·
                      rfl

theorem cell23_525701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 4, 3, 4].length) (baseStart_525701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_525701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_525701 prefixEnd_525701 := by exact prefixLift 525701
  have htrace : WordTrace (prefixWord ++ tailWord_525701) baseStart_525701 baseEnd_525701 := by
    simpa [prefixWord, tailWord_525701, baseEnd_525701] using wordTrace_append hprefix tailTrace_525701
  have hstable : (prefixWord ++ tailWord_525701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_525701).length < 2 ^ (prefixWord ++ tailWord_525701).sum := by decide
  have hdescent : baseEnd_525701 < baseStart_525701 := by decide
  rcases family_descends (prefixWord ++ tailWord_525701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_525731 : List Nat := [1, 1, 1, 4, 1, 3, 4, 2, 6]
def baseStart_525731 : Nat := 118140960795 + 525731 * 2 ^ 59
def prefixEnd_525731 : Nat := 4983230072969 + 3 ^ 40 * 525731 * 2
def baseEnd_525731 : Nat := 29994744218776423193857

theorem tailTrace_525731 : CollatzResearch.WordTrace tailWord_525731 prefixEnd_525731 29994744218776423193857 := by
  unfold tailWord_525731
  simp only [CollatzResearch.WordTrace]
  refine ⟨19174984858373849551545047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12783323238915899701030031 19174984858373849551545047)
  ·
    refine ⟨28762477287560774327317571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19174984858373849551545047 28762477287560774327317571)
    ·
      refine ⟨43143715931341161490976357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28762477287560774327317571 43143715931341161490976357)
      ·
        refine ⟨8089446737126467779558067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43143715931341161490976357 8089446737126467779558067)
        ·
          refine ⟨12134170105689701669337101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8089446737126467779558067 12134170105689701669337101)
          ·
            refine ⟨4550313789633638126001413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12134170105689701669337101 4550313789633638126001413)
            ·
              refine ⟨853183835556307148625265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4550313789633638126001413 853183835556307148625265)
              ·
                refine ⟨639887876667230361468949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 853183835556307148625265 639887876667230361468949)
                ·
                  refine ⟨29994744218776423193857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 639887876667230361468949 29994744218776423193857)
                  ·
                    rfl

theorem cell23_525731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 4, 2, 6].length) (baseStart_525731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_525731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_525731 prefixEnd_525731 := by exact prefixLift 525731
  have htrace : WordTrace (prefixWord ++ tailWord_525731) baseStart_525731 baseEnd_525731 := by
    simpa [prefixWord, tailWord_525731, baseEnd_525731] using wordTrace_append hprefix tailTrace_525731
  have hstable : (prefixWord ++ tailWord_525731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_525731).length < 2 ^ (prefixWord ++ tailWord_525731).sum := by decide
  have hdescent : baseEnd_525731 < baseStart_525731 := by decide
  rcases family_descends (prefixWord ++ tailWord_525731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_525735 : List Nat := [1, 1, 6, 1, 1, 1, 3, 4, 1, 4]
def baseStart_525735 : Nat := 118140960795 + 525735 * 2 ^ 59
def prefixEnd_525735 : Nat := 4983230072969 + 3 ^ 40 * 525735 * 2
def baseEnd_525735 : Nat := 89984917297201931031565

theorem tailTrace_525735 : CollatzResearch.WordTrace tailWord_525735 prefixEnd_525735 89984917297201931031565 := by
  unfold tailWord_525735
  simp only [CollatzResearch.WordTrace]
  refine ⟨19175130750359358234690659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12783420500239572156460439 19175130750359358234690659)
  ·
    refine ⟨28762696125539037352035989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19175130750359358234690659 28762696125539037352035989)
    ·
      refine ⟨1348251380884642375876687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 28762696125539037352035989 1348251380884642375876687)
      ·
        refine ⟨2022377071326963563815031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1348251380884642375876687 2022377071326963563815031)
        ·
          refine ⟨3033565606990445345722547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2022377071326963563815031 3033565606990445345722547)
          ·
            refine ⟨4550348410485668018583821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3033565606990445345722547 4550348410485668018583821)
            ·
              refine ⟨1706380653932125506968933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4550348410485668018583821 1706380653932125506968933)
              ·
                refine ⟨319946372612273532556675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1706380653932125506968933 319946372612273532556675)
                ·
                  refine ⟨479919558918410298835013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 319946372612273532556675 479919558918410298835013)
                  ·
                    refine ⟨89984917297201931031565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 479919558918410298835013 89984917297201931031565)
                    ·
                      rfl

theorem cell23_525735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 3, 4, 1, 4].length) (baseStart_525735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_525735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_525735 prefixEnd_525735 := by exact prefixLift 525735
  have htrace : WordTrace (prefixWord ++ tailWord_525735) baseStart_525735 baseEnd_525735 := by
    simpa [prefixWord, tailWord_525735, baseEnd_525735] using wordTrace_append hprefix tailTrace_525735
  have hstable : (prefixWord ++ tailWord_525735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_525735).length < 2 ^ (prefixWord ++ tailWord_525735).sum := by decide
  have hdescent : baseEnd_525735 < baseStart_525735 := by decide
  rcases family_descends (prefixWord ++ tailWord_525735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_525768 : List Nat := [2, 1, 3, 1, 3, 1, 3, 1, 1, 5, 2]
def baseStart_525768 : Nat := 118140960795 + 525768 * 2 ^ 59
def prefixEnd_525768 : Nat := 4983230072969 + 3 ^ 40 * 525768 * 2
def baseEnd_525768 : Nat := 269971696753204163982043

theorem tailTrace_525768 : CollatzResearch.WordTrace tailWord_525768 prefixEnd_525768 269971696753204163982043 := by
  unfold tailWord_525768
  simp only [CollatzResearch.WordTrace]
  refine ⟨9588167179619902435320979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12784222906159869913761305 9588167179619902435320979)
  ·
    refine ⟨14382250769429853652981469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9588167179619902435320979 14382250769429853652981469)
    ·
      refine ⟨5393344038536195119868051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14382250769429853652981469 5393344038536195119868051)
      ·
        refine ⟨8090016057804292679802077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5393344038536195119868051 8090016057804292679802077)
        ·
          refine ⟨3033756021676609754925779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8090016057804292679802077 3033756021676609754925779)
          ·
            refine ⟨4550634032514914632388669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3033756021676609754925779 4550634032514914632388669)
            ·
              refine ⟨1706487762193092987145751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4550634032514914632388669 1706487762193092987145751)
              ·
                refine ⟨2559731643289639480718627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1706487762193092987145751 2559731643289639480718627)
                ·
                  refine ⟨3839597464934459221077941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2559731643289639480718627 3839597464934459221077941)
                  ·
                    refine ⟨359962262337605551976057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3839597464934459221077941 359962262337605551976057)
                    ·
                      refine ⟨269971696753204163982043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 359962262337605551976057 269971696753204163982043)
                      ·
                        rfl

theorem cell23_525768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 3, 1, 1, 5, 2].length) (baseStart_525768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_525768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_525768 prefixEnd_525768 := by exact prefixLift 525768
  have htrace : WordTrace (prefixWord ++ tailWord_525768) baseStart_525768 baseEnd_525768 := by
    simpa [prefixWord, tailWord_525768, baseEnd_525768] using wordTrace_append hprefix tailTrace_525768
  have hstable : (prefixWord ++ tailWord_525768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_525768).length < 2 ^ (prefixWord ++ tailWord_525768).sum := by decide
  have hdescent : baseEnd_525768 < baseStart_525768 := by decide
  rcases family_descends (prefixWord ++ tailWord_525768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_525775 : List Nat := [1, 1, 2, 1, 1, 4, 3, 5, 1, 1, 3]
def baseStart_525775 : Nat := 118140960795 + 525775 * 2 ^ 59
def prefixEnd_525775 : Nat := 4983230072969 + 3 ^ 40 * 525775 * 2
def baseEnd_525775 : Nat := 269975291117785636594511

theorem tailTrace_525775 : CollatzResearch.WordTrace tailWord_525775 prefixEnd_525775 269975291117785636594511 := by
  unfold tailWord_525775
  simp only [CollatzResearch.WordTrace]
  refine ⟨19176589670214445066146779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12784393113476296710764519 19176589670214445066146779)
  ·
    refine ⟨28764884505321667599220169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19176589670214445066146779 28764884505321667599220169)
    ·
      refine ⟨21573663378991250699415127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28764884505321667599220169 21573663378991250699415127)
      ·
        refine ⟨32360495068486876049122691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21573663378991250699415127 32360495068486876049122691)
        ·
          refine ⟨48540742602730314073684037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32360495068486876049122691 48540742602730314073684037)
          ·
            refine ⟨9101389238011933888815757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48540742602730314073684037 9101389238011933888815757)
            ·
              refine ⟨3413020964254475208305909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9101389238011933888815757 3413020964254475208305909)
              ·
                refine ⟨319970715398857050778679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3413020964254475208305909 319970715398857050778679)
                ·
                  refine ⟨479956073098285576168019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 319970715398857050778679 479956073098285576168019)
                  ·
                    refine ⟨719934109647428364252029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 479956073098285576168019 719934109647428364252029)
                    ·
                      refine ⟨269975291117785636594511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 719934109647428364252029 269975291117785636594511)
                      ·
                        rfl

theorem cell23_525775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 5, 1, 1, 3].length) (baseStart_525775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_525775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_525775 prefixEnd_525775 := by exact prefixLift 525775
  have htrace : WordTrace (prefixWord ++ tailWord_525775) baseStart_525775 baseEnd_525775 := by
    simpa [prefixWord, tailWord_525775, baseEnd_525775] using wordTrace_append hprefix tailTrace_525775
  have hstable : (prefixWord ++ tailWord_525775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_525775).length < 2 ^ (prefixWord ++ tailWord_525775).sum := by decide
  have hdescent : baseEnd_525775 < baseStart_525775 := by decide
  rcases family_descends (prefixWord ++ tailWord_525775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_525808 : List Nat := [2, 1, 1, 1, 3, 6, 1, 1, 1, 6]
def baseStart_525808 : Nat := 118140960795 + 525808 * 2 ^ 59
def prefixEnd_525808 : Nat := 4983230072969 + 3 ^ 40 * 525808 * 2
def baseEnd_525808 : Nat := 89997411993128002493953

theorem tailTrace_525808 : CollatzResearch.WordTrace tailWord_525808 prefixEnd_525808 89997411993128002493953 := by
  unfold tailWord_525808
  simp only [CollatzResearch.WordTrace]
  refine ⟨9588896639547445851049039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12785195519396594468065385 9588896639547445851049039)
  ·
    refine ⟨14383344959321168776573559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9588896639547445851049039 14383344959321168776573559)
    ·
      refine ⟨21575017438981753164860339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14383344959321168776573559 21575017438981753164860339)
      ·
        refine ⟨32362526158472629747290509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21575017438981753164860339 32362526158472629747290509)
        ·
          refine ⟨12135947309427236155233941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32362526158472629747290509 12135947309427236155233941)
          ·
            refine ⟨568872530129401694776591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 12135947309427236155233941 568872530129401694776591)
            ·
              refine ⟨853308795194102542164887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 568872530129401694776591 853308795194102542164887)
              ·
                refine ⟨1279963192791153813247331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 853308795194102542164887 1279963192791153813247331)
                ·
                  refine ⟨1919944789186730719870997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1279963192791153813247331 1919944789186730719870997)
                  ·
                    refine ⟨89997411993128002493953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1919944789186730719870997 89997411993128002493953)
                    ·
                      rfl

theorem cell23_525808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 1, 1, 1, 6].length) (baseStart_525808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_525808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_525808 prefixEnd_525808 := by exact prefixLift 525808
  have htrace : WordTrace (prefixWord ++ tailWord_525808) baseStart_525808 baseEnd_525808 := by
    simpa [prefixWord, tailWord_525808, baseEnd_525808] using wordTrace_append hprefix tailTrace_525808
  have hstable : (prefixWord ++ tailWord_525808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_525808).length < 2 ^ (prefixWord ++ tailWord_525808).sum := by decide
  have hdescent : baseEnd_525808 < baseStart_525808 := by decide
  rcases family_descends (prefixWord ++ tailWord_525808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_525811 : List Nat := [1, 1, 1, 2, 2, 2, 2, 5, 1, 2, 4]
def baseStart_525811 : Nat := 118140960795 + 525811 * 2 ^ 59
def prefixEnd_525811 : Nat := 4983230072969 + 3 ^ 40 * 525811 * 2
def baseEnd_525811 : Nat := 269993776421347495744345

theorem tailTrace_525811 : CollatzResearch.WordTrace tailWord_525811 prefixEnd_525811 269993776421347495744345 := by
  unfold tailWord_525811
  simp only [CollatzResearch.WordTrace]
  refine ⟨19177902698084023214457287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12785268465389348809638191 19177902698084023214457287)
  ·
    refine ⟨28766854047126034821685931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19177902698084023214457287 28766854047126034821685931)
    ·
      refine ⟨43150281070689052232528897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28766854047126034821685931 43150281070689052232528897)
      ·
        refine ⟨32362710803016789174396673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43150281070689052232528897 32362710803016789174396673)
        ·
          refine ⟨24272033102262591880797505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32362710803016789174396673 24272033102262591880797505)
          ·
            refine ⟨18204024826696943910598129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24272033102262591880797505 18204024826696943910598129)
            ·
              refine ⟨13653018620022707932948597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18204024826696943910598129 13653018620022707932948597)
              ·
                refine ⟨1279970495627128868713931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13653018620022707932948597 1279970495627128868713931)
                ·
                  refine ⟨1919955743440693303070897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1279970495627128868713931 1919955743440693303070897)
                  ·
                    refine ⟨1439966807580519977303173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1919955743440693303070897 1439966807580519977303173)
                    ·
                      refine ⟨269993776421347495744345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1439966807580519977303173 269993776421347495744345)
                      ·
                        rfl

theorem cell23_525811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 5, 1, 2, 4].length) (baseStart_525811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_525811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_525811 prefixEnd_525811 := by exact prefixLift 525811
  have htrace : WordTrace (prefixWord ++ tailWord_525811) baseStart_525811 baseEnd_525811 := by
    simpa [prefixWord, tailWord_525811, baseEnd_525811] using wordTrace_append hprefix tailTrace_525811
  have hstable : (prefixWord ++ tailWord_525811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_525811).length < 2 ^ (prefixWord ++ tailWord_525811).sum := by decide
  have hdescent : baseEnd_525811 < baseStart_525811 := by decide
  rcases family_descends (prefixWord ++ tailWord_525811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_525821 : List Nat := [1, 4, 1, 1, 1, 5, 1, 9]
def baseStart_525821 : Nat := 118140960795 + 525821 * 2 ^ 59
def prefixEnd_525821 : Nat := 4983230072969 + 3 ^ 40 * 525821 * 2
def baseEnd_525821 : Nat := 9999959675107128022937

theorem tailTrace_525821 : CollatzResearch.WordTrace tailWord_525821 prefixEnd_525821 9999959675107128022937 := by
  unfold tailWord_525821
  simp only [CollatzResearch.WordTrace]
  refine ⟨19178267428047794922321317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12785511618698529948214211 19178267428047794922321317)
  ·
    refine ⟨3595925142758961547935247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19178267428047794922321317 3595925142758961547935247)
    ·
      refine ⟨5393887714138442321902871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3595925142758961547935247 5393887714138442321902871)
      ·
        refine ⟨8090831571207663482854307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5393887714138442321902871 8090831571207663482854307)
        ·
          refine ⟨12136247356811495224281461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8090831571207663482854307 12136247356811495224281461)
          ·
            refine ⟨1137773189701077677276387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12136247356811495224281461 1137773189701077677276387)
            ·
              refine ⟨1706659784551616515914581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1137773189701077677276387 1706659784551616515914581)
              ·
                refine ⟨9999959675107128022937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 1706659784551616515914581 9999959675107128022937)
                ·
                  rfl

theorem cell23_525821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 1, 9].length) (baseStart_525821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_525821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_525821 prefixEnd_525821 := by exact prefixLift 525821
  have htrace : WordTrace (prefixWord ++ tailWord_525821) baseStart_525821 baseEnd_525821 := by
    simpa [prefixWord, tailWord_525821, baseEnd_525821] using wordTrace_append hprefix tailTrace_525821
  have hstable : (prefixWord ++ tailWord_525821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_525821).length < 2 ^ (prefixWord ++ tailWord_525821).sum := by decide
  have hdescent : baseEnd_525821 < baseStart_525821 := by decide
  rcases family_descends (prefixWord ++ tailWord_525821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_525826 : List Nat := [3, 4, 1, 2, 1, 3, 1, 3, 1, 1, 3]
def baseStart_525826 : Nat := 118140960795 + 525826 * 2 ^ 59
def prefixEnd_525826 : Nat := 4983230072969 + 3 ^ 40 * 525826 * 2
def baseEnd_525826 : Nat := 270001478631164937056777

theorem tailTrace_525826 : CollatzResearch.WordTrace tailWord_525826 prefixEnd_525826 270001478631164937056777 := by
  unfold tailWord_525826
  simp only [CollatzResearch.WordTrace]
  refine ⟨4794612448257420194063333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12785633195353120517502221 4794612448257420194063333)
  ·
    refine ⟨898989834048266286386875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4794612448257420194063333 898989834048266286386875)
    ·
      refine ⟨1348484751072399429580313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 898989834048266286386875 1348484751072399429580313)
      ·
        refine ⟨1011363563304299572185235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1348484751072399429580313 1011363563304299572185235)
        ·
          refine ⟨1517045344956449358277853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1011363563304299572185235 1517045344956449358277853)
          ·
            refine ⟨568892004358668509354195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1517045344956449358277853 568892004358668509354195)
            ·
              refine ⟨853338006538002764031293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 568892004358668509354195 853338006538002764031293)
              ·
                refine ⟨320001752451751036511735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 853338006538002764031293 320001752451751036511735)
                ·
                  refine ⟨480002628677626554767603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 320001752451751036511735 480002628677626554767603)
                  ·
                    refine ⟨720003943016439832151405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 480002628677626554767603 720003943016439832151405)
                    ·
                      refine ⟨270001478631164937056777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 720003943016439832151405 270001478631164937056777)
                      ·
                        rfl

theorem cell23_525826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 1, 3, 1, 1, 3].length) (baseStart_525826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_525826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_525826 prefixEnd_525826 := by exact prefixLift 525826
  have htrace : WordTrace (prefixWord ++ tailWord_525826) baseStart_525826 baseEnd_525826 := by
    simpa [prefixWord, tailWord_525826, baseEnd_525826] using wordTrace_append hprefix tailTrace_525826
  have hstable : (prefixWord ++ tailWord_525826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_525826).length < 2 ^ (prefixWord ++ tailWord_525826).sum := by decide
  have hdescent : baseEnd_525826 < baseStart_525826 := by decide
  rcases family_descends (prefixWord ++ tailWord_525826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_525838 : List Nat := [4, 1, 1, 2, 4, 2, 9]
def baseStart_525838 : Nat := 118140960795 + 525838 * 2 ^ 59
def prefixEnd_525838 : Nat := 4983230072969 + 3 ^ 40 * 525838 * 2
def baseEnd_525838 : Nat := 3333427659247146791441

theorem tailTrace_525838 : CollatzResearch.WordTrace tailWord_525838 prefixEnd_525838 3333427659247146791441 := by
  unfold tailWord_525838
  simp only [CollatzResearch.WordTrace]
  refine ⟨2397360933623275853211271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12785924979324137883793445 2397360933623275853211271)
  ·
    refine ⟨3596041400434913779816907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2397360933623275853211271 3596041400434913779816907)
    ·
      refine ⟨5394062100652370669725361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3596041400434913779816907 5394062100652370669725361)
      ·
        refine ⟨4045546575489278002294021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5394062100652370669725361 4045546575489278002294021)
        ·
          refine ⟨758539982904239625430129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4045546575489278002294021 758539982904239625430129)
          ·
            refine ⟨568904987178179719072597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 758539982904239625430129 568904987178179719072597)
            ·
              refine ⟨3333427659247146791441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 568904987178179719072597 3333427659247146791441)
              ·
                rfl

theorem cell23_525838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 9].length) (baseStart_525838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_525838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_525838 prefixEnd_525838 := by exact prefixLift 525838
  have htrace : WordTrace (prefixWord ++ tailWord_525838) baseStart_525838 baseEnd_525838 := by
    simpa [prefixWord, tailWord_525838, baseEnd_525838] using wordTrace_append hprefix tailTrace_525838
  have hstable : (prefixWord ++ tailWord_525838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_525838).length < 2 ^ (prefixWord ++ tailWord_525838).sum := by decide
  have hdescent : baseEnd_525838 < baseStart_525838 := by decide
  rcases family_descends (prefixWord ++ tailWord_525838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_525859 : List Nat := [1, 1, 1, 4, 6, 1, 2, 1, 2, 4]
def baseStart_525859 : Nat := 118140960795 + 525859 * 2 ^ 59
def prefixEnd_525859 : Nat := 4983230072969 + 3 ^ 40 * 525859 * 2
def baseEnd_525859 : Nat := 90006141164254435981375

theorem tailTrace_525859 : CollatzResearch.WordTrace tailWord_525859 prefixEnd_525859 90006141164254435981375 := by
  unfold tailWord_525859
  simp only [CollatzResearch.WordTrace]
  refine ⟨19179653401910127412204631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12786435601273418274803087 19179653401910127412204631)
  ·
    refine ⟨28769480102865191118306947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19179653401910127412204631 28769480102865191118306947)
    ·
      refine ⟨43154220154297786677460421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28769480102865191118306947 43154220154297786677460421)
      ·
        refine ⟨8091416278930835002023829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43154220154297786677460421 8091416278930835002023829)
        ·
          refine ⟨379285138074882890719867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 8091416278930835002023829 379285138074882890719867)
          ·
            refine ⟨568927707112324336079801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 379285138074882890719867 568927707112324336079801)
            ·
              refine ⟨426695780334243252059851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 568927707112324336079801 426695780334243252059851)
              ·
                refine ⟨640043670501364878089777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 426695780334243252059851 640043670501364878089777)
                ·
                  refine ⟨480032752876023658567333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 640043670501364878089777 480032752876023658567333)
                  ·
                    refine ⟨90006141164254435981375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 480032752876023658567333 90006141164254435981375)
                    ·
                      rfl

theorem cell23_525859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 2, 1, 2, 4].length) (baseStart_525859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_525859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_525859 prefixEnd_525859 := by exact prefixLift 525859
  have htrace : WordTrace (prefixWord ++ tailWord_525859) baseStart_525859 baseEnd_525859 := by
    simpa [prefixWord, tailWord_525859, baseEnd_525859] using wordTrace_append hprefix tailTrace_525859
  have hstable : (prefixWord ++ tailWord_525859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_525859).length < 2 ^ (prefixWord ++ tailWord_525859).sum := by decide
  have hdescent : baseEnd_525859 < baseStart_525859 := by decide
  rcases family_descends (prefixWord ++ tailWord_525859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_525875 : List Nat := [1, 1, 1, 2, 4, 4, 1, 1, 3, 3, 2]
def baseStart_525875 : Nat := 118140960795 + 525875 * 2 ^ 59
def prefixEnd_525875 : Nat := 4983230072969 + 3 ^ 40 * 525875 * 2
def baseEnd_525875 : Nat := 270026639183235245344051

theorem tailTrace_525875 : CollatzResearch.WordTrace tailWord_525875 prefixEnd_525875 270026639183235245344051 := by
  unfold tailWord_525875
  simp only [CollatzResearch.WordTrace]
  refine ⟨19180236969852162144787079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12786824646568108096524719 19180236969852162144787079)
  ·
    refine ⟨28770355454778243217180619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19180236969852162144787079 28770355454778243217180619)
    ·
      refine ⟨43155533182167364825770929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28770355454778243217180619 43155533182167364825770929)
      ·
        refine ⟨32366649886625523619328197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43155533182167364825770929 32366649886625523619328197)
        ·
          refine ⟨6068746853742285678624037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32366649886625523619328197 6068746853742285678624037)
          ·
            refine ⟨1137890035076678564742007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6068746853742285678624037 1137890035076678564742007)
            ·
              refine ⟨1706835052615017847113011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1137890035076678564742007 1706835052615017847113011)
              ·
                refine ⟨2560252578922526770669517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1706835052615017847113011 2560252578922526770669517)
                ·
                  refine ⟨960094717095947539001069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2560252578922526770669517 960094717095947539001069)
                  ·
                    refine ⟨360035518910980327125401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 960094717095947539001069 360035518910980327125401)
                    ·
                      refine ⟨270026639183235245344051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 360035518910980327125401 270026639183235245344051)
                      ·
                        rfl

theorem cell23_525875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 1, 1, 3, 3, 2].length) (baseStart_525875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_525875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_525875 prefixEnd_525875 := by exact prefixLift 525875
  have htrace : WordTrace (prefixWord ++ tailWord_525875) baseStart_525875 baseEnd_525875 := by
    simpa [prefixWord, tailWord_525875, baseEnd_525875] using wordTrace_append hprefix tailTrace_525875
  have hstable : (prefixWord ++ tailWord_525875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_525875).length < 2 ^ (prefixWord ++ tailWord_525875).sum := by decide
  have hdescent : baseEnd_525875 < baseStart_525875 := by decide
  rcases family_descends (prefixWord ++ tailWord_525875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_525908 : List Nat := [2, 4, 1, 1, 1, 2, 1, 1, 1, 6, 3]
def baseStart_525908 : Nat := 118140960795 + 525908 * 2 ^ 59
def prefixEnd_525908 : Nat := 4983230072969 + 3 ^ 40 * 525908 * 2
def baseEnd_525908 : Nat := 270043584044833616231399

theorem tailTrace_525908 : CollatzResearch.WordTrace tailWord_525908 prefixEnd_525908 270043584044833616231399 := by
  unfold tailWord_525908
  simp only [CollatzResearch.WordTrace]
  refine ⟨9590720289366304390369189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12787627052488405853825585 9590720289366304390369189)
  ·
    refine ⟨1798260054256182073194223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9590720289366304390369189 1798260054256182073194223)
    ·
      refine ⟨2697390081384273109791335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1798260054256182073194223 2697390081384273109791335)
      ·
        refine ⟨4046085122076409664687003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2697390081384273109791335 4046085122076409664687003)
        ·
          refine ⟨6069127683114614497030505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4046085122076409664687003 6069127683114614497030505)
          ·
            refine ⟨4551845762335960872772879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6069127683114614497030505 4551845762335960872772879)
            ·
              refine ⟨6827768643503941309159319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4551845762335960872772879 6827768643503941309159319)
              ·
                refine ⟨10241652965255911963738979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6827768643503941309159319 10241652965255911963738979)
                ·
                  refine ⟨15362479447883867945608469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10241652965255911963738979 15362479447883867945608469)
                  ·
                    refine ⟨720116224119556309950397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15362479447883867945608469 720116224119556309950397)
                    ·
                      refine ⟨270043584044833616231399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 720116224119556309950397 270043584044833616231399)
                      ·
                        rfl

theorem cell23_525908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 1, 1, 6, 3].length) (baseStart_525908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_525908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_525908 prefixEnd_525908 := by exact prefixLift 525908
  have htrace : WordTrace (prefixWord ++ tailWord_525908) baseStart_525908 baseEnd_525908 := by
    simpa [prefixWord, tailWord_525908, baseEnd_525908] using wordTrace_append hprefix tailTrace_525908
  have hstable : (prefixWord ++ tailWord_525908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_525908).length < 2 ^ (prefixWord ++ tailWord_525908).sum := by decide
  have hdescent : baseEnd_525908 < baseStart_525908 := by decide
  rcases family_descends (prefixWord ++ tailWord_525908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_525928 : List Nat := [2, 1, 4, 3, 1, 1, 1, 1, 9]
def baseStart_525928 : Nat := 118140960795 + 525928 * 2 ^ 59
def prefixEnd_525928 : Nat := 4983230072969 + 3 ^ 40 * 525928 * 2
def baseEnd_525928 : Nat := 30005983739769281997923

theorem tailTrace_525928 : CollatzResearch.WordTrace tailWord_525928 prefixEnd_525928 30005983739769281997923 := by
  unfold tailWord_525928
  simp only [CollatzResearch.WordTrace]
  refine ⟨9591085019330076098233219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12788113359106768130977625 9591085019330076098233219)
  ·
    refine ⟨14386627528995114147349829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9591085019330076098233219 14386627528995114147349829)
    ·
      refine ⟨2697492661686583902628093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14386627528995114147349829 2697492661686583902628093)
      ·
        refine ⟨1011559748132468963485535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2697492661686583902628093 1011559748132468963485535)
        ·
          refine ⟨1517339622198703445228303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1011559748132468963485535 1517339622198703445228303)
          ·
            refine ⟨2276009433298055167842455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1517339622198703445228303 2276009433298055167842455)
            ·
              refine ⟨3414014149947082751763683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2276009433298055167842455 3414014149947082751763683)
              ·
                refine ⟨5121021224920624127645525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3414014149947082751763683 5121021224920624127645525)
                ·
                  refine ⟨30005983739769281997923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 5121021224920624127645525 30005983739769281997923)
                  ·
                    rfl

theorem cell23_525928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 1, 9].length) (baseStart_525928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_525928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_525928 prefixEnd_525928 := by exact prefixLift 525928
  have htrace : WordTrace (prefixWord ++ tailWord_525928) baseStart_525928 baseEnd_525928 := by
    simpa [prefixWord, tailWord_525928, baseEnd_525928] using wordTrace_append hprefix tailTrace_525928
  have hstable : (prefixWord ++ tailWord_525928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_525928).length < 2 ^ (prefixWord ++ tailWord_525928).sum := by decide
  have hdescent : baseEnd_525928 < baseStart_525928 := by decide
  rcases family_descends (prefixWord ++ tailWord_525928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_525945 : List Nat := [1, 2, 1, 3, 3, 1, 4, 3, 5]
def baseStart_525945 : Nat := 118140960795 + 525945 * 2 ^ 59
def prefixEnd_525945 : Nat := 4983230072969 + 3 ^ 40 * 525945 * 2
def baseEnd_525945 : Nat := 30006953647672219052081

theorem tailTrace_525945 : CollatzResearch.WordTrace tailWord_525945 prefixEnd_525945 30006953647672219052081 := by
  unfold tailWord_525945
  simp only [CollatzResearch.WordTrace]
  refine ⟨19182790079598564099835289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12788526719732376066556859 19182790079598564099835289)
  ·
    refine ⟨14387092559698923074876467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19182790079598564099835289 14387092559698923074876467)
    ·
      refine ⟨21580638839548384612314701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14387092559698923074876467 21580638839548384612314701)
      ·
        refine ⟨8092739564830644229618013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21580638839548384612314701 8092739564830644229618013)
        ·
          refine ⟨3034777336811491586106755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8092739564830644229618013 3034777336811491586106755)
          ·
            refine ⟨4552166005217237379160133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3034777336811491586106755 4552166005217237379160133)
            ·
              refine ⟨853531125978232008592525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4552166005217237379160133 853531125978232008592525)
              ·
                refine ⟨320074172241837003222197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 853531125978232008592525 320074172241837003222197)
                ·
                  refine ⟨30006953647672219052081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 320074172241837003222197 30006953647672219052081)
                  ·
                    rfl

theorem cell23_525945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 4, 3, 5].length) (baseStart_525945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_525945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_525945 prefixEnd_525945 := by exact prefixLift 525945
  have htrace : WordTrace (prefixWord ++ tailWord_525945) baseStart_525945 baseEnd_525945 := by
    simpa [prefixWord, tailWord_525945, baseEnd_525945] using wordTrace_append hprefix tailTrace_525945
  have hstable : (prefixWord ++ tailWord_525945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_525945).length < 2 ^ (prefixWord ++ tailWord_525945).sum := by decide
  have hdescent : baseEnd_525945 < baseStart_525945 := by decide
  rcases family_descends (prefixWord ++ tailWord_525945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_525956 : List Nat := [2, 3, 2, 1, 4, 2, 1, 2, 2, 2, 2]
def baseStart_525956 : Nat := 118140960795 + 525956 * 2 ^ 59
def prefixEnd_525956 : Nat := 4983230072969 + 3 ^ 40 * 525956 * 2
def baseEnd_525956 : Nat := 270068231116249428431179

theorem tailTrace_525956 : CollatzResearch.WordTrace tailWord_525956 prefixEnd_525956 270068231116249428431179 := by
  unfold tailWord_525956
  simp only [CollatzResearch.WordTrace]
  refine ⟨9591595641279356489242861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12788794188372475318990481 9591595641279356489242861)
  ·
    refine ⟨3596848365479758683466073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9591595641279356489242861 3596848365479758683466073)
    ·
      refine ⟨2697636274109819012599555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3596848365479758683466073 2697636274109819012599555)
      ·
        refine ⟨4046454411164728518899333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2697636274109819012599555 4046454411164728518899333)
        ·
          refine ⟨758710202093386597293625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4046454411164728518899333 758710202093386597293625)
          ·
            refine ⟨569032651570039947970219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 758710202093386597293625 569032651570039947970219)
            ·
              refine ⟨853548977355059921955329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 569032651570039947970219 853548977355059921955329)
              ·
                refine ⟨640161733016294941466497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 853548977355059921955329 640161733016294941466497)
                ·
                  refine ⟨480121299762221206099873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 640161733016294941466497 480121299762221206099873)
                  ·
                    refine ⟨360090974821665904574905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 480121299762221206099873 360090974821665904574905)
                    ·
                      refine ⟨270068231116249428431179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 360090974821665904574905 270068231116249428431179)
                      ·
                        rfl

theorem cell23_525956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 1, 2, 2, 2, 2].length) (baseStart_525956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_525956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_525956 prefixEnd_525956 := by exact prefixLift 525956
  have htrace : WordTrace (prefixWord ++ tailWord_525956) baseStart_525956 baseEnd_525956 := by
    simpa [prefixWord, tailWord_525956, baseEnd_525956] using wordTrace_append hprefix tailTrace_525956
  have hstable : (prefixWord ++ tailWord_525956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_525956).length < 2 ^ (prefixWord ++ tailWord_525956).sum := by decide
  have hdescent : baseEnd_525956 < baseStart_525956 := by decide
  rcases family_descends (prefixWord ++ tailWord_525956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_525971 : List Nat := [1, 1, 1, 2, 1, 2, 2, 1, 4, 8]
def baseStart_525971 : Nat := 118140960795 + 525971 * 2 ^ 59
def prefixEnd_525971 : Nat := 4983230072969 + 3 ^ 40 * 525971 * 2
def baseEnd_525971 : Nat := 90025311108688956581203

theorem tailTrace_525971 : CollatzResearch.WordTrace tailWord_525971 prefixEnd_525971 90025311108688956581203 := by
  unfold tailWord_525971
  simp only [CollatzResearch.WordTrace]
  refine ⟨19183738377504370540281767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12789158918336247026854511 19183738377504370540281767)
  ·
    refine ⟨28775607566256555810422651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19183738377504370540281767 28775607566256555810422651)
    ·
      refine ⟨43163411349384833715633977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28775607566256555810422651 43163411349384833715633977)
      ·
        refine ⟨32372558512038625286725483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43163411349384833715633977 32372558512038625286725483)
        ·
          refine ⟨48558837768057937930088225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32372558512038625286725483 48558837768057937930088225)
          ·
            refine ⟨36419128326043453447566169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48558837768057937930088225 36419128326043453447566169)
            ·
              refine ⟨27314346244532590085674627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36419128326043453447566169 27314346244532590085674627)
              ·
                refine ⟨40971519366798885128511941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27314346244532590085674627 40971519366798885128511941)
                ·
                  refine ⟨7682159881274790961595989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40971519366798885128511941 7682159881274790961595989)
                  ·
                    refine ⟨90025311108688956581203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 7682159881274790961595989 90025311108688956581203)
                    ·
                      rfl

theorem cell23_525971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 4, 8].length) (baseStart_525971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_525971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_525971 prefixEnd_525971 := by exact prefixLift 525971
  have htrace : WordTrace (prefixWord ++ tailWord_525971) baseStart_525971 baseEnd_525971 := by
    simpa [prefixWord, tailWord_525971, baseEnd_525971] using wordTrace_append hprefix tailTrace_525971
  have hstable : (prefixWord ++ tailWord_525971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_525971).length < 2 ^ (prefixWord ++ tailWord_525971).sum := by decide
  have hdescent : baseEnd_525971 < baseStart_525971 := by decide
  rcases family_descends (prefixWord ++ tailWord_525971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_526015 : List Nat := [1, 1, 2, 2, 2, 3, 3, 2, 2, 2, 3]
def baseStart_526015 : Nat := 118140960795 + 526015 * 2 ^ 59
def prefixEnd_526015 : Nat := 4983230072969 + 3 ^ 40 * 526015 * 2
def baseEnd_526015 : Nat := 270098526474864697593407

theorem tailTrace_526015 : CollatzResearch.WordTrace tailWord_526015 prefixEnd_526015 270098526474864697593407 := by
  unfold tailWord_526015
  simp only [CollatzResearch.WordTrace]
  refine ⟨19185343189344966054883499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12790228792896644036588999 19185343189344966054883499)
  ·
    refine ⟨28778014784017449082325249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19185343189344966054883499 28778014784017449082325249)
    ·
      refine ⟨21583511088013086811743937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28778014784017449082325249 21583511088013086811743937)
      ·
        refine ⟨16187633316009815108807953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21583511088013086811743937 16187633316009815108807953)
        ·
          refine ⟨12140724987007361331605965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16187633316009815108807953 12140724987007361331605965)
          ·
            refine ⟨4552771870127760499352237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12140724987007361331605965 4552771870127760499352237)
            ·
              refine ⟨1707289451297910187257089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4552771870127760499352237 1707289451297910187257089)
              ·
                refine ⟨1280467088473432640442817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1707289451297910187257089 1280467088473432640442817)
                ·
                  refine ⟨960350316355074480332113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1280467088473432640442817 960350316355074480332113)
                  ·
                    refine ⟨720262737266305860249085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 960350316355074480332113 720262737266305860249085)
                    ·
                      refine ⟨270098526474864697593407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 720262737266305860249085 270098526474864697593407)
                      ·
                        rfl

theorem cell23_526015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3, 2, 2, 2, 3].length) (baseStart_526015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_526015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_526015 prefixEnd_526015 := by exact prefixLift 526015
  have htrace : WordTrace (prefixWord ++ tailWord_526015) baseStart_526015 baseEnd_526015 := by
    simpa [prefixWord, tailWord_526015, baseEnd_526015] using wordTrace_append hprefix tailTrace_526015
  have hstable : (prefixWord ++ tailWord_526015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_526015).length < 2 ^ (prefixWord ++ tailWord_526015).sum := by decide
  have hdescent : baseEnd_526015 < baseStart_526015 := by decide
  rcases family_descends (prefixWord ++ tailWord_526015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_526085 : List Nat := [1, 3, 1, 1, 2, 1, 1, 1, 4, 6, 2]
def baseStart_526085 : Nat := 118140960795 + 526085 * 2 ^ 59
def prefixEnd_526085 : Nat := 4983230072969 + 3 ^ 40 * 526085 * 2
def baseEnd_526085 : Nat := 270134470120679423718085

theorem tailTrace_526085 : CollatzResearch.WordTrace tailWord_526085 prefixEnd_526085 270134470120679423718085 := by
  unfold tailWord_526085
  simp only [CollatzResearch.WordTrace]
  refine ⟨19187896299091368009931709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12791930866060912006621139 19187896299091368009931709)
  ·
    refine ⟨7195461112159263003724391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19187896299091368009931709 7195461112159263003724391)
    ·
      refine ⟨10793191668238894505586587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7195461112159263003724391 10793191668238894505586587)
      ·
        refine ⟨16189787502358341758379881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10793191668238894505586587 16189787502358341758379881)
        ·
          refine ⟨12142340626768756318784911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16189787502358341758379881 12142340626768756318784911)
          ·
            refine ⟨18213510940153134478177367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12142340626768756318784911 18213510940153134478177367)
            ·
              refine ⟨27320266410229701717266051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18213510940153134478177367 27320266410229701717266051)
              ·
                refine ⟨40980399615344552575899077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27320266410229701717266051 40980399615344552575899077)
                ·
                  refine ⟨7683824927877103607981077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40980399615344552575899077 7683824927877103607981077)
                  ·
                    refine ⟨360179293494239231624113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7683824927877103607981077 360179293494239231624113)
                    ·
                      refine ⟨270134470120679423718085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 360179293494239231624113 270134470120679423718085)
                      ·
                        rfl

theorem cell23_526085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 4, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 4, 6, 2].length) (baseStart_526085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_526085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_526085 prefixEnd_526085 := by exact prefixLift 526085
  have htrace : WordTrace (prefixWord ++ tailWord_526085) baseStart_526085 baseEnd_526085 := by
    simpa [prefixWord, tailWord_526085, baseEnd_526085] using wordTrace_append hprefix tailTrace_526085
  have hstable : (prefixWord ++ tailWord_526085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_526085).length < 2 ^ (prefixWord ++ tailWord_526085).sum := by decide
  have hdescent : baseEnd_526085 < baseStart_526085 := by decide
  rcases family_descends (prefixWord ++ tailWord_526085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_526100 : List Nat := [2, 4, 4, 1, 2, 1, 1, 1, 2, 2, 3]
def baseStart_526100 : Nat := 118140960795 + 526100 * 2 ^ 59
def prefixEnd_526100 : Nat := 4983230072969 + 3 ^ 40 * 526100 * 2
def baseEnd_526100 : Nat := 270142172330496865030517

theorem tailTrace_526100 : CollatzResearch.WordTrace tailWord_526100 prefixEnd_526100 270142172330496865030517 := by
  unfold tailWord_526100
  simp only [CollatzResearch.WordTrace]
  refine ⟨9594221697018512785863877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12792295596024683714485169 9594221697018512785863877)
  ·
    refine ⟨1798916568190971147349477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9594221697018512785863877 1798916568190971147349477)
    ·
      refine ⟨337296856535807090128027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1798916568190971147349477 337296856535807090128027)
      ·
        refine ⟨505945284803710635192041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 337296856535807090128027 505945284803710635192041)
        ·
          refine ⟨379458963602782976394031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 505945284803710635192041 379458963602782976394031)
          ·
            refine ⟨569188445404174464591047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 379458963602782976394031 569188445404174464591047)
            ·
              refine ⟨853782668106261696886571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 569188445404174464591047 853782668106261696886571)
              ·
                refine ⟨1280674002159392545329857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 853782668106261696886571 1280674002159392545329857)
                ·
                  refine ⟨960505501619544408997393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1280674002159392545329857 960505501619544408997393)
                  ·
                    refine ⟨720379126214658306748045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 960505501619544408997393 720379126214658306748045)
                    ·
                      refine ⟨270142172330496865030517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 720379126214658306748045 270142172330496865030517)
                      ·
                        rfl

theorem cell23_526100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 1, 1, 2, 2, 3].length) (baseStart_526100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_526100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_526100 prefixEnd_526100 := by exact prefixLift 526100
  have htrace : WordTrace (prefixWord ++ tailWord_526100) baseStart_526100 baseEnd_526100 := by
    simpa [prefixWord, tailWord_526100, baseEnd_526100] using wordTrace_append hprefix tailTrace_526100
  have hstable : (prefixWord ++ tailWord_526100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_526100).length < 2 ^ (prefixWord ++ tailWord_526100).sum := by decide
  have hdescent : baseEnd_526100 < baseStart_526100 := by decide
  rcases family_descends (prefixWord ++ tailWord_526100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_526115 : List Nat := [1, 1, 1, 4, 2, 1, 4, 2, 1, 2, 4]
def baseStart_526115 : Nat := 118140960795 + 526115 * 2 ^ 59
def prefixEnd_526115 : Nat := 4983230072969 + 3 ^ 40 * 526115 * 2
def baseEnd_526115 : Nat := 270149874540314306342947

theorem tailTrace_526115 : CollatzResearch.WordTrace tailWord_526115 prefixEnd_526115 270149874540314306342947 := by
  unfold tailWord_526115
  simp only [CollatzResearch.WordTrace]
  refine ⟨19188990488982683133523799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12792660325988455422349199 19188990488982683133523799)
  ·
    refine ⟨28783485733474024700285699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19188990488982683133523799 28783485733474024700285699)
    ·
      refine ⟨43175228600211037050428549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28783485733474024700285699 43175228600211037050428549)
      ·
        refine ⟨8095355362539569446955353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43175228600211037050428549 8095355362539569446955353)
        ·
          refine ⟨6071516521904677085216515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8095355362539569446955353 6071516521904677085216515)
          ·
            refine ⟨9107274782857015627824773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6071516521904677085216515 9107274782857015627824773)
            ·
              refine ⟨1707614021785690430217145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9107274782857015627824773 1707614021785690430217145)
              ·
                refine ⟨1280710516339267822662859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1707614021785690430217145 1280710516339267822662859)
                ·
                  refine ⟨1921065774508901733994289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1280710516339267822662859 1921065774508901733994289)
                  ·
                    refine ⟨1440799330881676300495717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1921065774508901733994289 1440799330881676300495717)
                    ·
                      refine ⟨270149874540314306342947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1440799330881676300495717 270149874540314306342947)
                      ·
                        rfl

theorem cell23_526115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4, 2, 1, 2, 4].length) (baseStart_526115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_526115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_526115 prefixEnd_526115 := by exact prefixLift 526115
  have htrace : WordTrace (prefixWord ++ tailWord_526115) baseStart_526115 baseEnd_526115 := by
    simpa [prefixWord, tailWord_526115, baseEnd_526115] using wordTrace_append hprefix tailTrace_526115
  have hstable : (prefixWord ++ tailWord_526115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_526115).length < 2 ^ (prefixWord ++ tailWord_526115).sum := by decide
  have hdescent : baseEnd_526115 < baseStart_526115 := by decide
  rcases family_descends (prefixWord ++ tailWord_526115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_526128 : List Nat := [2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 6]
def baseStart_526128 : Nat := 118140960795 + 526128 * 2 ^ 59
def prefixEnd_526128 : Nat := 4983230072969 + 3 ^ 40 * 526128 * 2
def baseEnd_526128 : Nat := 270156549788822755480387

theorem tailTrace_526128 : CollatzResearch.WordTrace tailWord_526128 prefixEnd_526128 270156549788822755480387 := by
  unfold tailWord_526128
  simp only [CollatzResearch.WordTrace]
  refine ⟨9594732318967793176873519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12792976425290390902498025 9594732318967793176873519)
  ·
    refine ⟨14392098478451689765310279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9594732318967793176873519 14392098478451689765310279)
    ·
      refine ⟨21588147717677534647965419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14392098478451689765310279 21588147717677534647965419)
      ·
        refine ⟨32382221576516301971948129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21588147717677534647965419 32382221576516301971948129)
        ·
          refine ⟨24286666182387226478961097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32382221576516301971948129 24286666182387226478961097)
          ·
            refine ⟨18214999636790419859220823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24286666182387226478961097 18214999636790419859220823)
            ·
              refine ⟨27322499455185629788831235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18214999636790419859220823 27322499455185629788831235)
              ·
                refine ⟨40983749182778444683246853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27322499455185629788831235 40983749182778444683246853)
                ·
                  refine ⟨7684452971770958378108785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40983749182778444683246853 7684452971770958378108785)
                  ·
                    refine ⟨5763339728828218783581589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7684452971770958378108785 5763339728828218783581589)
                    ·
                      refine ⟨270156549788822755480387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 5763339728828218783581589 270156549788822755480387)
                      ·
                        rfl

theorem cell23_526128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 6].length) (baseStart_526128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_526128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_526128 prefixEnd_526128 := by exact prefixLift 526128
  have htrace : WordTrace (prefixWord ++ tailWord_526128) baseStart_526128 baseEnd_526128 := by
    simpa [prefixWord, tailWord_526128, baseEnd_526128] using wordTrace_append hprefix tailTrace_526128
  have hstable : (prefixWord ++ tailWord_526128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_526128).length < 2 ^ (prefixWord ++ tailWord_526128).sum := by decide
  have hdescent : baseEnd_526128 < baseStart_526128 := by decide
  rcases family_descends (prefixWord ++ tailWord_526128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_526129 : List Nat := [1, 2, 2, 3, 2, 4, 1, 2, 2, 4]
def baseStart_526129 : Nat := 118140960795 + 526129 * 2 ^ 59
def prefixEnd_526129 : Nat := 4983230072969 + 3 ^ 40 * 526129 * 2
def baseEnd_526129 : Nat := 90052354423159083855961

theorem tailTrace_526129 : CollatzResearch.WordTrace tailWord_526129 prefixEnd_526129 90052354423159083855961 := by
  unfold tailWord_526129
  simp only [CollatzResearch.WordTrace]
  refine ⟨19189501110931963524533441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12793000740621309016355627 19189501110931963524533441)
  ·
    refine ⟨14392125833198972643400081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19189501110931963524533441 14392125833198972643400081)
    ·
      refine ⟨10794094374899229482550061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14392125833198972643400081 10794094374899229482550061)
      ·
        refine ⟨4047785390587211055956273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10794094374899229482550061 4047785390587211055956273)
        ·
          refine ⟨3035839042940408291967205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4047785390587211055956273 3035839042940408291967205)
          ·
            refine ⟨569219820551326554743851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3035839042940408291967205 569219820551326554743851)
            ·
              refine ⟨853829730826989832115777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 569219820551326554743851 853829730826989832115777)
              ·
                refine ⟨640372298120242374086833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 853829730826989832115777 640372298120242374086833)
                ·
                  refine ⟨480279223590181780565125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 640372298120242374086833 480279223590181780565125)
                  ·
                    refine ⟨90052354423159083855961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 480279223590181780565125 90052354423159083855961)
                    ·
                      rfl

theorem cell23_526129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 1, 2, 2, 4].length) (baseStart_526129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_526129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_526129 prefixEnd_526129 := by exact prefixLift 526129
  have htrace : WordTrace (prefixWord ++ tailWord_526129) baseStart_526129 baseEnd_526129 := by
    simpa [prefixWord, tailWord_526129, baseEnd_526129] using wordTrace_append hprefix tailTrace_526129
  have hstable : (prefixWord ++ tailWord_526129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_526129).length < 2 ^ (prefixWord ++ tailWord_526129).sum := by decide
  have hdescent : baseEnd_526129 < baseStart_526129 := by decide
  rcases family_descends (prefixWord ++ tailWord_526129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_526136 : List Nat := [2, 1, 2, 1, 3, 3, 2, 4, 1, 2, 2]
def baseStart_526136 : Nat := 118140960795 + 526136 * 2 ^ 59
def prefixEnd_526136 : Nat := 4983230072969 + 3 ^ 40 * 526136 * 2
def baseEnd_526136 : Nat := 270160657634058724180351

theorem tailTrace_526136 : CollatzResearch.WordTrace tailWord_526136 prefixEnd_526136 270160657634058724180351 := by
  unfold tailWord_526136
  simp only [CollatzResearch.WordTrace]
  refine ⟨9594878210953301860019131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12793170947937735813358841 9594878210953301860019131)
  ·
    refine ⟨14392317316429952790028697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9594878210953301860019131 14392317316429952790028697)
    ·
      refine ⟨10794237987322464592521523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14392317316429952790028697 10794237987322464592521523)
      ·
        refine ⟨16191356980983696888782285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10794237987322464592521523 16191356980983696888782285)
        ·
          refine ⟨6071758867868886333293357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16191356980983696888782285 6071758867868886333293357)
          ·
            refine ⟨2276909575450832374985009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6071758867868886333293357 2276909575450832374985009)
            ·
              refine ⟨1707682181588124281238757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2276909575450832374985009 1707682181588124281238757)
              ·
                refine ⟨320190409047773302732267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1707682181588124281238757 320190409047773302732267)
                ·
                  refine ⟨480285613571659954098401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 320190409047773302732267 480285613571659954098401)
                  ·
                    refine ⟨360214210178744965573801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 480285613571659954098401 360214210178744965573801)
                    ·
                      refine ⟨270160657634058724180351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 360214210178744965573801 270160657634058724180351)
                      ·
                        rfl

theorem cell23_526136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 2, 4, 1, 2, 2].length) (baseStart_526136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_526136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_526136 prefixEnd_526136 := by exact prefixLift 526136
  have htrace : WordTrace (prefixWord ++ tailWord_526136) baseStart_526136 baseEnd_526136 := by
    simpa [prefixWord, tailWord_526136, baseEnd_526136] using wordTrace_append hprefix tailTrace_526136
  have hstable : (prefixWord ++ tailWord_526136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_526136).length < 2 ^ (prefixWord ++ tailWord_526136).sum := by decide
  have hdescent : baseEnd_526136 < baseStart_526136 := by decide
  rcases family_descends (prefixWord ++ tailWord_526136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_526152 : List Nat := [2, 1, 3, 1, 1, 4, 3, 1, 1, 3, 3]
def baseStart_526152 : Nat := 118140960795 + 526152 * 2 ^ 59
def prefixEnd_526152 : Nat := 4983230072969 + 3 ^ 40 * 526152 * 2
def baseEnd_526152 : Nat := 270168873324530661580277

theorem tailTrace_526152 : CollatzResearch.WordTrace tailWord_526152 prefixEnd_526152 270168873324530661580277 := by
  unfold tailWord_526152
  simp only [CollatzResearch.WordTrace]
  refine ⟨9595169994924319226310355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12793559993232425635080473 9595169994924319226310355)
  ·
    refine ⟨14392754992386478839465533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9595169994924319226310355 14392754992386478839465533)
    ·
      refine ⟨5397283122144929564799575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14392754992386478839465533 5397283122144929564799575)
      ·
        refine ⟨8095924683217394347199363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5397283122144929564799575 8095924683217394347199363)
        ·
          refine ⟨12143887024826091520799045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8095924683217394347199363 12143887024826091520799045)
          ·
            refine ⟨2276978817154892160149821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12143887024826091520799045 2276978817154892160149821)
            ·
              refine ⟨853867056433084560056183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2276978817154892160149821 853867056433084560056183)
              ·
                refine ⟨1280800584649626840084275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 853867056433084560056183 1280800584649626840084275)
                ·
                  refine ⟨1921200876974440260126413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1280800584649626840084275 1921200876974440260126413)
                  ·
                    refine ⟨720450328865415097547405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1921200876974440260126413 720450328865415097547405)
                    ·
                      refine ⟨270168873324530661580277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 720450328865415097547405 270168873324530661580277)
                      ·
                        rfl

theorem cell23_526152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 3, 1, 1, 3, 3].length) (baseStart_526152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_526152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_526152 prefixEnd_526152 := by exact prefixLift 526152
  have htrace : WordTrace (prefixWord ++ tailWord_526152) baseStart_526152 baseEnd_526152 := by
    simpa [prefixWord, tailWord_526152, baseEnd_526152] using wordTrace_append hprefix tailTrace_526152
  have hstable : (prefixWord ++ tailWord_526152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_526152).length < 2 ^ (prefixWord ++ tailWord_526152).sum := by decide
  have hdescent : baseEnd_526152 < baseStart_526152 := by decide
  rcases family_descends (prefixWord ++ tailWord_526152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_526165 : List Nat := [1, 3, 2, 2, 2, 2, 1, 1, 2, 2, 5]
def baseStart_526165 : Nat := 118140960795 + 526165 * 2 ^ 59
def prefixEnd_526165 : Nat := 4983230072969 + 3 ^ 40 * 526165 * 2
def baseEnd_526165 : Nat := 270175548573039110717717

theorem tailTrace_526165 : CollatzResearch.WordTrace tailWord_526165 prefixEnd_526165 270175548573039110717717 := by
  unfold tailWord_526165
  simp only [CollatzResearch.WordTrace]
  refine ⟨19190814138801541672843949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12793876092534361115229299 19190814138801541672843949)
  ·
    refine ⟨7196555302050578127316481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19190814138801541672843949 7196555302050578127316481)
    ·
      refine ⟨5397416476537933595487361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7196555302050578127316481 5397416476537933595487361)
      ·
        refine ⟨4048062357403450196615521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5397416476537933595487361 4048062357403450196615521)
        ·
          refine ⟨3036046768052587647461641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4048062357403450196615521 3036046768052587647461641)
          ·
            refine ⟨2277035076039440735596231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3036046768052587647461641 2277035076039440735596231)
            ·
              refine ⟨3415552614059161103394347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2277035076039440735596231 3415552614059161103394347)
              ·
                refine ⟨5123328921088741655091521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3415552614059161103394347 5123328921088741655091521)
                ·
                  refine ⟨3842496690816556241318641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5123328921088741655091521 3842496690816556241318641)
                  ·
                    refine ⟨2881872518112417180988981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3842496690816556241318641 2881872518112417180988981)
                    ·
                      refine ⟨270175548573039110717717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2881872518112417180988981 270175548573039110717717)
                      ·
                        rfl

theorem cell23_526165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 1, 2, 2, 5].length) (baseStart_526165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_526165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_526165 prefixEnd_526165 := by exact prefixLift 526165
  have htrace : WordTrace (prefixWord ++ tailWord_526165) baseStart_526165 baseEnd_526165 := by
    simpa [prefixWord, tailWord_526165, baseEnd_526165] using wordTrace_append hprefix tailTrace_526165
  have hstable : (prefixWord ++ tailWord_526165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_526165).length < 2 ^ (prefixWord ++ tailWord_526165).sum := by decide
  have hdescent : baseEnd_526165 < baseStart_526165 := by decide
  rcases family_descends (prefixWord ++ tailWord_526165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_526195 : List Nat := [1, 1, 1, 2, 2, 1, 3, 3, 2, 4, 3]
def baseStart_526195 : Nat := 118140960795 + 526195 * 2 ^ 59
def prefixEnd_526195 : Nat := 4983230072969 + 3 ^ 40 * 526195 * 2
def baseEnd_526195 : Nat := 270190952992673993342579

theorem tailTrace_526195 : CollatzResearch.WordTrace tailWord_526195 prefixEnd_526195 270190952992673993342579 := by
  unfold tailWord_526195
  simp only [CollatzResearch.WordTrace]
  refine ⟨19191908328692856796436039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12794605552461904530957359 19191908328692856796436039)
  ·
    refine ⟨28787862493039285194654059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19191908328692856796436039 28787862493039285194654059)
    ·
      refine ⟨43181793739558927791981089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28787862493039285194654059 43181793739558927791981089)
      ·
        refine ⟨32386345304669195843985817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43181793739558927791981089 32386345304669195843985817)
        ·
          refine ⟨24289758978501896882989363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32386345304669195843985817 24289758978501896882989363)
          ·
            refine ⟨36434638467752845324484045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24289758978501896882989363 36434638467752845324484045)
            ·
              refine ⟨13662989425407316996681517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36434638467752845324484045 13662989425407316996681517)
              ·
                refine ⟨5123621034527743873755569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13662989425407316996681517 5123621034527743873755569)
                ·
                  refine ⟨3842715775895807905316677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5123621034527743873755569 3842715775895807905316677)
                  ·
                    refine ⟨720509207980463982246877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3842715775895807905316677 720509207980463982246877)
                    ·
                      refine ⟨270190952992673993342579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 720509207980463982246877 270190952992673993342579)
                      ·
                        rfl

theorem cell23_526195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 3, 2, 4, 3].length) (baseStart_526195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_526195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_526195 prefixEnd_526195 := by exact prefixLift 526195
  have htrace : WordTrace (prefixWord ++ tailWord_526195) baseStart_526195 baseEnd_526195 := by
    simpa [prefixWord, tailWord_526195, baseEnd_526195] using wordTrace_append hprefix tailTrace_526195
  have hstable : (prefixWord ++ tailWord_526195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_526195).length < 2 ^ (prefixWord ++ tailWord_526195).sum := by decide
  have hdescent : baseEnd_526195 < baseStart_526195 := by decide
  rcases family_descends (prefixWord ++ tailWord_526195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_526205 : List Nat := [1, 4, 1, 1, 2, 1, 1, 3, 1, 4, 4]
def baseStart_526205 : Nat := 118140960795 + 526205 * 2 ^ 59
def prefixEnd_526205 : Nat := 4983230072969 + 3 ^ 40 * 526205 * 2
def baseEnd_526205 : Nat := 270196087799218954217533

theorem tailTrace_526205 : CollatzResearch.WordTrace tailWord_526205 prefixEnd_526205 270196087799218954217533 := by
  unfold tailWord_526205
  simp only [CollatzResearch.WordTrace]
  refine ⟨19192273058656628504300069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12794848705771085669533379 19192273058656628504300069)
  ·
    refine ⟨3598551198498117844556263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19192273058656628504300069 3598551198498117844556263)
    ·
      refine ⟨5397826797747176766834395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3598551198498117844556263 5397826797747176766834395)
      ·
        refine ⟨8096740196620765150251593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5397826797747176766834395 8096740196620765150251593)
        ·
          refine ⟨6072555147465573862688695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8096740196620765150251593 6072555147465573862688695)
          ·
            refine ⟨9108832721198360794033043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6072555147465573862688695 9108832721198360794033043)
            ·
              refine ⟨13663249081797541191049565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9108832721198360794033043 13663249081797541191049565)
              ·
                refine ⟨5123718405674077946643587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13663249081797541191049565 5123718405674077946643587)
                ·
                  refine ⟨7685577608511116919965381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5123718405674077946643587 7685577608511116919965381)
                  ·
                    refine ⟨1441045801595834422493509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7685577608511116919965381 1441045801595834422493509)
                    ·
                      refine ⟨270196087799218954217533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1441045801595834422493509 270196087799218954217533)
                      ·
                        rfl

theorem cell23_526205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 3, 1, 4, 4].length) (baseStart_526205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_526205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_526205 prefixEnd_526205 := by exact prefixLift 526205
  have htrace : WordTrace (prefixWord ++ tailWord_526205) baseStart_526205 baseEnd_526205 := by
    simpa [prefixWord, tailWord_526205, baseEnd_526205] using wordTrace_append hprefix tailTrace_526205
  have hstable : (prefixWord ++ tailWord_526205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_526205).length < 2 ^ (prefixWord ++ tailWord_526205).sum := by decide
  have hdescent : baseEnd_526205 < baseStart_526205 := by decide
  rcases family_descends (prefixWord ++ tailWord_526205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_526226 : List Nat := [3, 2, 3, 2, 1, 2, 1, 2, 1, 4, 2]
def baseStart_526226 : Nat := 118140960795 + 526226 * 2 ^ 59
def prefixEnd_526226 : Nat := 4983230072969 + 3 ^ 40 * 526226 * 2
def baseEnd_526226 : Nat := 270206870892963372054937

theorem tailTrace_526226 : CollatzResearch.WordTrace tailWord_526226 prefixEnd_526226 270206870892963372054937 := by
  unfold tailWord_526226
  simp only [CollatzResearch.WordTrace]
  refine ⟨4798259747895137272703633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12795359327720366060543021 4798259747895137272703633)
  ·
    refine ⟨3598694810921352954527725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4798259747895137272703633 3598694810921352954527725)
    ·
      refine ⟨1349510554095507357947897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3598694810921352954527725 1349510554095507357947897)
      ·
        refine ⟨1012132915571630518460923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1349510554095507357947897 1012132915571630518460923)
        ·
          refine ⟨1518199373357445777691385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1012132915571630518460923 1518199373357445777691385)
          ·
            refine ⟨1138649530018084333268539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1518199373357445777691385 1138649530018084333268539)
            ·
              refine ⟨1707974295027126499902809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1138649530018084333268539 1707974295027126499902809)
              ·
                refine ⟨1280980721270344874927107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1707974295027126499902809 1280980721270344874927107)
                ·
                  refine ⟨1921471081905517312390661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1280980721270344874927107 1921471081905517312390661)
                  ·
                    refine ⟨360275827857284496073249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1921471081905517312390661 360275827857284496073249)
                    ·
                      refine ⟨270206870892963372054937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 360275827857284496073249 270206870892963372054937)
                      ·
                        rfl

theorem cell23_526226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 1, 2, 1, 4, 2].length) (baseStart_526226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_526226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_526226 prefixEnd_526226 := by exact prefixLift 526226
  have htrace : WordTrace (prefixWord ++ tailWord_526226) baseStart_526226 baseEnd_526226 := by
    simpa [prefixWord, tailWord_526226, baseEnd_526226] using wordTrace_append hprefix tailTrace_526226
  have hstable : (prefixWord ++ tailWord_526226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_526226).length < 2 ^ (prefixWord ++ tailWord_526226).sum := by decide
  have hdescent : baseEnd_526226 < baseStart_526226 := by decide
  rcases family_descends (prefixWord ++ tailWord_526226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_526255 : List Nat := [1, 1, 2, 1, 2, 2, 3, 3, 1, 2, 5]
def baseStart_526255 : Nat := 118140960795 + 526255 * 2 ^ 59
def prefixEnd_526255 : Nat := 4983230072969 + 3 ^ 40 * 526255 * 2
def baseEnd_526255 : Nat := 270221761831943758592303

theorem tailTrace_526255 : CollatzResearch.WordTrace tailWord_526255 prefixEnd_526255 270221761831943758592303 := by
  unfold tailWord_526255
  simp only [CollatzResearch.WordTrace]
  refine ⟨19194096708475487043620219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12796064472316991362413479 19194096708475487043620219)
  ·
    refine ⟨28791145062713230565430329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19194096708475487043620219 28791145062713230565430329)
    ·
      refine ⟨21593358797034922924072747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28791145062713230565430329 21593358797034922924072747)
      ·
        refine ⟨32390038195552384386109121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21593358797034922924072747 32390038195552384386109121)
        ·
          refine ⟨24292528646664288289581841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32390038195552384386109121 24292528646664288289581841)
          ·
            refine ⟨18219396484998216217186381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24292528646664288289581841 18219396484998216217186381)
            ·
              refine ⟨6832273681874331081444893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18219396484998216217186381 6832273681874331081444893)
              ·
                refine ⟨2562102630702874155541835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6832273681874331081444893 2562102630702874155541835)
                ·
                  refine ⟨3843153946054311233312753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2562102630702874155541835 3843153946054311233312753)
                  ·
                    refine ⟨2882365459540733424984565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3843153946054311233312753 2882365459540733424984565)
                    ·
                      refine ⟨270221761831943758592303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2882365459540733424984565 270221761831943758592303)
                      ·
                        rfl

theorem cell23_526255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 3, 1, 2, 5].length) (baseStart_526255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_526255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_526255 prefixEnd_526255 := by exact prefixLift 526255
  have htrace : WordTrace (prefixWord ++ tailWord_526255) baseStart_526255 baseEnd_526255 := by
    simpa [prefixWord, tailWord_526255, baseEnd_526255] using wordTrace_append hprefix tailTrace_526255
  have hstable : (prefixWord ++ tailWord_526255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_526255).length < 2 ^ (prefixWord ++ tailWord_526255).sum := by decide
  have hdescent : baseEnd_526255 < baseStart_526255 := by decide
  rcases family_descends (prefixWord ++ tailWord_526255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_526295 : List Nat := [1, 1, 3, 2, 1, 1, 3, 1, 1, 3, 6]
def baseStart_526295 : Nat := 118140960795 + 526295 * 2 ^ 59
def prefixEnd_526295 : Nat := 4983230072969 + 3 ^ 40 * 526295 * 2
def baseEnd_526295 : Nat := 270242301058123602092119

theorem tailTrace_526295 : CollatzResearch.WordTrace tailWord_526295 prefixEnd_526295 270242301058123602092119 := by
  unfold tailWord_526295
  simp only [CollatzResearch.WordTrace]
  refine ⟨19195555628330573875076339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12797037085553715916717559 19195555628330573875076339)
  ·
    refine ⟨28793333442495860812614509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19195555628330573875076339 28793333442495860812614509)
    ·
      refine ⟨10797500040935947804730441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28793333442495860812614509 10797500040935947804730441)
      ·
        refine ⟨8098125030701960853547831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10797500040935947804730441 8098125030701960853547831)
        ·
          refine ⟨12147187546052941280321747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8098125030701960853547831 12147187546052941280321747)
          ·
            refine ⟨18220781319079411920482621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12147187546052941280321747 18220781319079411920482621)
            ·
              refine ⟨6832792994654779470180983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18220781319079411920482621 6832792994654779470180983)
              ·
                refine ⟨10249189491982169205271475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6832792994654779470180983 10249189491982169205271475)
                ·
                  refine ⟨15373784237973253807907213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10249189491982169205271475 15373784237973253807907213)
                  ·
                    refine ⟨5765169089239970177965205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15373784237973253807907213 5765169089239970177965205)
                    ·
                      refine ⟨270242301058123602092119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 5765169089239970177965205 270242301058123602092119)
                      ·
                        rfl

theorem cell23_526295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 1, 1, 3, 6].length) (baseStart_526295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_526295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_526295 prefixEnd_526295 := by exact prefixLift 526295
  have htrace : WordTrace (prefixWord ++ tailWord_526295) baseStart_526295 baseEnd_526295 := by
    simpa [prefixWord, tailWord_526295, baseEnd_526295] using wordTrace_append hprefix tailTrace_526295
  have hstable : (prefixWord ++ tailWord_526295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_526295).length < 2 ^ (prefixWord ++ tailWord_526295).sum := by decide
  have hdescent : baseEnd_526295 < baseStart_526295 := by decide
  rcases family_descends (prefixWord ++ tailWord_526295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_526332 : List Nat := [2, 2, 2, 1, 2, 2, 1, 1, 2, 5, 3]
def baseStart_526332 : Nat := 118140960795 + 526332 * 2 ^ 59
def prefixEnd_526332 : Nat := 4983230072969 + 3 ^ 40 * 526332 * 2
def baseEnd_526332 : Nat := 270261299842339957329449

theorem tailTrace_526332 : CollatzResearch.WordTrace tailWord_526332 prefixEnd_526332 270261299842339957329449 := by
  unfold tailWord_526332
  simp only [CollatzResearch.WordTrace]
  refine ⟨9598452564598264597086625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12797936752797686129448833 9598452564598264597086625)
  ·
    refine ⟨7198839423448698447814969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9598452564598264597086625 7198839423448698447814969)
    ·
      refine ⟨5399129567586523835861227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7198839423448698447814969 5399129567586523835861227)
      ·
        refine ⟨8098694351379785753791841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5399129567586523835861227 8098694351379785753791841)
        ·
          refine ⟨6074020763534839315343881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8098694351379785753791841 6074020763534839315343881)
          ·
            refine ⟨4555515572651129486507911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6074020763534839315343881 4555515572651129486507911)
            ·
              refine ⟨6833273358976694229761867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4555515572651129486507911 6833273358976694229761867)
              ·
                refine ⟨10249910038465041344642801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6833273358976694229761867 10249910038465041344642801)
                ·
                  refine ⟨7687432528848781008482101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10249910038465041344642801 7687432528848781008482101)
                  ·
                    refine ⟨720696799579573219545197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7687432528848781008482101 720696799579573219545197)
                    ·
                      refine ⟨270261299842339957329449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 720696799579573219545197 270261299842339957329449)
                      ·
                        rfl

theorem cell23_526332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 1, 2, 5, 3].length) (baseStart_526332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_526332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_526332 prefixEnd_526332 := by exact prefixLift 526332
  have htrace : WordTrace (prefixWord ++ tailWord_526332) baseStart_526332 baseEnd_526332 := by
    simpa [prefixWord, tailWord_526332, baseEnd_526332] using wordTrace_append hprefix tailTrace_526332
  have hstable : (prefixWord ++ tailWord_526332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_526332).length < 2 ^ (prefixWord ++ tailWord_526332).sum := by decide
  have hdescent : baseEnd_526332 < baseStart_526332 := by decide
  rcases family_descends (prefixWord ++ tailWord_526332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_526335 : List Nat := [1, 1, 2, 2, 1, 2, 1, 2, 2, 9]
def baseStart_526335 : Nat := 118140960795 + 526335 * 2 ^ 59
def prefixEnd_526335 : Nat := 4983230072969 + 3 ^ 40 * 526335 * 2
def baseEnd_526335 : Nat := 90087613428101148530645

theorem tailTrace_526335 : CollatzResearch.WordTrace tailWord_526335 prefixEnd_526335 90087613428101148530645 := by
  unfold tailWord_526335
  simp only [CollatzResearch.WordTrace]
  refine ⟨19197014548185660706532459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12798009698790440471021639 19197014548185660706532459)
  ·
    refine ⟨28795521822278491059798689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19197014548185660706532459 28795521822278491059798689)
    ·
      refine ⟨21596641366708868294849017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28795521822278491059798689 21596641366708868294849017)
      ·
        refine ⟨16197481025031651221136763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21596641366708868294849017 16197481025031651221136763)
        ·
          refine ⟨24296221537547476831705145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16197481025031651221136763 24296221537547476831705145)
          ·
            refine ⟨18222166153160607623778859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24296221537547476831705145 18222166153160607623778859)
            ·
              refine ⟨27333249229740911435668289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18222166153160607623778859 27333249229740911435668289)
              ·
                refine ⟨20499936922305683576751217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27333249229740911435668289 20499936922305683576751217)
                ·
                  refine ⟨15374952691729262682563413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20499936922305683576751217 15374952691729262682563413)
                  ·
                    refine ⟨90087613428101148530645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 15374952691729262682563413 90087613428101148530645)
                    ·
                      rfl

theorem cell23_526335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 2, 2, 9].length) (baseStart_526335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_526335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_526335 prefixEnd_526335 := by exact prefixLift 526335
  have htrace : WordTrace (prefixWord ++ tailWord_526335) baseStart_526335 baseEnd_526335 := by
    simpa [prefixWord, tailWord_526335, baseEnd_526335] using wordTrace_append hprefix tailTrace_526335
  have hstable : (prefixWord ++ tailWord_526335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_526335).length < 2 ^ (prefixWord ++ tailWord_526335).sum := by decide
  have hdescent : baseEnd_526335 < baseStart_526335 := by decide
  rcases family_descends (prefixWord ++ tailWord_526335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_526343 : List Nat := [1, 1, 4, 3, 1, 4, 1, 3, 1, 4]
def baseStart_526343 : Nat := 118140960795 + 526343 * 2 ^ 59
def prefixEnd_526343 : Nat := 4983230072969 + 3 ^ 40 * 526343 * 2
def baseEnd_526343 : Nat := 90088982709846471430633

theorem tailTrace_526343 : CollatzResearch.WordTrace tailWord_526343 prefixEnd_526343 90088982709846471430633 := by
  unfold tailWord_526343
  simp only [CollatzResearch.WordTrace]
  refine ⟨19197306332156678072823683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12798204221437785381882455 19197306332156678072823683)
  ·
    refine ⟨28795959498235017109235525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19197306332156678072823683 28795959498235017109235525)
    ·
      refine ⟨5399242405919065707981661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28795959498235017109235525 5399242405919065707981661)
      ·
        refine ⟨2024715902219649640493123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5399242405919065707981661 2024715902219649640493123)
        ·
          refine ⟨3037073853329474460739685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2024715902219649640493123 3037073853329474460739685)
          ·
            refine ⟨569451347499276461388691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3037073853329474460739685 569451347499276461388691)
            ·
              refine ⟨854177021248914692083037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 569451347499276461388691 854177021248914692083037)
              ·
                refine ⟨320316382968343009531139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 854177021248914692083037 320316382968343009531139)
                ·
                  refine ⟨480474574452514514296709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 320316382968343009531139 480474574452514514296709)
                  ·
                    refine ⟨90088982709846471430633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 480474574452514514296709 90088982709846471430633)
                    ·
                      rfl

theorem cell23_526343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 1, 3, 1, 4].length) (baseStart_526343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_526343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_526343 prefixEnd_526343 := by exact prefixLift 526343
  have htrace : WordTrace (prefixWord ++ tailWord_526343) baseStart_526343 baseEnd_526343 := by
    simpa [prefixWord, tailWord_526343, baseEnd_526343] using wordTrace_append hprefix tailTrace_526343
  have hstable : (prefixWord ++ tailWord_526343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_526343).length < 2 ^ (prefixWord ++ tailWord_526343).sum := by decide
  have hdescent : baseEnd_526343 < baseStart_526343 := by decide
  rcases family_descends (prefixWord ++ tailWord_526343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_526386 : List Nat := [3, 2, 1, 1, 2, 5, 1, 2, 1, 5]
def baseStart_526386 : Nat := 118140960795 + 526386 * 2 ^ 59
def prefixEnd_526386 : Nat := 4983230072969 + 3 ^ 40 * 526386 * 2
def baseEnd_526386 : Nat := 90096342599227582018067

theorem tailTrace_526386 : CollatzResearch.WordTrace tailWord_526386 prefixEnd_526386 90096342599227582018067 := by
  unfold tailWord_526386
  simp only [CollatzResearch.WordTrace]
  refine ⟨4799718667750224104159753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12799249780667264277759341 4799718667750224104159753)
  ·
    refine ⟨3599789000812668078119815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4799718667750224104159753 3599789000812668078119815)
    ·
      refine ⟨5399683501219002117179723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3599789000812668078119815 5399683501219002117179723)
      ·
        refine ⟨8099525251828503175769585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5399683501219002117179723 8099525251828503175769585)
        ·
          refine ⟨6074643938871377381827189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8099525251828503175769585 6074643938871377381827189)
          ·
            refine ⟨569497869269191629546299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6074643938871377381827189 569497869269191629546299)
            ·
              refine ⟨854246803903787444319449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 569497869269191629546299 854246803903787444319449)
              ·
                refine ⟨640685102927840583239587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 854246803903787444319449 640685102927840583239587)
                ·
                  refine ⟨961027654391760874859381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 640685102927840583239587 961027654391760874859381)
                  ·
                    refine ⟨90096342599227582018067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 961027654391760874859381 90096342599227582018067)
                    ·
                      rfl

theorem cell23_526386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 1, 2, 1, 5].length) (baseStart_526386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_526386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_526386 prefixEnd_526386 := by exact prefixLift 526386
  have htrace : WordTrace (prefixWord ++ tailWord_526386) baseStart_526386 baseEnd_526386 := by
    simpa [prefixWord, tailWord_526386, baseEnd_526386] using wordTrace_append hprefix tailTrace_526386
  have hstable : (prefixWord ++ tailWord_526386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_526386).length < 2 ^ (prefixWord ++ tailWord_526386).sum := by decide
  have hdescent : baseEnd_526386 < baseStart_526386 := by decide
  rcases family_descends (prefixWord ++ tailWord_526386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_526389 : List Nat := [1, 3, 3, 1, 1, 1, 2, 1, 2, 6, 2]
def baseStart_526389 : Nat := 118140960795 + 526389 * 2 ^ 59
def prefixEnd_526389 : Nat := 4983230072969 + 3 ^ 40 * 526389 * 2
def baseEnd_526389 : Nat := 270290568239646234316687

theorem tailTrace_526389 : CollatzResearch.WordTrace tailWord_526389 prefixEnd_526389 270290568239646234316687 := by
  unfold tailWord_526389
  simp only [CollatzResearch.WordTrace]
  refine ⟨19198984089990027928998221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12799322726660018619332147 19198984089990027928998221)
  ·
    refine ⟨7199619033746260473374333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19198984089990027928998221 7199619033746260473374333)
    ·
      refine ⟨2699857137654847677515375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7199619033746260473374333 2699857137654847677515375)
      ·
        refine ⟨4049785706482271516273063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2699857137654847677515375 4049785706482271516273063)
        ·
          refine ⟨6074678559723407274409595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4049785706482271516273063 6074678559723407274409595)
          ·
            refine ⟨9112017839585110911614393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6074678559723407274409595 9112017839585110911614393)
            ·
              refine ⟨6834013379688833183710795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9112017839585110911614393 6834013379688833183710795)
              ·
                refine ⟨10251020069533249775566193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6834013379688833183710795 10251020069533249775566193)
                ·
                  refine ⟨7688265052149937331674645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10251020069533249775566193 7688265052149937331674645)
                  ·
                    refine ⟨360387424319528312422249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7688265052149937331674645 360387424319528312422249)
                    ·
                      refine ⟨270290568239646234316687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 360387424319528312422249 270290568239646234316687)
                      ·
                        rfl

theorem cell23_526389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 1, 2, 6, 2].length) (baseStart_526389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_526389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_526389 prefixEnd_526389 := by exact prefixLift 526389
  have htrace : WordTrace (prefixWord ++ tailWord_526389) baseStart_526389 baseEnd_526389 := by
    simpa [prefixWord, tailWord_526389, baseEnd_526389] using wordTrace_append hprefix tailTrace_526389
  have hstable : (prefixWord ++ tailWord_526389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_526389).length < 2 ^ (prefixWord ++ tailWord_526389).sum := by decide
  have hdescent : baseEnd_526389 < baseStart_526389 := by decide
  rcases family_descends (prefixWord ++ tailWord_526389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_526393 : List Nat := [1, 2, 1, 5, 3, 1, 2, 1, 2, 3, 2]
def baseStart_526393 : Nat := 118140960795 + 526393 * 2 ^ 59
def prefixEnd_526393 : Nat := 4983230072969 + 3 ^ 40 * 526393 * 2
def baseEnd_526393 : Nat := 270292622162264218666669

theorem tailTrace_526393 : CollatzResearch.WordTrace tailWord_526393 prefixEnd_526393 270292622162264218666669 := by
  unfold tailWord_526393
  simp only [CollatzResearch.WordTrace]
  refine ⟨19199129981975536612143833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12799419987983691074762555 19199129981975536612143833)
  ·
    refine ⟨14399347486481652459107875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19199129981975536612143833 14399347486481652459107875)
    ·
      refine ⟨21599021229722478688661813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14399347486481652459107875 21599021229722478688661813)
      ·
        refine ⟨2024908240286482377062045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 21599021229722478688661813 2024908240286482377062045)
        ·
          refine ⟨759340590107430891398267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2024908240286482377062045 759340590107430891398267)
          ·
            refine ⟨1139010885161146337097401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 759340590107430891398267 1139010885161146337097401)
            ·
              refine ⟨854258163870859752823051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1139010885161146337097401 854258163870859752823051)
              ·
                refine ⟨1281387245806289629234577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 854258163870859752823051 1281387245806289629234577)
                ·
                  refine ⟨961040434354717221925933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1281387245806289629234577 961040434354717221925933)
                  ·
                    refine ⟨360390162883018958222225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 961040434354717221925933 360390162883018958222225)
                    ·
                      refine ⟨270292622162264218666669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 360390162883018958222225 270292622162264218666669)
                      ·
                        rfl

theorem cell23_526393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 2, 1, 2, 3, 2].length) (baseStart_526393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_526393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_526393 prefixEnd_526393 := by exact prefixLift 526393
  have htrace : WordTrace (prefixWord ++ tailWord_526393) baseStart_526393 baseEnd_526393 := by
    simpa [prefixWord, tailWord_526393, baseEnd_526393] using wordTrace_append hprefix tailTrace_526393
  have hstable : (prefixWord ++ tailWord_526393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_526393).length < 2 ^ (prefixWord ++ tailWord_526393).sum := by decide
  have hdescent : baseEnd_526393 < baseStart_526393 := by decide
  rcases family_descends (prefixWord ++ tailWord_526393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_526490 : List Nat := [3, 1, 1, 5, 3, 1, 1, 1, 1, 3, 3]
def baseStart_526490 : Nat := 118140960795 + 526490 * 2 ^ 59
def prefixEnd_526490 : Nat := 4983230072969 + 3 ^ 40 * 526490 * 2
def baseEnd_526490 : Nat := 270342429785750339153723

theorem tailTrace_526490 : CollatzResearch.WordTrace tailWord_526490 prefixEnd_526490 270342429785750339153723 := by
  unfold tailWord_526490
  simp only [CollatzResearch.WordTrace]
  refine ⟨4800666965656030544606231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12801778575082748118949949 4800666965656030544606231)
  ·
    refine ⟨7201000448484045816909347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4800666965656030544606231 7201000448484045816909347)
    ·
      refine ⟨10801500672726068725364021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7201000448484045816909347 10801500672726068725364021)
      ·
        refine ⟨1012640688068068943002877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10801500672726068725364021 1012640688068068943002877)
        ·
          refine ⟨379740258025525853626079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1012640688068068943002877 379740258025525853626079)
          ·
            refine ⟨569610387038288780439119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 379740258025525853626079 569610387038288780439119)
            ·
              refine ⟨854415580557433170658679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 569610387038288780439119 854415580557433170658679)
              ·
                refine ⟨1281623370836149755988019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 854415580557433170658679 1281623370836149755988019)
                ·
                  refine ⟨1922435056254224633982029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1281623370836149755988019 1922435056254224633982029)
                  ·
                    refine ⟨720913146095334237743261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1922435056254224633982029 720913146095334237743261)
                    ·
                      refine ⟨270342429785750339153723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 720913146095334237743261 270342429785750339153723)
                      ·
                        rfl

theorem cell23_526490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 1, 1, 1, 3, 3].length) (baseStart_526490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_526490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_526490 prefixEnd_526490 := by exact prefixLift 526490
  have htrace : WordTrace (prefixWord ++ tailWord_526490) baseStart_526490 baseEnd_526490 := by
    simpa [prefixWord, tailWord_526490, baseEnd_526490] using wordTrace_append hprefix tailTrace_526490
  have hstable : (prefixWord ++ tailWord_526490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_526490).length < 2 ^ (prefixWord ++ tailWord_526490).sum := by decide
  have hdescent : baseEnd_526490 < baseStart_526490 := by decide
  rcases family_descends (prefixWord ++ tailWord_526490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_526500 : List Nat := [2, 3, 1, 2, 4, 1, 2, 2, 1, 3, 2]
def baseStart_526500 : Nat := 118140960795 + 526500 * 2 ^ 59
def prefixEnd_526500 : Nat := 4983230072969 + 3 ^ 40 * 526500 * 2
def baseEnd_526500 : Nat := 270347564592295300028677

theorem tailTrace_526500 : CollatzResearch.WordTrace tailWord_526500 prefixEnd_526500 270347564592295300028677 := by
  unfold tailWord_526500
  simp only [CollatzResearch.WordTrace]
  refine ⟨9601516296293946943144477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12802021728391929257525969 9601516296293946943144477)
  ·
    refine ⟨3600568611110230103679179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9601516296293946943144477 3600568611110230103679179)
    ·
      refine ⟨5400852916665345155518769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3600568611110230103679179 5400852916665345155518769)
      ·
        refine ⟨4050639687499008866639077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5400852916665345155518769 4050639687499008866639077)
        ·
          refine ⟨759494941406064162494827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4050639687499008866639077 759494941406064162494827)
          ·
            refine ⟨1139242412109096243742241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 759494941406064162494827 1139242412109096243742241)
            ·
              refine ⟨854431809081822182806681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1139242412109096243742241 854431809081822182806681)
              ·
                refine ⟨640823856811366637105011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 854431809081822182806681 640823856811366637105011)
                ·
                  refine ⟨961235785217049955657517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 640823856811366637105011 961235785217049955657517)
                  ·
                    refine ⟨360463419456393733371569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 961235785217049955657517 360463419456393733371569)
                    ·
                      refine ⟨270347564592295300028677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 360463419456393733371569 270347564592295300028677)
                      ·
                        rfl

theorem cell23_526500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 2, 2, 1, 3, 2].length) (baseStart_526500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_526500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_526500 prefixEnd_526500 := by exact prefixLift 526500
  have htrace : WordTrace (prefixWord ++ tailWord_526500) baseStart_526500 baseEnd_526500 := by
    simpa [prefixWord, tailWord_526500, baseEnd_526500] using wordTrace_append hprefix tailTrace_526500
  have hstable : (prefixWord ++ tailWord_526500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_526500).length < 2 ^ (prefixWord ++ tailWord_526500).sum := by decide
  have hdescent : baseEnd_526500 < baseStart_526500 := by decide
  rcases family_descends (prefixWord ++ tailWord_526500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_526512 : List Nat := [2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 7]
def baseStart_526512 : Nat := 118140960795 + 526512 * 2 ^ 59
def prefixEnd_526512 : Nat := 4983230072969 + 3 ^ 40 * 526512 * 2
def baseEnd_526512 : Nat := 270353726360149253078621

theorem tailTrace_526512 : CollatzResearch.WordTrace tailWord_526512 prefixEnd_526512 270353726360149253078621 := by
  unfold tailWord_526512
  simp only [CollatzResearch.WordTrace]
  refine ⟨9601735134272209967862895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12802313512362946623817193 9601735134272209967862895)
  ·
    refine ⟨14402602701408314951794343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9601735134272209967862895 14402602701408314951794343)
    ·
      refine ⟨21603904052112472427691515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14402602701408314951794343 21603904052112472427691515)
      ·
        refine ⟨32405856078168708641537273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21603904052112472427691515 32405856078168708641537273)
        ·
          refine ⟨24304392058626531481152955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32405856078168708641537273 24304392058626531481152955)
          ·
            refine ⟨36456588087939797221729433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24304392058626531481152955 36456588087939797221729433)
            ·
              refine ⟨27342441065954847916297075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36456588087939797221729433 27342441065954847916297075)
              ·
                refine ⟨41013661598932271874445613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27342441065954847916297075 41013661598932271874445613)
                ·
                  refine ⟨15380123099599601952917105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41013661598932271874445613 15380123099599601952917105)
                  ·
                    refine ⟨11535092324699701464687829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15380123099599601952917105 11535092324699701464687829)
                    ·
                      refine ⟨270353726360149253078621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 11535092324699701464687829 270353726360149253078621)
                      ·
                        rfl

theorem cell23_526512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 7].length) (baseStart_526512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_526512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_526512 prefixEnd_526512 := by exact prefixLift 526512
  have htrace : WordTrace (prefixWord ++ tailWord_526512) baseStart_526512 baseEnd_526512 := by
    simpa [prefixWord, tailWord_526512, baseEnd_526512] using wordTrace_append hprefix tailTrace_526512
  have hstable : (prefixWord ++ tailWord_526512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_526512).length < 2 ^ (prefixWord ++ tailWord_526512).sum := by decide
  have hdescent : baseEnd_526512 < baseStart_526512 := by decide
  rcases family_descends (prefixWord ++ tailWord_526512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_526569 : List Nat := [1, 2, 1, 1, 1, 2, 2, 2, 6, 1, 4]
def baseStart_526569 : Nat := 118140960795 + 526569 * 2 ^ 59
def prefixEnd_526569 : Nat := 4983230072969 + 3 ^ 40 * 526569 * 2
def baseEnd_526569 : Nat := 270382994757455530065859

theorem tailTrace_526569 : CollatzResearch.WordTrace tailWord_526569 prefixEnd_526569 270382994757455530065859 := by
  unfold tailWord_526569
  simp only [CollatzResearch.WordTrace]
  refine ⟨19205549229337918670550761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12803699486225279113700507 19205549229337918670550761)
  ·
    refine ⟨14404161922003439002913071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19205549229337918670550761 14404161922003439002913071)
    ·
      refine ⟨21606242883005158504369607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14404161922003439002913071 21606242883005158504369607)
      ·
        refine ⟨32409364324507737756554411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21606242883005158504369607 32409364324507737756554411)
        ·
          refine ⟨48614046486761606634831617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32409364324507737756554411 48614046486761606634831617)
          ·
            refine ⟨36460534865071204976123713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48614046486761606634831617 36460534865071204976123713)
            ·
              refine ⟨27345401148803403732092785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36460534865071204976123713 27345401148803403732092785)
              ·
                refine ⟨20509050861602552799069589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27345401148803403732092785 20509050861602552799069589)
                ·
                  refine ⟨961361759137619662456387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 20509050861602552799069589 961361759137619662456387)
                  ·
                    refine ⟨1442042638706429493684581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 961361759137619662456387 1442042638706429493684581)
                    ·
                      refine ⟨270382994757455530065859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1442042638706429493684581 270382994757455530065859)
                      ·
                        rfl

theorem cell23_526569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 2, 6, 1, 4].length) (baseStart_526569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_526569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_526569 prefixEnd_526569 := by exact prefixLift 526569
  have htrace : WordTrace (prefixWord ++ tailWord_526569) baseStart_526569 baseEnd_526569 := by
    simpa [prefixWord, tailWord_526569, baseEnd_526569] using wordTrace_append hprefix tailTrace_526569
  have hstable : (prefixWord ++ tailWord_526569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_526569).length < 2 ^ (prefixWord ++ tailWord_526569).sum := by decide
  have hdescent : baseEnd_526569 < baseStart_526569 := by decide
  rcases family_descends (prefixWord ++ tailWord_526569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_526586 : List Nat := [3, 1, 1, 1, 1, 5, 2, 2, 2, 1, 4]
def baseStart_526586 : Nat := 118140960795 + 526586 * 2 ^ 59
def prefixEnd_526586 : Nat := 4983230072969 + 3 ^ 40 * 526586 * 2
def baseEnd_526586 : Nat := 270391723928581963553281

theorem tailTrace_526586 : CollatzResearch.WordTrace tailWord_526586 prefixEnd_526586 270391723928581963553281 := by
  unfold tailWord_526586
  simp only [CollatzResearch.WordTrace]
  refine ⟨4801542317569082643479903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12804112846850887049279741 4801542317569082643479903)
  ·
    refine ⟨7202313476353623965219855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4801542317569082643479903 7202313476353623965219855)
    ·
      refine ⟨10803470214530435947829783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7202313476353623965219855 10803470214530435947829783)
      ·
        refine ⟨16205205321795653921744675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10803470214530435947829783 16205205321795653921744675)
        ·
          refine ⟨24307807982693480882617013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16205205321795653921744675 24307807982693480882617013)
          ·
            refine ⟨2278856998377513832745345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 24307807982693480882617013 2278856998377513832745345)
            ·
              refine ⟨1709142748783135374559009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2278856998377513832745345 1709142748783135374559009)
              ·
                refine ⟨1281857061587351530919257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1709142748783135374559009 1281857061587351530919257)
                ·
                  refine ⟨961392796190513648189443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1281857061587351530919257 961392796190513648189443)
                  ·
                    refine ⟨1442089194285770472284165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 961392796190513648189443 1442089194285770472284165)
                    ·
                      refine ⟨270391723928581963553281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1442089194285770472284165 270391723928581963553281)
                      ·
                        rfl

theorem cell23_526586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 2, 2, 2, 1, 4].length) (baseStart_526586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_526586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_526586 prefixEnd_526586 := by exact prefixLift 526586
  have htrace : WordTrace (prefixWord ++ tailWord_526586) baseStart_526586 baseEnd_526586 := by
    simpa [prefixWord, tailWord_526586, baseEnd_526586] using wordTrace_append hprefix tailTrace_526586
  have hstable : (prefixWord ++ tailWord_526586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_526586).length < 2 ^ (prefixWord ++ tailWord_526586).sum := by decide
  have hdescent : baseEnd_526586 < baseStart_526586 := by decide
  rcases family_descends (prefixWord ++ tailWord_526586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_526606 : List Nat := [4, 1, 1, 2, 1, 2, 2, 2, 1, 4, 3]
def baseStart_526606 : Nat := 118140960795 + 526606 * 2 ^ 59
def prefixEnd_526606 : Nat := 4983230072969 + 3 ^ 40 * 526606 * 2
def baseEnd_526606 : Nat := 270401993541671885303189

theorem tailTrace_526606 : CollatzResearch.WordTrace tailWord_526606 prefixEnd_526606 270401993541671885303189 := by
  unfold tailWord_526606
  simp only [CollatzResearch.WordTrace]
  refine ⟨2400862341275484248705959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12804599153469249326431781 2400862341275484248705959)
  ·
    refine ⟨3601293511913226373058939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2400862341275484248705959 3601293511913226373058939)
    ·
      refine ⟨5401940267869839559588409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3601293511913226373058939 5401940267869839559588409)
      ·
        refine ⟨4051455200902379669691307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5401940267869839559588409 4051455200902379669691307)
        ·
          refine ⟨6077182801353569504536961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4051455200902379669691307 6077182801353569504536961)
          ·
            refine ⟨4557887101015177128402721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6077182801353569504536961 4557887101015177128402721)
            ·
              refine ⟨3418415325761382846302041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4557887101015177128402721 3418415325761382846302041)
              ·
                refine ⟨2563811494321037134726531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3418415325761382846302041 2563811494321037134726531)
                ·
                  refine ⟨3845717241481555702089797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2563811494321037134726531 3845717241481555702089797)
                  ·
                    refine ⟨721071982777791694141837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3845717241481555702089797 721071982777791694141837)
                    ·
                      refine ⟨270401993541671885303189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 721071982777791694141837 270401993541671885303189)
                      ·
                        rfl

theorem cell23_526606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 2, 1, 4, 3].length) (baseStart_526606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_526606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_526606 prefixEnd_526606 := by exact prefixLift 526606
  have htrace : WordTrace (prefixWord ++ tailWord_526606) baseStart_526606 baseEnd_526606 := by
    simpa [prefixWord, tailWord_526606, baseEnd_526606] using wordTrace_append hprefix tailTrace_526606
  have hstable : (prefixWord ++ tailWord_526606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_526606).length < 2 ^ (prefixWord ++ tailWord_526606).sum := by decide
  have hdescent : baseEnd_526606 < baseStart_526606 := by decide
  rcases family_descends (prefixWord ++ tailWord_526606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_526623 : List Nat := [1, 1, 2, 4, 3, 1, 3, 1, 2, 2, 3]
def baseStart_526623 : Nat := 118140960795 + 526623 * 2 ^ 59
def prefixEnd_526623 : Nat := 4983230072969 + 3 ^ 40 * 526623 * 2
def baseEnd_526623 : Nat := 270410722712798318790611

theorem tailTrace_526623 : CollatzResearch.WordTrace tailWord_526623 prefixEnd_526623 270410722712798318790611 := by
  unfold tailWord_526623
  simp only [CollatzResearch.WordTrace]
  refine ⟨19207518771142285893016523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12805012514094857262011015 19207518771142285893016523)
  ·
    refine ⟨28811278156713428839524785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19207518771142285893016523 28811278156713428839524785)
    ·
      refine ⟨21608458617535071629643589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28811278156713428839524785 21608458617535071629643589)
      ·
        refine ⟨4051585990787825930558173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21608458617535071629643589 4051585990787825930558173)
        ·
          refine ⟨1519344746545434723959315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4051585990787825930558173 1519344746545434723959315)
          ·
            refine ⟨2279017119818152085938973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1519344746545434723959315 2279017119818152085938973)
            ·
              refine ⟨854631419931807032227115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2279017119818152085938973 854631419931807032227115)
              ·
                refine ⟨1281947129897710548340673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 854631419931807032227115 1281947129897710548340673)
                ·
                  refine ⟨961460347423282911255505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1281947129897710548340673 961460347423282911255505)
                  ·
                    refine ⟨721095260567462183441629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 961460347423282911255505 721095260567462183441629)
                    ·
                      refine ⟨270410722712798318790611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 721095260567462183441629 270410722712798318790611)
                      ·
                        rfl

theorem cell23_526623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 3, 1, 2, 2, 3].length) (baseStart_526623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_526623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_526623 prefixEnd_526623 := by exact prefixLift 526623
  have htrace : WordTrace (prefixWord ++ tailWord_526623) baseStart_526623 baseEnd_526623 := by
    simpa [prefixWord, tailWord_526623, baseEnd_526623] using wordTrace_append hprefix tailTrace_526623
  have hstable : (prefixWord ++ tailWord_526623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_526623).length < 2 ^ (prefixWord ++ tailWord_526623).sum := by decide
  have hdescent : baseEnd_526623 < baseStart_526623 := by decide
  rcases family_descends (prefixWord ++ tailWord_526623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_526673 : List Nat := [1, 2, 2, 1, 4, 3, 2, 2, 1, 5]
def baseStart_526673 : Nat := 118140960795 + 526673 * 2 ^ 59
def prefixEnd_526673 : Nat := 4983230072969 + 3 ^ 40 * 526673 * 2
def baseEnd_526673 : Nat := 90145465581841041055127

theorem tailTrace_526673 : CollatzResearch.WordTrace tailWord_526673 prefixEnd_526673 90145465581841041055127 := by
  unfold tailWord_526673
  simp only [CollatzResearch.WordTrace]
  refine ⟨19209342420961144432336673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12806228280640762954891115 19209342420961144432336673)
  ·
    refine ⟨14407006815720858324252505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19209342420961144432336673 14407006815720858324252505)
    ·
      refine ⟨10805255111790643743189379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14407006815720858324252505 10805255111790643743189379)
      ·
        refine ⟨16207882667685965614784069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10805255111790643743189379 16207882667685965614784069)
        ·
          refine ⟨3038978000191118552772013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16207882667685965614784069 3038978000191118552772013)
          ·
            refine ⟨1139616750071669457289505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3038978000191118552772013 1139616750071669457289505)
            ·
              refine ⟨854712562553752092967129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1139616750071669457289505 854712562553752092967129)
              ·
                refine ⟨641034421915314069725347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 854712562553752092967129 641034421915314069725347)
                ·
                  refine ⟨961551632872971104588021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 641034421915314069725347 961551632872971104588021)
                  ·
                    refine ⟨90145465581841041055127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 961551632872971104588021 90145465581841041055127)
                    ·
                      rfl

theorem cell23_526673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 2, 2, 1, 5].length) (baseStart_526673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_526673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_526673 prefixEnd_526673 := by exact prefixLift 526673
  have htrace : WordTrace (prefixWord ++ tailWord_526673) baseStart_526673 baseEnd_526673 := by
    simpa [prefixWord, tailWord_526673, baseEnd_526673] using wordTrace_append hprefix tailTrace_526673
  have hstable : (prefixWord ++ tailWord_526673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_526673).length < 2 ^ (prefixWord ++ tailWord_526673).sum := by decide
  have hdescent : baseEnd_526673 < baseStart_526673 := by decide
  rcases family_descends (prefixWord ++ tailWord_526673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_526693 : List Nat := [1, 3, 1, 3, 1, 3, 2, 3, 1, 1, 4]
def baseStart_526693 : Nat := 118140960795 + 526693 * 2 ^ 59
def prefixEnd_526693 : Nat := 4983230072969 + 3 ^ 40 * 526693 * 2
def baseEnd_526693 : Nat := 270446666358613044915289

theorem tailTrace_526693 : CollatzResearch.WordTrace tailWord_526693 prefixEnd_526693 270446666358613044915289 := by
  unfold tailWord_526693
  simp only [CollatzResearch.WordTrace]
  refine ⟨19210071880888687848064733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12806714587259125232043155 19210071880888687848064733)
  ·
    refine ⟨7203776955333257943024275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19210071880888687848064733 7203776955333257943024275)
    ·
      refine ⟨10805665432999886914536413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7203776955333257943024275 10805665432999886914536413)
      ·
        refine ⟨4052124537374957592951155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10805665432999886914536413 4052124537374957592951155)
        ·
          refine ⟨6078186806062436389426733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4052124537374957592951155 6078186806062436389426733)
          ·
            refine ⟨2279320052273413646035025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6078186806062436389426733 2279320052273413646035025)
            ·
              refine ⟨1709490039205060234526269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2279320052273413646035025 1709490039205060234526269)
              ·
                refine ⟨641058764701897587947351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1709490039205060234526269 641058764701897587947351)
                ·
                  refine ⟨961588147052846381921027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 641058764701897587947351 961588147052846381921027)
                  ·
                    refine ⟨1442382220579269572881541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 961588147052846381921027 1442382220579269572881541)
                    ·
                      refine ⟨270446666358613044915289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1442382220579269572881541 270446666358613044915289)
                      ·
                        rfl

theorem cell23_526693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 2, 3, 1, 1, 4].length) (baseStart_526693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_526693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_526693 prefixEnd_526693 := by exact prefixLift 526693
  have htrace : WordTrace (prefixWord ++ tailWord_526693) baseStart_526693 baseEnd_526693 := by
    simpa [prefixWord, tailWord_526693, baseEnd_526693] using wordTrace_append hprefix tailTrace_526693
  have hstable : (prefixWord ++ tailWord_526693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_526693).length < 2 ^ (prefixWord ++ tailWord_526693).sum := by decide
  have hdescent : baseEnd_526693 < baseStart_526693 := by decide
  rcases family_descends (prefixWord ++ tailWord_526693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_526706 : List Nat := [3, 2, 1, 2, 1, 3, 1, 2, 1, 1, 6]
def baseStart_526706 : Nat := 118140960795 + 526706 * 2 ^ 59
def prefixEnd_526706 : Nat := 4983230072969 + 3 ^ 40 * 526706 * 2
def baseEnd_526706 : Nat := 270453341607121494052729

theorem tailTrace_526706 : CollatzResearch.WordTrace tailWord_526706 prefixEnd_526706 270453341607121494052729 := by
  unfold tailWord_526706
  simp only [CollatzResearch.WordTrace]
  refine ⟨4802636507460397767071993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12807030686561060712191981 4802636507460397767071993)
  ·
    refine ⟨3601977380595298325303995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4802636507460397767071993 3601977380595298325303995)
    ·
      refine ⟨5402966070892947487955993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3601977380595298325303995 5402966070892947487955993)
      ·
        refine ⟨4052224553169710615966995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5402966070892947487955993 4052224553169710615966995)
        ·
          refine ⟨6078336829754565923950493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4052224553169710615966995 6078336829754565923950493)
          ·
            refine ⟨2279376311157962221481435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6078336829754565923950493 2279376311157962221481435)
            ·
              refine ⟨3419064466736943332222153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2279376311157962221481435 3419064466736943332222153)
              ·
                refine ⟨2564298350052707499166615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3419064466736943332222153 2564298350052707499166615)
                ·
                  refine ⟨3846447525079061248749923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2564298350052707499166615 3846447525079061248749923)
                  ·
                    refine ⟨5769671287618591873124885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3846447525079061248749923 5769671287618591873124885)
                    ·
                      refine ⟨270453341607121494052729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 5769671287618591873124885 270453341607121494052729)
                      ·
                        rfl

theorem cell23_526706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 2, 1, 1, 6].length) (baseStart_526706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_526706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_526706 prefixEnd_526706 := by exact prefixLift 526706
  have htrace : WordTrace (prefixWord ++ tailWord_526706) baseStart_526706 baseEnd_526706 := by
    simpa [prefixWord, tailWord_526706, baseEnd_526706] using wordTrace_append hprefix tailTrace_526706
  have hstable : (prefixWord ++ tailWord_526706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_526706).length < 2 ^ (prefixWord ++ tailWord_526706).sum := by decide
  have hdescent : baseEnd_526706 < baseStart_526706 := by decide
  rcases family_descends (prefixWord ++ tailWord_526706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_526740 : List Nat := [2, 4, 2, 1, 3, 1, 1, 2, 1, 2, 4]
def baseStart_526740 : Nat := 118140960795 + 526740 * 2 ^ 59
def prefixEnd_526740 : Nat := 4983230072969 + 3 ^ 40 * 526740 * 2
def baseEnd_526740 : Nat := 270470799949374361027573

theorem tailTrace_526740 : CollatzResearch.WordTrace tailWord_526740 prefixEnd_526740 270470799949374361027573 := by
  unfold tailWord_526740
  simp only [CollatzResearch.WordTrace]
  refine ⟨9605893055859207437512837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12807857407812276583350449 9605893055859207437512837)
  ·
    refine ⟨1801104947973601394533657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9605893055859207437512837 1801104947973601394533657)
    ·
      refine ⟨1350828710980201045900243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1801104947973601394533657 1350828710980201045900243)
      ·
        refine ⟨2026243066470301568850365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1350828710980201045900243 2026243066470301568850365)
        ·
          refine ⟨759841149926363088318887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2026243066470301568850365 759841149926363088318887)
          ·
            refine ⟨1139761724889544632478331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 759841149926363088318887 1139761724889544632478331)
            ·
              refine ⟨1709642587334316948717497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1139761724889544632478331 1709642587334316948717497)
              ·
                refine ⟨1282231940500737711538123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1709642587334316948717497 1282231940500737711538123)
                ·
                  refine ⟨1923347910751106567307185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1282231940500737711538123 1923347910751106567307185)
                  ·
                    refine ⟨1442510933063329925480389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1923347910751106567307185 1442510933063329925480389)
                    ·
                      refine ⟨270470799949374361027573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1442510933063329925480389 270470799949374361027573)
                      ·
                        rfl

theorem cell23_526740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 1, 2, 1, 2, 4].length) (baseStart_526740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_526740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_526740 prefixEnd_526740 := by exact prefixLift 526740
  have htrace : WordTrace (prefixWord ++ tailWord_526740) baseStart_526740 baseEnd_526740 := by
    simpa [prefixWord, tailWord_526740, baseEnd_526740] using wordTrace_append hprefix tailTrace_526740
  have hstable : (prefixWord ++ tailWord_526740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_526740).length < 2 ^ (prefixWord ++ tailWord_526740).sum := by decide
  have hdescent : baseEnd_526740 < baseStart_526740 := by decide
  rcases family_descends (prefixWord ++ tailWord_526740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_526743 : List Nat := [1, 1, 3, 3, 1, 1, 2, 1, 6, 1, 3]
def baseStart_526743 : Nat := 118140960795 + 526743 * 2 ^ 59
def prefixEnd_526743 : Nat := 4983230072969 + 3 ^ 40 * 526743 * 2
def baseEnd_526743 : Nat := 270472340391337849290059

theorem tailTrace_526743 : CollatzResearch.WordTrace tailWord_526743 prefixEnd_526743 270472340391337849290059 := by
  unfold tailWord_526743
  simp only [CollatzResearch.WordTrace]
  refine ⟨19211895530707546387384883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12807930353805030924923255 19211895530707546387384883)
  ·
    refine ⟨28817843296061319581077325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19211895530707546387384883 28817843296061319581077325)
    ·
      refine ⟨10806691236022994842903997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28817843296061319581077325 10806691236022994842903997)
      ·
        refine ⟨4052509213508623066088999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10806691236022994842903997 4052509213508623066088999)
        ·
          refine ⟨6078763820262934599133499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4052509213508623066088999 6078763820262934599133499)
          ·
            refine ⟨9118145730394401898700249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6078763820262934599133499 9118145730394401898700249)
            ·
              refine ⟨6838609297795801424025187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9118145730394401898700249 6838609297795801424025187)
              ·
                refine ⟨10257913946693702136037781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6838609297795801424025187 10257913946693702136037781)
                ·
                  refine ⟨480839716251267287626771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10257913946693702136037781 480839716251267287626771)
                  ·
                    refine ⟨721259574376900931440157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 480839716251267287626771 721259574376900931440157)
                    ·
                      refine ⟨270472340391337849290059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 721259574376900931440157 270472340391337849290059)
                      ·
                        rfl

theorem cell23_526743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 1, 6, 1, 3].length) (baseStart_526743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_526743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_526743 prefixEnd_526743 := by exact prefixLift 526743
  have htrace : WordTrace (prefixWord ++ tailWord_526743) baseStart_526743 baseEnd_526743 := by
    simpa [prefixWord, tailWord_526743, baseEnd_526743] using wordTrace_append hprefix tailTrace_526743
  have hstable : (prefixWord ++ tailWord_526743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_526743).length < 2 ^ (prefixWord ++ tailWord_526743).sum := by decide
  have hdescent : baseEnd_526743 < baseStart_526743 := by decide
  rcases family_descends (prefixWord ++ tailWord_526743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_526756 : List Nat := [2, 3, 1, 2, 1, 1, 2, 2, 2, 2, 5]
def baseStart_526756 : Nat := 118140960795 + 526756 * 2 ^ 59
def prefixEnd_526756 : Nat := 4983230072969 + 3 ^ 40 * 526756 * 2
def baseEnd_526756 : Nat := 270479015639846298427499

theorem tailTrace_526756 : CollatzResearch.WordTrace tailWord_526756 prefixEnd_526756 270479015639846298427499 := by
  unfold tailWord_526756
  simp only [CollatzResearch.WordTrace]
  refine ⟨9606184839830224803804061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12808246453106966405072081 9606184839830224803804061)
  ·
    refine ⟨3602319314936334301426523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9606184839830224803804061 3602319314936334301426523)
    ·
      refine ⟨5403478972404501452139785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3602319314936334301426523 5403478972404501452139785)
      ·
        refine ⟨4052609229303376089104839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5403478972404501452139785 4052609229303376089104839)
        ·
          refine ⟨6078913843955064133657259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4052609229303376089104839 6078913843955064133657259)
          ·
            refine ⟨9118370765932596200485889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6078913843955064133657259 9118370765932596200485889)
            ·
              refine ⟨6838778074449447150364417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9118370765932596200485889 6838778074449447150364417)
              ·
                refine ⟨5129083555837085362773313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6838778074449447150364417 5129083555837085362773313)
                ·
                  refine ⟨3846812666877814022079985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5129083555837085362773313 3846812666877814022079985)
                  ·
                    refine ⟨2885109500158360516559989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3846812666877814022079985 2885109500158360516559989)
                    ·
                      refine ⟨270479015639846298427499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2885109500158360516559989 270479015639846298427499)
                      ·
                        rfl

theorem cell23_526756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 2, 2, 2, 5].length) (baseStart_526756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_526756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_526756 prefixEnd_526756 := by exact prefixLift 526756
  have htrace : WordTrace (prefixWord ++ tailWord_526756) baseStart_526756 baseEnd_526756 := by
    simpa [prefixWord, tailWord_526756, baseEnd_526756] using wordTrace_append hprefix tailTrace_526756
  have hstable : (prefixWord ++ tailWord_526756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_526756).length < 2 ^ (prefixWord ++ tailWord_526756).sum := by decide
  have hdescent : baseEnd_526756 < baseStart_526756 := by decide
  rcases family_descends (prefixWord ++ tailWord_526756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_526804 : List Nat := [2, 4, 1, 2, 2, 1, 4, 1, 1, 3, 2]
def baseStart_526804 : Nat := 118140960795 + 526804 * 2 ^ 59
def prefixEnd_526804 : Nat := 4983230072969 + 3 ^ 40 * 526804 * 2
def baseEnd_526804 : Nat := 270503662711262110627279

theorem tailTrace_526804 : CollatzResearch.WordTrace tailWord_526804 prefixEnd_526804 270503662711262110627279 := by
  unfold tailWord_526804
  simp only [CollatzResearch.WordTrace]
  refine ⟨9607060191743276902677733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12809413588991035870236977 9607060191743276902677733)
  ·
    refine ⟨1801323785951864419252075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9607060191743276902677733 1801323785951864419252075)
    ·
      refine ⟨2701985678927796628878113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1801323785951864419252075 2701985678927796628878113)
      ·
        refine ⟨2026489259195847471658585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2701985678927796628878113 2026489259195847471658585)
        ·
          refine ⟨1519866944396885603743939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2026489259195847471658585 1519866944396885603743939)
          ·
            refine ⟨2279800416595328405615909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1519866944396885603743939 2279800416595328405615909)
            ·
              refine ⟨427462578111624076052983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2279800416595328405615909 427462578111624076052983)
              ·
                refine ⟨641193867167436114079475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 427462578111624076052983 641193867167436114079475)
                ·
                  refine ⟨961790800751154171119213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 641193867167436114079475 961790800751154171119213)
                  ·
                    refine ⟨360671550281682814169705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 961790800751154171119213 360671550281682814169705)
                    ·
                      refine ⟨270503662711262110627279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 360671550281682814169705 270503662711262110627279)
                      ·
                        rfl

theorem cell23_526804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 4, 1, 1, 3, 2].length) (baseStart_526804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_526804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_526804 prefixEnd_526804 := by exact prefixLift 526804
  have htrace : WordTrace (prefixWord ++ tailWord_526804) baseStart_526804 baseEnd_526804 := by
    simpa [prefixWord, tailWord_526804, baseEnd_526804] using wordTrace_append hprefix tailTrace_526804
  have hstable : (prefixWord ++ tailWord_526804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_526804).length < 2 ^ (prefixWord ++ tailWord_526804).sum := by decide
  have hdescent : baseEnd_526804 < baseStart_526804 := by decide
  rcases family_descends (prefixWord ++ tailWord_526804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_526813 : List Nat := [1, 4, 3, 1, 1, 1, 1, 1, 4, 2, 4]
def baseStart_526813 : Nat := 118140960795 + 526813 * 2 ^ 59
def prefixEnd_526813 : Nat := 4983230072969 + 3 ^ 40 * 526813 * 2
def baseEnd_526813 : Nat := 270508284037152575414737

theorem tailTrace_526813 : CollatzResearch.WordTrace tailWord_526813 prefixEnd_526813 270508284037152575414737 := by
  unfold tailWord_526813
  simp only [CollatzResearch.WordTrace]
  refine ⟨19214448640453948342433093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12809632426969298894955395 19214448640453948342433093)
  ·
    refine ⟨3602709120085115314206205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19214448640453948342433093 3602709120085115314206205)
    ·
      refine ⟨1351015920031918242827327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3602709120085115314206205 1351015920031918242827327)
      ·
        refine ⟨2026523880047877364240991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1351015920031918242827327 2026523880047877364240991)
        ·
          refine ⟨3039785820071816046361487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2026523880047877364240991 3039785820071816046361487)
          ·
            refine ⟨4559678730107724069542231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3039785820071816046361487 4559678730107724069542231)
            ·
              refine ⟨6839518095161586104313347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4559678730107724069542231 6839518095161586104313347)
              ·
                refine ⟨10259277142742379156470021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6839518095161586104313347 10259277142742379156470021)
                ·
                  refine ⟨1923614464264196091838129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10259277142742379156470021 1923614464264196091838129)
                  ·
                    refine ⟨1442710848198147068878597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1923614464264196091838129 1442710848198147068878597)
                    ·
                      refine ⟨270508284037152575414737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1442710848198147068878597 270508284037152575414737)
                      ·
                        rfl

theorem cell23_526813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 1, 4, 2, 4].length) (baseStart_526813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_526813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_526813 prefixEnd_526813 := by exact prefixLift 526813
  have htrace : WordTrace (prefixWord ++ tailWord_526813) baseStart_526813 baseEnd_526813 := by
    simpa [prefixWord, tailWord_526813, baseEnd_526813] using wordTrace_append hprefix tailTrace_526813
  have hstable : (prefixWord ++ tailWord_526813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_526813).length < 2 ^ (prefixWord ++ tailWord_526813).sum := by decide
  have hdescent : baseEnd_526813 < baseStart_526813 := by decide
  rcases family_descends (prefixWord ++ tailWord_526813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_526823 : List Nat := [1, 1, 5, 2, 1, 1, 4, 1, 7]
def baseStart_526823 : Nat := 118140960795 + 526823 * 2 ^ 59
def prefixEnd_526823 : Nat := 4983230072969 + 3 ^ 40 * 526823 * 2
def baseEnd_526823 : Nat := 30057046538188615143299

theorem tailTrace_526823 : CollatzResearch.WordTrace tailWord_526823 prefixEnd_526823 30057046538188615143299 := by
  unfold tailWord_526823
  simp only [CollatzResearch.WordTrace]
  refine ⟨19214813370417720050297123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12809875580278480033531415 19214813370417720050297123)
  ·
    refine ⟨28822220055626580075445685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19214813370417720050297123 28822220055626580075445685)
    ·
      refine ⟨2702083130214991882073033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 28822220055626580075445685 2702083130214991882073033)
      ·
        refine ⟨2026562347661243911554775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2702083130214991882073033 2026562347661243911554775)
        ·
          refine ⟨3039843521491865867332163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2026562347661243911554775 3039843521491865867332163)
          ·
            refine ⟨4559765282237798800998245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3039843521491865867332163 4559765282237798800998245)
            ·
              refine ⟨854955990419587275187171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4559765282237798800998245 854955990419587275187171)
              ·
                refine ⟨1282433985629380912780757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 854955990419587275187171 1282433985629380912780757)
                ·
                  refine ⟨30057046538188615143299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1282433985629380912780757 30057046538188615143299)
                  ·
                    rfl

theorem cell23_526823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 4, 1, 7].length) (baseStart_526823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_526823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_526823 prefixEnd_526823 := by exact prefixLift 526823
  have htrace : WordTrace (prefixWord ++ tailWord_526823) baseStart_526823 baseEnd_526823 := by
    simpa [prefixWord, tailWord_526823, baseEnd_526823] using wordTrace_append hprefix tailTrace_526823
  have hstable : (prefixWord ++ tailWord_526823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_526823).length < 2 ^ (prefixWord ++ tailWord_526823).sum := by decide
  have hdescent : baseEnd_526823 < baseStart_526823 := by decide
  rcases family_descends (prefixWord ++ tailWord_526823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_526833 : List Nat := [1, 2, 2, 2, 3, 1, 1, 3, 2, 3, 3]
def baseStart_526833 : Nat := 118140960795 + 526833 * 2 ^ 59
def prefixEnd_526833 : Nat := 4983230072969 + 3 ^ 40 * 526833 * 2
def baseEnd_526833 : Nat := 270518553650242497164645

theorem tailTrace_526833 : CollatzResearch.WordTrace tailWord_526833 prefixEnd_526833 270518553650242497164645 := by
  unfold tailWord_526833
  simp only [CollatzResearch.WordTrace]
  refine ⟨19215178100381491758161153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12810118733587661172107435 19215178100381491758161153)
  ·
    refine ⟨14411383575286118818620865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19215178100381491758161153 14411383575286118818620865)
    ·
      refine ⟨10808537681464589113965649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14411383575286118818620865 10808537681464589113965649)
      ·
        refine ⟨8106403261098441835474237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10808537681464589113965649 8106403261098441835474237)
        ·
          refine ⟨3039901222911915688302839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8106403261098441835474237 3039901222911915688302839)
          ·
            refine ⟨4559851834367873532454259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3039901222911915688302839 4559851834367873532454259)
            ·
              refine ⟨6839777751551810298681389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4559851834367873532454259 6839777751551810298681389)
              ·
                refine ⟨2564916656831928862005521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6839777751551810298681389 2564916656831928862005521)
                ·
                  refine ⟨1923687492623946646504141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2564916656831928862005521 1923687492623946646504141)
                  ·
                    refine ⟨721382809733979992439053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1923687492623946646504141 721382809733979992439053)
                    ·
                      refine ⟨270518553650242497164645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 721382809733979992439053 270518553650242497164645)
                      ·
                        rfl

theorem cell23_526833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 3, 2, 3, 3].length) (baseStart_526833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_526833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_526833 prefixEnd_526833 := by exact prefixLift 526833
  have htrace : WordTrace (prefixWord ++ tailWord_526833) baseStart_526833 baseEnd_526833 := by
    simpa [prefixWord, tailWord_526833, baseEnd_526833] using wordTrace_append hprefix tailTrace_526833
  have hstable : (prefixWord ++ tailWord_526833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_526833).length < 2 ^ (prefixWord ++ tailWord_526833).sum := by decide
  have hdescent : baseEnd_526833 < baseStart_526833 := by decide
  rcases family_descends (prefixWord ++ tailWord_526833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_526834 : List Nat := [3, 2, 1, 4, 2, 2, 1, 1, 1, 4, 2]
def baseStart_526834 : Nat := 118140960795 + 526834 * 2 ^ 59
def prefixEnd_526834 : Nat := 4983230072969 + 3 ^ 40 * 526834 * 2
def baseEnd_526834 : Nat := 270519067130896993252141

theorem tailTrace_526834 : CollatzResearch.WordTrace tailWord_526834 prefixEnd_526834 270519067130896993252141 := by
  unfold tailWord_526834
  simp only [CollatzResearch.WordTrace]
  refine ⟨4803803643344467232236889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12810143048918579285965037 4803803643344467232236889)
  ·
    refine ⟨3602852732508350424177667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4803803643344467232236889 3602852732508350424177667)
    ·
      refine ⟨5404279098762525636266501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3602852732508350424177667 5404279098762525636266501)
      ·
        refine ⟨1013302331017973556799969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5404279098762525636266501 1013302331017973556799969)
        ·
          refine ⟨759976748263480167599977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1013302331017973556799969 759976748263480167599977)
          ·
            refine ⟨569982561197610125699983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 759976748263480167599977 569982561197610125699983)
            ·
              refine ⟨854973841796415188549975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 569982561197610125699983 854973841796415188549975)
              ·
                refine ⟨1282460762694622782824963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 854973841796415188549975 1282460762694622782824963)
                ·
                  refine ⟨1923691144041934174237445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1282460762694622782824963 1923691144041934174237445)
                  ·
                    refine ⟨360692089507862657669521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1923691144041934174237445 360692089507862657669521)
                    ·
                      refine ⟨270519067130896993252141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 360692089507862657669521 270519067130896993252141)
                      ·
                        rfl

theorem cell23_526834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 1, 1, 1, 4, 2].length) (baseStart_526834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_526834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_526834 prefixEnd_526834 := by exact prefixLift 526834
  have htrace : WordTrace (prefixWord ++ tailWord_526834) baseStart_526834 baseEnd_526834 := by
    simpa [prefixWord, tailWord_526834, baseEnd_526834] using wordTrace_append hprefix tailTrace_526834
  have hstable : (prefixWord ++ tailWord_526834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_526834).length < 2 ^ (prefixWord ++ tailWord_526834).sum := by decide
  have hdescent : baseEnd_526834 < baseStart_526834 := by decide
  rcases family_descends (prefixWord ++ tailWord_526834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_526854 : List Nat := [6, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5]
def baseStart_526854 : Nat := 118140960795 + 526854 * 2 ^ 59
def prefixEnd_526854 : Nat := 4983230072969 + 3 ^ 40 * 526854 * 2
def baseEnd_526854 : Nat := 270529336743986915002049

theorem tailTrace_526854 : CollatzResearch.WordTrace tailWord_526854 prefixEnd_526854 270529336743986915002049 := by
  unfold tailWord_526854
  simp only [CollatzResearch.WordTrace]
  refine ⟨600498251040794135771113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 12810629355536941563117077 600498251040794135771113)
  ·
    refine ⟨450373688280595601828335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 600498251040794135771113 450373688280595601828335)
    ·
      refine ⟨675560532420893402742503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 450373688280595601828335 675560532420893402742503)
      ·
        refine ⟨1013340798631340104113755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 675560532420893402742503 1013340798631340104113755)
        ·
          refine ⟨1520011197947010156170633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1013340798631340104113755 1520011197947010156170633)
          ·
            refine ⟨1140008398460257617127975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1520011197947010156170633 1140008398460257617127975)
            ·
              refine ⟨1710012597690386425691963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1140008398460257617127975 1710012597690386425691963)
              ·
                refine ⟨2565018896535579638537945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1710012597690386425691963 2565018896535579638537945)
                ·
                  refine ⟨1923764172401684728903459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2565018896535579638537945 1923764172401684728903459)
                  ·
                    refine ⟨2885646258602527093355189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1923764172401684728903459 2885646258602527093355189)
                    ·
                      refine ⟨270529336743986915002049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2885646258602527093355189 270529336743986915002049)
                      ·
                        rfl

theorem cell23_526854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_526854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_526854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_526854 prefixEnd_526854 := by exact prefixLift 526854
  have htrace : WordTrace (prefixWord ++ tailWord_526854) baseStart_526854 baseEnd_526854 := by
    simpa [prefixWord, tailWord_526854, baseEnd_526854] using wordTrace_append hprefix tailTrace_526854
  have hstable : (prefixWord ++ tailWord_526854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_526854).length < 2 ^ (prefixWord ++ tailWord_526854).sum := by decide
  have hdescent : baseEnd_526854 < baseStart_526854 := by decide
  rcases family_descends (prefixWord ++ tailWord_526854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_526873 : List Nat := [1, 2, 1, 2, 1, 1, 2, 6, 2, 1, 4]
def baseStart_526873 : Nat := 118140960795 + 526873 * 2 ^ 59
def prefixEnd_526873 : Nat := 4983230072969 + 3 ^ 40 * 526873 * 2
def baseEnd_526873 : Nat := 270539092876422340664461

theorem tailTrace_526873 : CollatzResearch.WordTrace tailWord_526873 prefixEnd_526873 270539092876422340664461 := by
  unfold tailWord_526873
  simp only [CollatzResearch.WordTrace]
  refine ⟨19216637020236578589617273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12811091346824385726411515 19216637020236578589617273)
  ·
    refine ⟨14412477765177433942212955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19216637020236578589617273 14412477765177433942212955)
    ·
      refine ⟨21618716647766150913319433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14412477765177433942212955 21618716647766150913319433)
      ·
        refine ⟨16214037485824613184989575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21618716647766150913319433 16214037485824613184989575)
        ·
          refine ⟨24321056228736919777484363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16214037485824613184989575 24321056228736919777484363)
          ·
            refine ⟨36481584343105379666226545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24321056228736919777484363 36481584343105379666226545)
            ·
              refine ⟨27361188257329034749669909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36481584343105379666226545 27361188257329034749669909)
              ·
                refine ⟨1282555699562298503890777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 27361188257329034749669909 1282555699562298503890777)
                ·
                  refine ⟨961916774671723877918083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1282555699562298503890777 961916774671723877918083)
                  ·
                    refine ⟨1442875162007585816877125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 961916774671723877918083 1442875162007585816877125)
                    ·
                      refine ⟨270539092876422340664461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1442875162007585816877125 270539092876422340664461)
                      ·
                        rfl

theorem cell23_526873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 6, 2, 1, 4].length) (baseStart_526873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_526873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_526873 prefixEnd_526873 := by exact prefixLift 526873
  have htrace : WordTrace (prefixWord ++ tailWord_526873) baseStart_526873 baseEnd_526873 := by
    simpa [prefixWord, tailWord_526873, baseEnd_526873] using wordTrace_append hprefix tailTrace_526873
  have hstable : (prefixWord ++ tailWord_526873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_526873).length < 2 ^ (prefixWord ++ tailWord_526873).sum := by decide
  have hdescent : baseEnd_526873 < baseStart_526873 := by decide
  rcases family_descends (prefixWord ++ tailWord_526873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_526880 : List Nat := [2, 1, 1, 6, 2, 1, 1, 1, 1, 2, 5]
def baseStart_526880 : Nat := 118140960795 + 526880 * 2 ^ 59
def prefixEnd_526880 : Nat := 4983230072969 + 3 ^ 40 * 526880 * 2
def baseEnd_526880 : Nat := 270542687241003813276929

theorem tailTrace_526880 : CollatzResearch.WordTrace tailWord_526880 prefixEnd_526880 270542687241003813276929 := by
  unfold tailWord_526880
  simp only [CollatzResearch.WordTrace]
  refine ⟨9608446165605609392561047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12811261554140812523414729 9608446165605609392561047)
  ·
    refine ⟨14412669248408414088841571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9608446165605609392561047 14412669248408414088841571)
    ·
      refine ⟨21619003872612621133262357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14412669248408414088841571 21619003872612621133262357)
      ·
        refine ⟨1013390806528716615621673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 21619003872612621133262357 1013390806528716615621673)
        ·
          refine ⟨760043104896537461716255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1013390806528716615621673 760043104896537461716255)
          ·
            refine ⟨1140064657344806192574383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 760043104896537461716255 1140064657344806192574383)
            ·
              refine ⟨1710096986017209288861575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1140064657344806192574383 1710096986017209288861575)
              ·
                refine ⟨2565145479025813933292363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1710096986017209288861575 2565145479025813933292363)
                ·
                  refine ⟨3847718218538720899938545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2565145479025813933292363 3847718218538720899938545)
                  ·
                    refine ⟨2885788663904040674953909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3847718218538720899938545 2885788663904040674953909)
                    ·
                      refine ⟨270542687241003813276929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2885788663904040674953909 270542687241003813276929)
                      ·
                        rfl

theorem cell23_526880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 1, 1, 1, 2, 5].length) (baseStart_526880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_526880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_526880 prefixEnd_526880 := by exact prefixLift 526880
  have htrace : WordTrace (prefixWord ++ tailWord_526880) baseStart_526880 baseEnd_526880 := by
    simpa [prefixWord, tailWord_526880, baseEnd_526880] using wordTrace_append hprefix tailTrace_526880
  have hstable : (prefixWord ++ tailWord_526880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_526880).length < 2 ^ (prefixWord ++ tailWord_526880).sum := by decide
  have hdescent : baseEnd_526880 < baseStart_526880 := by decide
  rcases family_descends (prefixWord ++ tailWord_526880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_526930 : List Nat := [3, 2, 2, 1, 2, 1, 4, 2, 6]
def baseStart_526930 : Nat := 118140960795 + 526930 * 2 ^ 59
def prefixEnd_526930 : Nat := 4983230072969 + 3 ^ 40 * 526930 * 2
def baseEnd_526930 : Nat := 30063151252636513072411

theorem tailTrace_526930 : CollatzResearch.WordTrace tailWord_526930 prefixEnd_526930 30063151252636513072411 := by
  unfold tailWord_526930
  simp only [CollatzResearch.WordTrace]
  refine ⟨4804678995257519331110561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12812477320686718216294829 4804678995257519331110561)
  ·
    refine ⟨3603509246443139498332921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4804678995257519331110561 3603509246443139498332921)
    ·
      refine ⟨2702631934832354623749691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3603509246443139498332921 2702631934832354623749691)
      ·
        refine ⟨4053947902248531935624537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2702631934832354623749691 4053947902248531935624537)
        ·
          refine ⟨3040460926686398951718403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4053947902248531935624537 3040460926686398951718403)
          ·
            refine ⟨4560691390029598427577605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3040460926686398951718403 4560691390029598427577605)
            ·
              refine ⟨855129635630549705170801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4560691390029598427577605 855129635630549705170801)
              ·
                refine ⟨641347226722912278878101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 855129635630549705170801 641347226722912278878101)
                ·
                  refine ⟨30063151252636513072411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 641347226722912278878101 30063151252636513072411)
                  ·
                    rfl

theorem cell23_526930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 4, 2, 6].length) (baseStart_526930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_526930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_526930 prefixEnd_526930 := by exact prefixLift 526930
  have htrace : WordTrace (prefixWord ++ tailWord_526930) baseStart_526930 baseEnd_526930 := by
    simpa [prefixWord, tailWord_526930, baseEnd_526930] using wordTrace_append hprefix tailTrace_526930
  have hstable : (prefixWord ++ tailWord_526930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_526930).length < 2 ^ (prefixWord ++ tailWord_526930).sum := by decide
  have hdescent : baseEnd_526930 < baseStart_526930 := by decide
  rcases family_descends (prefixWord ++ tailWord_526930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_526957 : List Nat := [1, 5, 1, 1, 3, 1, 1, 1, 5, 1, 3]
def baseStart_526957 : Nat := 118140960795 + 526957 * 2 ^ 59
def prefixEnd_526957 : Nat := 4983230072969 + 3 ^ 40 * 526957 * 2
def baseEnd_526957 : Nat := 270582225251400012014075

theorem tailTrace_526957 : CollatzResearch.WordTrace tailWord_526957 prefixEnd_526957 270582225251400012014075 := by
  unfold tailWord_526957
  simp only [CollatzResearch.WordTrace]
  refine ⟨19219700751932260935675125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12813133834621507290450083 19219700751932260935675125)
  ·
    refine ⟨1801846945493649462719543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 19219700751932260935675125 1801846945493649462719543)
    ·
      refine ⟨2702770418240474194079315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1801846945493649462719543 2702770418240474194079315)
      ·
        refine ⟨4054155627360711291118973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2702770418240474194079315 4054155627360711291118973)
        ·
          refine ⟨1520308360260266734169615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4054155627360711291118973 1520308360260266734169615)
          ·
            refine ⟨2280462540390400101254423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1520308360260266734169615 2280462540390400101254423)
            ·
              refine ⟨3420693810585600151881635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2280462540390400101254423 3420693810585600151881635)
              ·
                refine ⟨5131040715878400227822453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3420693810585600151881635 5131040715878400227822453)
                ·
                  refine ⟨481035067113600021358355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5131040715878400227822453 481035067113600021358355)
                  ·
                    refine ⟨721552600670400032037533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 481035067113600021358355 721552600670400032037533)
                    ·
                      refine ⟨270582225251400012014075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 721552600670400032037533 270582225251400012014075)
                      ·
                        rfl

theorem cell23_526957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 1, 5, 1, 3].length) (baseStart_526957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_526957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_526957 prefixEnd_526957 := by exact prefixLift 526957
  have htrace : WordTrace (prefixWord ++ tailWord_526957) baseStart_526957 baseEnd_526957 := by
    simpa [prefixWord, tailWord_526957, baseEnd_526957] using wordTrace_append hprefix tailTrace_526957
  have hstable : (prefixWord ++ tailWord_526957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_526957).length < 2 ^ (prefixWord ++ tailWord_526957).sum := by decide
  have hdescent : baseEnd_526957 < baseStart_526957 := by decide
  rcases family_descends (prefixWord ++ tailWord_526957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_526967 : List Nat := [1, 1, 3, 1, 1, 3, 5, 1, 2, 3, 2]
def baseStart_526967 : Nat := 118140960795 + 526967 * 2 ^ 59
def prefixEnd_526967 : Nat := 4983230072969 + 3 ^ 40 * 526967 * 2
def baseEnd_526967 : Nat := 270587360057944972889029

theorem tailTrace_526967 : CollatzResearch.WordTrace tailWord_526967 prefixEnd_526967 270587360057944972889029 := by
  unfold tailWord_526967
  simp only [CollatzResearch.WordTrace]
  refine ⟨19220065481896032643539155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12813376987930688429026103 19220065481896032643539155)
  ·
    refine ⟨28830098222844048965308733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19220065481896032643539155 28830098222844048965308733)
    ·
      refine ⟨10811286833566518361990775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28830098222844048965308733 10811286833566518361990775)
      ·
        refine ⟨16216930250349777542986163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10811286833566518361990775 16216930250349777542986163)
        ·
          refine ⟨24325395375524666314479245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16216930250349777542986163 24325395375524666314479245)
          ·
            refine ⟨9122023265821749867929717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24325395375524666314479245 9122023265821749867929717)
            ·
              refine ⟨855189681170789050118411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9122023265821749867929717 855189681170789050118411)
              ·
                refine ⟨1282784521756183575177617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 855189681170789050118411 1282784521756183575177617)
                ·
                  refine ⟨962088391317137681383213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1282784521756183575177617 962088391317137681383213)
                  ·
                    refine ⟨360783146743926630518705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 962088391317137681383213 360783146743926630518705)
                    ·
                      refine ⟨270587360057944972889029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 360783146743926630518705 270587360057944972889029)
                      ·
                        rfl

theorem cell23_526967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 5, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 5, 1, 2, 3, 2].length) (baseStart_526967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_526967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_526967 prefixEnd_526967 := by exact prefixLift 526967
  have htrace : WordTrace (prefixWord ++ tailWord_526967) baseStart_526967 baseEnd_526967 := by
    simpa [prefixWord, tailWord_526967, baseEnd_526967] using wordTrace_append hprefix tailTrace_526967
  have hstable : (prefixWord ++ tailWord_526967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_526967).length < 2 ^ (prefixWord ++ tailWord_526967).sum := by decide
  have hdescent : baseEnd_526967 < baseStart_526967 := by decide
  rcases family_descends (prefixWord ++ tailWord_526967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_527000 : List Nat := [2, 1, 2, 4, 1, 1, 3, 2, 1, 1, 5]
def baseStart_527000 : Nat := 118140960795 + 527000 * 2 ^ 59
def prefixEnd_527000 : Nat := 4983230072969 + 3 ^ 40 * 527000 * 2
def baseEnd_527000 : Nat := 270604304919543343776377

theorem tailTrace_527000 : CollatzResearch.WordTrace tailWord_527000 prefixEnd_527000 270604304919543343776377 := by
  unfold tailWord_527000
  simp only [CollatzResearch.WordTrace]
  refine ⟨9610634545388239639745227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12814179393850986186326969 9610634545388239639745227)
  ·
    refine ⟨14415951818082359459617841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9610634545388239639745227 14415951818082359459617841)
    ·
      refine ⟨10811963863561769594713381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14415951818082359459617841 10811963863561769594713381)
      ·
        refine ⟨2027243224417831799008759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10811963863561769594713381 2027243224417831799008759)
        ·
          refine ⟨3040864836626747698513139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2027243224417831799008759 3040864836626747698513139)
          ·
            refine ⟨4561297254940121547769709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3040864836626747698513139 4561297254940121547769709)
            ·
              refine ⟨1710486470602545580413641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4561297254940121547769709 1710486470602545580413641)
              ·
                refine ⟨1282864852951909185310231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1710486470602545580413641 1282864852951909185310231)
                ·
                  refine ⟨1924297279427863777965347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1282864852951909185310231 1924297279427863777965347)
                  ·
                    refine ⟨2886445919141795666948021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1924297279427863777965347 2886445919141795666948021)
                    ·
                      refine ⟨270604304919543343776377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2886445919141795666948021 270604304919543343776377)
                      ·
                        rfl

theorem cell23_527000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 3, 2, 1, 1, 5].length) (baseStart_527000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_527000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_527000 prefixEnd_527000 := by exact prefixLift 527000
  have htrace : WordTrace (prefixWord ++ tailWord_527000) baseStart_527000 baseEnd_527000 := by
    simpa [prefixWord, tailWord_527000, baseEnd_527000] using wordTrace_append hprefix tailTrace_527000
  have hstable : (prefixWord ++ tailWord_527000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_527000).length < 2 ^ (prefixWord ++ tailWord_527000).sum := by decide
  have hdescent : baseEnd_527000 < baseStart_527000 := by decide
  rcases family_descends (prefixWord ++ tailWord_527000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_527025 : List Nat := [1, 2, 2, 6, 2, 1, 1, 3, 1, 1, 3]
def baseStart_527025 : Nat := 118140960795 + 527025 * 2 ^ 59
def prefixEnd_527025 : Nat := 4983230072969 + 3 ^ 40 * 527025 * 2
def baseEnd_527025 : Nat := 270617141935905745963763

theorem tailTrace_527025 : CollatzResearch.WordTrace tailWord_527025 prefixEnd_527025 270617141935905745963763 := by
  unfold tailWord_527025
  simp only [CollatzResearch.WordTrace]
  refine ⟨19222180915685908549150529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12814787277123939032767019 19222180915685908549150529)
  ·
    refine ⟨14416635686764431411862897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19222180915685908549150529 14416635686764431411862897)
    ·
      refine ⟨10812476765073323558897173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14416635686764431411862897 10812476765073323558897173)
      ·
        refine ⟨506834848362812041823305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 10812476765073323558897173 506834848362812041823305)
        ·
          refine ⟨380126136272109031367479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 506834848362812041823305 380126136272109031367479)
          ·
            refine ⟨570189204408163547051219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 380126136272109031367479 570189204408163547051219)
            ·
              refine ⟨855283806612245320576829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 570189204408163547051219 855283806612245320576829)
              ·
                refine ⟨320731427479591995216311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 855283806612245320576829 320731427479591995216311)
                ·
                  refine ⟨481097141219387992824467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 320731427479591995216311 481097141219387992824467)
                  ·
                    refine ⟨721645711829081989236701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 481097141219387992824467 721645711829081989236701)
                    ·
                      refine ⟨270617141935905745963763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 721645711829081989236701 270617141935905745963763)
                      ·
                        rfl

theorem cell23_527025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 1, 3, 1, 1, 3].length) (baseStart_527025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_527025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_527025 prefixEnd_527025 := by exact prefixLift 527025
  have htrace : WordTrace (prefixWord ++ tailWord_527025) baseStart_527025 baseEnd_527025 := by
    simpa [prefixWord, tailWord_527025, baseEnd_527025] using wordTrace_append hprefix tailTrace_527025
  have hstable : (prefixWord ++ tailWord_527025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_527025).length < 2 ^ (prefixWord ++ tailWord_527025).sum := by decide
  have hdescent : baseEnd_527025 < baseStart_527025 := by decide
  rcases family_descends (prefixWord ++ tailWord_527025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_527033 : List Nat := [1, 2, 1, 4, 1, 1, 1, 2, 1, 9]
def baseStart_527033 : Nat := 118140960795 + 527033 * 2 ^ 59
def prefixEnd_527033 : Nat := 4983230072969 + 3 ^ 40 * 527033 * 2
def baseEnd_527033 : Nat := 90207083260380571554575

theorem tailTrace_527033 : CollatzResearch.WordTrace tailWord_527033 prefixEnd_527033 90207083260380571554575 := by
  unfold tailWord_527033
  simp only [CollatzResearch.WordTrace]
  refine ⟨19222472699656925915441753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12814981799771283943627835 19222472699656925915441753)
  ·
    refine ⟨14416854524742694436581315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19222472699656925915441753 14416854524742694436581315)
    ·
      refine ⟨21625281787114041654871973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14416854524742694436581315 21625281787114041654871973)
      ·
        refine ⟨4054740335083882810288495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21625281787114041654871973 4054740335083882810288495)
        ·
          refine ⟨6082110502625824215432743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4054740335083882810288495 6082110502625824215432743)
          ·
            refine ⟨9123165753938736323149115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6082110502625824215432743 9123165753938736323149115)
            ·
              refine ⟨13684748630908104484723673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9123165753938736323149115 13684748630908104484723673)
              ·
                refine ⟨10263561473181078363542755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13684748630908104484723673 10263561473181078363542755)
                ·
                  refine ⟨15395342209771617545314133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10263561473181078363542755 15395342209771617545314133)
                  ·
                    refine ⟨90207083260380571554575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 15395342209771617545314133 90207083260380571554575)
                    ·
                      rfl

theorem cell23_527033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 2, 1, 9].length) (baseStart_527033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_527033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_527033 prefixEnd_527033 := by exact prefixLift 527033
  have htrace : WordTrace (prefixWord ++ tailWord_527033) baseStart_527033 baseEnd_527033 := by
    simpa [prefixWord, tailWord_527033, baseEnd_527033] using wordTrace_append hprefix tailTrace_527033
  have hstable : (prefixWord ++ tailWord_527033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_527033).length < 2 ^ (prefixWord ++ tailWord_527033).sum := by decide
  have hdescent : baseEnd_527033 < baseStart_527033 := by decide
  rcases family_descends (prefixWord ++ tailWord_527033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_527048 : List Nat := [2, 1, 3, 1, 2, 4, 3, 2, 1, 2, 2]
def baseStart_527048 : Nat := 118140960795 + 527048 * 2 ^ 59
def prefixEnd_527048 : Nat := 4983230072969 + 3 ^ 40 * 527048 * 2
def baseEnd_527048 : Nat := 270628951990959155976157

theorem tailTrace_527048 : CollatzResearch.WordTrace tailWord_527048 prefixEnd_527048 270628951990959155976157 := by
  unfold tailWord_527048
  simp only [CollatzResearch.WordTrace]
  refine ⟨9611509897301291738618899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12815346529735055651491865 9611509897301291738618899)
  ·
    refine ⟨14417264845951937607928349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9611509897301291738618899 14417264845951937607928349)
    ·
      refine ⟨5406474317231976602973131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14417264845951937607928349 5406474317231976602973131)
      ·
        refine ⟨8109711475847964904459697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5406474317231976602973131 8109711475847964904459697)
        ·
          refine ⟨6082283606885973678344773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8109711475847964904459697 6082283606885973678344773)
          ·
            refine ⟨1140428176291120064689645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6082283606885973678344773 1140428176291120064689645)
            ·
              refine ⟨427660566109170024258617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1140428176291120064689645 427660566109170024258617)
              ·
                refine ⟨320745424581877518193963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 427660566109170024258617 320745424581877518193963)
                ·
                  refine ⟨481118136872816277290945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 320745424581877518193963 481118136872816277290945)
                  ·
                    refine ⟨360838602654612207968209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 481118136872816277290945 360838602654612207968209)
                    ·
                      refine ⟨270628951990959155976157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 360838602654612207968209 270628951990959155976157)
                      ·
                        rfl

theorem cell23_527048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 3, 2, 1, 2, 2].length) (baseStart_527048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_527048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_527048 prefixEnd_527048 := by exact prefixLift 527048
  have htrace : WordTrace (prefixWord ++ tailWord_527048) baseStart_527048 baseEnd_527048 := by
    simpa [prefixWord, tailWord_527048, baseEnd_527048] using wordTrace_append hprefix tailTrace_527048
  have hstable : (prefixWord ++ tailWord_527048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_527048).length < 2 ^ (prefixWord ++ tailWord_527048).sum := by decide
  have hdescent : baseEnd_527048 < baseStart_527048 := by decide
  rcases family_descends (prefixWord ++ tailWord_527048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_527057 : List Nat := [1, 2, 2, 1, 2, 3, 2, 2, 3, 3, 2]
def baseStart_527057 : Nat := 118140960795 + 527057 * 2 ^ 59
def prefixEnd_527057 : Nat := 4983230072969 + 3 ^ 40 * 527057 * 2
def baseEnd_527057 : Nat := 270633573316849620763615

theorem tailTrace_527057 : CollatzResearch.WordTrace tailWord_527057 prefixEnd_527057 270633573316849620763615 := by
  unfold tailWord_527057
  simp only [CollatzResearch.WordTrace]
  refine ⟨19223348051569978014315425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12815565367713318676210283 19223348051569978014315425)
  ·
    refine ⟨14417511038677483510736569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19223348051569978014315425 14417511038677483510736569)
    ·
      refine ⟨10813133279008112633052427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14417511038677483510736569 10813133279008112633052427)
      ·
        refine ⟨16219699918512168949578641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10813133279008112633052427 16219699918512168949578641)
        ·
          refine ⟨12164774938884126712183981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16219699918512168949578641 12164774938884126712183981)
          ·
            refine ⟨4561790602081547517068993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12164774938884126712183981 4561790602081547517068993)
            ·
              refine ⟨3421342951561160637801745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4561790602081547517068993 3421342951561160637801745)
              ·
                refine ⟨2566007213670870478351309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3421342951561160637801745 2566007213670870478351309)
                ·
                  refine ⟨962252705126576429381741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2566007213670870478351309 962252705126576429381741)
                  ·
                    refine ⟨360844764422466161018153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 962252705126576429381741 360844764422466161018153)
                    ·
                      refine ⟨270633573316849620763615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 360844764422466161018153 270633573316849620763615)
                      ·
                        rfl

theorem cell23_527057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 2, 3, 3, 2].length) (baseStart_527057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_527057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_527057 prefixEnd_527057 := by exact prefixLift 527057
  have htrace : WordTrace (prefixWord ++ tailWord_527057) baseStart_527057 baseEnd_527057 := by
    simpa [prefixWord, tailWord_527057, baseEnd_527057] using wordTrace_append hprefix tailTrace_527057
  have hstable : (prefixWord ++ tailWord_527057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_527057).length < 2 ^ (prefixWord ++ tailWord_527057).sum := by decide
  have hdescent : baseEnd_527057 < baseStart_527057 := by decide
  rcases family_descends (prefixWord ++ tailWord_527057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_527058 : List Nat := [3, 2, 2, 2, 4, 1, 2, 1, 2, 4]
def baseStart_527058 : Nat := 118140960795 + 527058 * 2 ^ 59
def prefixEnd_527058 : Nat := 4983230072969 + 3 ^ 40 * 527058 * 2
def baseEnd_527058 : Nat := 90211362265834705617037

theorem tailTrace_527058 : CollatzResearch.WordTrace tailWord_527058 prefixEnd_527058 90211362265834705617037 := by
  unfold tailWord_527058
  simp only [CollatzResearch.WordTrace]
  refine ⟨4805846131141588796275457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12815589683044236790067885 4805846131141588796275457)
  ·
    refine ⟨3604384598356191597206593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4805846131141588796275457 3604384598356191597206593)
    ·
      refine ⟨2703288448767143697904945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3604384598356191597206593 2703288448767143697904945)
      ·
        refine ⟨2027466336575357773428709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2703288448767143697904945 2027466336575357773428709)
        ·
          refine ⟨380149938107879582517883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2027466336575357773428709 380149938107879582517883)
          ·
            refine ⟨570224907161819373776825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 380149938107879582517883 570224907161819373776825)
            ·
              refine ⟨427668680371364530332619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 570224907161819373776825 427668680371364530332619)
              ·
                refine ⟨641503020557046795498929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 427668680371364530332619 641503020557046795498929)
                ·
                  refine ⟨481127265417785096624197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 641503020557046795498929 481127265417785096624197)
                  ·
                    refine ⟨90211362265834705617037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 481127265417785096624197 90211362265834705617037)
                    ·
                      rfl

theorem cell23_527058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 2, 1, 2, 4].length) (baseStart_527058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_527058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_527058 prefixEnd_527058 := by exact prefixLift 527058
  have htrace : WordTrace (prefixWord ++ tailWord_527058) baseStart_527058 baseEnd_527058 := by
    simpa [prefixWord, tailWord_527058, baseEnd_527058] using wordTrace_append hprefix tailTrace_527058
  have hstable : (prefixWord ++ tailWord_527058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_527058).length < 2 ^ (prefixWord ++ tailWord_527058).sum := by decide
  have hdescent : baseEnd_527058 < baseStart_527058 := by decide
  rcases family_descends (prefixWord ++ tailWord_527058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_527064 : List Nat := [2, 1, 2, 2, 3, 3, 1, 3, 2, 1, 3]
def baseStart_527064 : Nat := 118140960795 + 527064 * 2 ^ 59
def prefixEnd_527064 : Nat := 4983230072969 + 3 ^ 40 * 527064 * 2
def baseEnd_527064 : Nat := 270637167681431093376083

theorem tailTrace_527064 : CollatzResearch.WordTrace tailWord_527064 prefixEnd_527064 270637167681431093376083 := by
  unfold tailWord_527064
  simp only [CollatzResearch.WordTrace]
  refine ⟨9611801681272309104910123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12815735575029745473213497 9611801681272309104910123)
  ·
    refine ⟨14417702521908463657365185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9611801681272309104910123 14417702521908463657365185)
    ·
      refine ⟨10813276891431347743023889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14417702521908463657365185 10813276891431347743023889)
      ·
        refine ⟨8109957668573510807267917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10813276891431347743023889 8109957668573510807267917)
        ·
          refine ⟨3041234125715066552725469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8109957668573510807267917 3041234125715066552725469)
          ·
            refine ⟨1140462797143149957272051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3041234125715066552725469 1140462797143149957272051)
            ·
              refine ⟨1710694195714724935908077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1140462797143149957272051 1710694195714724935908077)
              ·
                refine ⟨641510323393021850965529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1710694195714724935908077 641510323393021850965529)
                ·
                  refine ⟨481132742544766388224147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 641510323393021850965529 481132742544766388224147)
                  ·
                    refine ⟨721699113817149582336221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 481132742544766388224147 721699113817149582336221)
                    ·
                      refine ⟨270637167681431093376083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 721699113817149582336221 270637167681431093376083)
                      ·
                        rfl

theorem cell23_527064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 1, 3, 2, 1, 3].length) (baseStart_527064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_527064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_527064 prefixEnd_527064 := by exact prefixLift 527064
  have htrace : WordTrace (prefixWord ++ tailWord_527064) baseStart_527064 baseEnd_527064 := by
    simpa [prefixWord, tailWord_527064, baseEnd_527064] using wordTrace_append hprefix tailTrace_527064
  have hstable : (prefixWord ++ tailWord_527064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_527064).length < 2 ^ (prefixWord ++ tailWord_527064).sum := by decide
  have hdescent : baseEnd_527064 < baseStart_527064 := by decide
  rcases family_descends (prefixWord ++ tailWord_527064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_527087 : List Nat := [1, 1, 2, 1, 5, 2, 1, 1, 3, 4, 2]
def baseStart_527087 : Nat := 118140960795 + 527087 * 2 ^ 59
def prefixEnd_527087 : Nat := 4983230072969 + 3 ^ 40 * 527087 * 2
def baseEnd_527087 : Nat := 270648977736484503388477

theorem tailTrace_527087 : CollatzResearch.WordTrace tailWord_527087 prefixEnd_527087 270648977736484503388477 := by
  unfold tailWord_527087
  simp only [CollatzResearch.WordTrace]
  refine ⟨19224442241461293137907515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12816294827640862091938343 19224442241461293137907515)
  ·
    refine ⟨28836663362191939706861273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19224442241461293137907515 28836663362191939706861273)
    ·
      refine ⟨21627497521643954780145955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28836663362191939706861273 21627497521643954780145955)
      ·
        refine ⟨32441246282465932170218933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21627497521643954780145955 32441246282465932170218933)
        ·
          refine ⟨3041366838981181140958025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 32441246282465932170218933 3041366838981181140958025)
          ·
            refine ⟨2281025129235885855718519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3041366838981181140958025 2281025129235885855718519)
            ·
              refine ⟨3421537693853828783577779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2281025129235885855718519 3421537693853828783577779)
              ·
                refine ⟨5132306540780743175366669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3421537693853828783577779 5132306540780743175366669)
                ·
                  refine ⟨1924614952792778690762501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5132306540780743175366669 1924614952792778690762501)
                  ·
                    refine ⟨360865303648646004517969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1924614952792778690762501 360865303648646004517969)
                    ·
                      refine ⟨270648977736484503388477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 360865303648646004517969 270648977736484503388477)
                      ·
                        rfl

theorem cell23_527087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 1, 3, 4, 2].length) (baseStart_527087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_527087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_527087 prefixEnd_527087 := by exact prefixLift 527087
  have htrace : WordTrace (prefixWord ++ tailWord_527087) baseStart_527087 baseEnd_527087 := by
    simpa [prefixWord, tailWord_527087, baseEnd_527087] using wordTrace_append hprefix tailTrace_527087
  have hstable : (prefixWord ++ tailWord_527087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_527087).length < 2 ^ (prefixWord ++ tailWord_527087).sum := by decide
  have hdescent : baseEnd_527087 < baseStart_527087 := by decide
  rcases family_descends (prefixWord ++ tailWord_527087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_527127 : List Nat := [1, 1, 3, 4, 3, 1, 1, 2, 7]
def baseStart_527127 : Nat := 118140960795 + 527127 * 2 ^ 59
def prefixEnd_527127 : Nat := 4983230072969 + 3 ^ 40 * 527127 * 2
def baseEnd_527127 : Nat := 30074390773629371876477

theorem tailTrace_527127 : CollatzResearch.WordTrace tailWord_527127 prefixEnd_527127 30074390773629371876477 := by
  unfold tailWord_527127
  simp only [CollatzResearch.WordTrace]
  refine ⟨19225901161316379969363635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12817267440877586646242423 19225901161316379969363635)
  ·
    refine ⟨28838851741974569954045453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19225901161316379969363635 28838851741974569954045453)
    ·
      refine ⟨10814569403240463732767045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28838851741974569954045453 10814569403240463732767045)
      ·
        refine ⟨2027731763107586949893821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10814569403240463732767045 2027731763107586949893821)
        ·
          refine ⟨760399411165345106210183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2027731763107586949893821 760399411165345106210183)
          ·
            refine ⟨1140599116748017659315275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 760399411165345106210183 1140599116748017659315275)
            ·
              refine ⟨1710898675122026488972913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1140599116748017659315275 1710898675122026488972913)
              ·
                refine ⟨1283174006341519866729685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1710898675122026488972913 1283174006341519866729685)
                ·
                  refine ⟨30074390773629371876477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1283174006341519866729685 30074390773629371876477)
                  ·
                    rfl

theorem cell23_527127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 1, 2, 7].length) (baseStart_527127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_527127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_527127 prefixEnd_527127 := by exact prefixLift 527127
  have htrace : WordTrace (prefixWord ++ tailWord_527127) baseStart_527127 baseEnd_527127 := by
    simpa [prefixWord, tailWord_527127, baseEnd_527127] using wordTrace_append hprefix tailTrace_527127
  have hstable : (prefixWord ++ tailWord_527127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_527127).length < 2 ^ (prefixWord ++ tailWord_527127).sum := by decide
  have hdescent : baseEnd_527127 < baseStart_527127 := by decide
  rcases family_descends (prefixWord ++ tailWord_527127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_527144 : List Nat := [2, 1, 5, 1, 1, 1, 4, 3, 5]
def baseStart_527144 : Nat := 118140960795 + 527144 * 2 ^ 59
def prefixEnd_527144 : Nat := 4983230072969 + 3 ^ 40 * 527144 * 2
def baseEnd_527144 : Nat := 30075360681532308930635

theorem tailTrace_527144 : CollatzResearch.WordTrace tailWord_527144 prefixEnd_527144 30075360681532308930635 := by
  unfold tailWord_527144
  simp only [CollatzResearch.WordTrace]
  refine ⟨9613260601127395936366243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12817680801503194581821657 9613260601127395936366243)
  ·
    refine ⟨14419890901691093904549365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9613260601127395936366243 14419890901691093904549365)
    ·
      refine ⟨1351864772033540053551503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14419890901691093904549365 1351864772033540053551503)
      ·
        refine ⟨2027797158050310080327255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1351864772033540053551503 2027797158050310080327255)
        ·
          refine ⟨3041695737075465120490883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2027797158050310080327255 3041695737075465120490883)
          ·
            refine ⟨4562543605613197680736325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3041695737075465120490883 4562543605613197680736325)
            ·
              refine ⟨855476926052474565138061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4562543605613197680736325 855476926052474565138061)
              ·
                refine ⟨320803847269677961926773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 855476926052474565138061 320803847269677961926773)
                ·
                  refine ⟨30075360681532308930635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 320803847269677961926773 30075360681532308930635)
                  ·
                    rfl

theorem cell23_527144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 4, 3, 5].length) (baseStart_527144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_527144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_527144 prefixEnd_527144 := by exact prefixLift 527144
  have htrace : WordTrace (prefixWord ++ tailWord_527144) baseStart_527144 baseEnd_527144 := by
    simpa [prefixWord, tailWord_527144, baseEnd_527144] using wordTrace_append hprefix tailTrace_527144
  have hstable : (prefixWord ++ tailWord_527144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_527144).length < 2 ^ (prefixWord ++ tailWord_527144).sum := by decide
  have hdescent : baseEnd_527144 < baseStart_527144 := by decide
  rcases family_descends (prefixWord ++ tailWord_527144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_527172 : List Nat := [2, 3, 4, 2, 1, 1, 3, 1, 2, 2, 2]
def baseStart_527172 : Nat := 118140960795 + 527172 * 2 ^ 59
def prefixEnd_527172 : Nat := 4983230072969 + 3 ^ 40 * 527172 * 2
def baseEnd_527172 : Nat := 270692623592116670825587

theorem tailTrace_527172 : CollatzResearch.WordTrace tailWord_527172 prefixEnd_527172 270692623592116670825587 := by
  unfold tailWord_527172
  simp only [CollatzResearch.WordTrace]
  refine ⟨9613771223076676327375885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12818361630768901769834513 9613771223076676327375885)
  ·
    refine ⟨3605164208653753622765957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9613771223076676327375885 3605164208653753622765957)
    ·
      refine ⟨675968289122578804268617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3605164208653753622765957 675968289122578804268617)
      ·
        refine ⟨506976216841934103201463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 675968289122578804268617 506976216841934103201463)
        ·
          refine ⟨760464325262901154802195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 506976216841934103201463 760464325262901154802195)
          ·
            refine ⟨1140696487894351732203293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 760464325262901154802195 1140696487894351732203293)
            ·
              refine ⟨427761182960381899576235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1140696487894351732203293 427761182960381899576235)
              ·
                refine ⟨641641774440572849364353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 427761182960381899576235 641641774440572849364353)
                ·
                  refine ⟨481231330830429637023265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 641641774440572849364353 481231330830429637023265)
                  ·
                    refine ⟨360923498122822227767449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 481231330830429637023265 360923498122822227767449)
                    ·
                      refine ⟨270692623592116670825587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 360923498122822227767449 270692623592116670825587)
                      ·
                        rfl

theorem cell23_527172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 3, 1, 2, 2, 2].length) (baseStart_527172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_527172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_527172 prefixEnd_527172 := by exact prefixLift 527172
  have htrace : WordTrace (prefixWord ++ tailWord_527172) baseStart_527172 baseEnd_527172 := by
    simpa [prefixWord, tailWord_527172, baseEnd_527172] using wordTrace_append hprefix tailTrace_527172
  have hstable : (prefixWord ++ tailWord_527172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_527172).length < 2 ^ (prefixWord ++ tailWord_527172).sum := by decide
  have hdescent : baseEnd_527172 < baseStart_527172 := by decide
  rcases family_descends (prefixWord ++ tailWord_527172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_527200 : List Nat := [2, 1, 1, 3, 3, 1, 1, 1, 10]
def baseStart_527200 : Nat := 118140960795 + 527200 * 2 ^ 59
def prefixEnd_527200 : Nat := 4983230072969 + 3 ^ 40 * 527200 * 2
def baseEnd_527200 : Nat := 30078555672271395697273

theorem tailTrace_527200 : CollatzResearch.WordTrace tailWord_527200 prefixEnd_527200 30078555672271395697273 := by
  unfold tailWord_527200
  simp only [CollatzResearch.WordTrace]
  refine ⟨9614281845025956718385527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12819042460034608957847369 9614281845025956718385527)
  ·
    refine ⟨14421422767538935077578291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9614281845025956718385527 14421422767538935077578291)
    ·
      refine ⟨21632134151308402616367437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14421422767538935077578291 21632134151308402616367437)
      ·
        refine ⟨8112050306740650981137789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21632134151308402616367437 8112050306740650981137789)
        ·
          refine ⟨3042018865027744117926671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8112050306740650981137789 3042018865027744117926671)
          ·
            refine ⟨4563028297541616176890007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3042018865027744117926671 4563028297541616176890007)
            ·
              refine ⟨6844542446312424265335011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4563028297541616176890007 6844542446312424265335011)
              ·
                refine ⟨10266813669468636398002517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6844542446312424265335011 10266813669468636398002517)
                ·
                  refine ⟨30078555672271395697273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 10266813669468636398002517 30078555672271395697273)
                  ·
                    rfl

theorem cell23_527200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 1, 10].length) (baseStart_527200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_527200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_527200 prefixEnd_527200 := by exact prefixLift 527200
  have htrace : WordTrace (prefixWord ++ tailWord_527200) baseStart_527200 baseEnd_527200 := by
    simpa [prefixWord, tailWord_527200, baseEnd_527200] using wordTrace_append hprefix tailTrace_527200
  have hstable : (prefixWord ++ tailWord_527200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_527200).length < 2 ^ (prefixWord ++ tailWord_527200).sum := by decide
  have hdescent : baseEnd_527200 < baseStart_527200 := by decide
  rcases family_descends (prefixWord ++ tailWord_527200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_527221 : List Nat := [1, 3, 4, 1, 1, 4, 1, 1, 3, 4]
def baseStart_527221 : Nat := 118140960795 + 527221 * 2 ^ 59
def prefixEnd_527221 : Nat := 4983230072969 + 3 ^ 40 * 527221 * 2
def baseEnd_527221 : Nat := 90239261381395659704287

theorem tailTrace_527221 : CollatzResearch.WordTrace tailWord_527221 prefixEnd_527221 90239261381395659704287 := by
  unfold tailWord_527221
  simp only [CollatzResearch.WordTrace]
  refine ⟨19229329622975834023285517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12819553081983889348857011 19229329622975834023285517)
  ·
    refine ⟨7210998608615937758732069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19229329622975834023285517 7210998608615937758732069)
    ·
      refine ⟨1352062239115488329762263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7210998608615937758732069 1352062239115488329762263)
      ·
        refine ⟨2028093358673232494643395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1352062239115488329762263 2028093358673232494643395)
        ·
          refine ⟨3042140038009848741965093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2028093358673232494643395 3042140038009848741965093)
          ·
            refine ⟨570401257126846639118455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3042140038009848741965093 570401257126846639118455)
            ·
              refine ⟨855601885690269958677683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 570401257126846639118455 855601885690269958677683)
              ·
                refine ⟨1283402828535404938016525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 855601885690269958677683 1283402828535404938016525)
                ·
                  refine ⟨481276060700776851756197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1283402828535404938016525 481276060700776851756197)
                  ·
                    refine ⟨90239261381395659704287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 481276060700776851756197 90239261381395659704287)
                    ·
                      rfl

theorem cell23_527221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 1, 1, 3, 4].length) (baseStart_527221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_527221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_527221 prefixEnd_527221 := by exact prefixLift 527221
  have htrace : WordTrace (prefixWord ++ tailWord_527221) baseStart_527221 baseEnd_527221 := by
    simpa [prefixWord, tailWord_527221, baseEnd_527221] using wordTrace_append hprefix tailTrace_527221
  have hstable : (prefixWord ++ tailWord_527221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_527221).length < 2 ^ (prefixWord ++ tailWord_527221).sum := by decide
  have hdescent : baseEnd_527221 < baseStart_527221 := by decide
  rcases family_descends (prefixWord ++ tailWord_527221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_527244 : List Nat := [2, 2, 1, 2, 1, 2, 2, 4, 3, 1, 3]
def baseStart_527244 : Nat := 118140960795 + 527244 * 2 ^ 59
def prefixEnd_527244 : Nat := 4983230072969 + 3 ^ 40 * 527244 * 2
def baseEnd_527244 : Nat := 270729594199240389125255

theorem tailTrace_527244 : CollatzResearch.WordTrace tailWord_527244 prefixEnd_527244 270729594199240389125255 := by
  unfold tailWord_527244
  simp only [CollatzResearch.WordTrace]
  refine ⟨9615084250946254475686393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12820112334595005967581857 9615084250946254475686393)
  ·
    refine ⟨7211313188209690856764795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9615084250946254475686393 7211313188209690856764795)
    ·
      refine ⟨10816969782314536285147193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7211313188209690856764795 10816969782314536285147193)
      ·
        refine ⟨8112727336735902213860395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10816969782314536285147193 8112727336735902213860395)
        ·
          refine ⟨12169091005103853320790593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8112727336735902213860395 12169091005103853320790593)
          ·
            refine ⟨9126818253827889990592945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12169091005103853320790593 9126818253827889990592945)
            ·
              refine ⟨6845113690370917492944709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9126818253827889990592945 6845113690370917492944709)
              ·
                refine ⟨1283458816944547029927133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6845113690370917492944709 1283458816944547029927133)
                ·
                  refine ⟨481297056354205136222675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1283458816944547029927133 481297056354205136222675)
                  ·
                    refine ⟨721945584531307704334013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 481297056354205136222675 721945584531307704334013)
                    ·
                      refine ⟨270729594199240389125255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 721945584531307704334013 270729594199240389125255)
                      ·
                        rfl

theorem cell23_527244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 4, 3, 1, 3].length) (baseStart_527244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_527244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_527244 prefixEnd_527244 := by exact prefixLift 527244
  have htrace : WordTrace (prefixWord ++ tailWord_527244) baseStart_527244 baseEnd_527244 := by
    simpa [prefixWord, tailWord_527244, baseEnd_527244] using wordTrace_append hprefix tailTrace_527244
  have hstable : (prefixWord ++ tailWord_527244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_527244).length < 2 ^ (prefixWord ++ tailWord_527244).sum := by decide
  have hdescent : baseEnd_527244 < baseStart_527244 := by decide
  rcases family_descends (prefixWord ++ tailWord_527244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_527287 : List Nat := [1, 1, 3, 1, 3, 1, 2, 4, 1, 1, 5]
def baseStart_527287 : Nat := 118140960795 + 527287 * 2 ^ 59
def prefixEnd_527287 : Nat := 4983230072969 + 3 ^ 40 * 527287 * 2
def baseEnd_527287 : Nat := 270751673867383720887557

theorem tailTrace_527287 : CollatzResearch.WordTrace tailWord_527287 prefixEnd_527287 270751673867383720887557 := by
  unfold tailWord_527287
  simp only [CollatzResearch.WordTrace]
  refine ⟨19231736840736727295188115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12821157893824484863458743 19231736840736727295188115)
  ·
    refine ⟨28847605261105090942782173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19231736840736727295188115 28847605261105090942782173)
    ·
      refine ⟨10817851972914409103543315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28847605261105090942782173 10817851972914409103543315)
      ·
        refine ⟨16226777959371613655314973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10817851972914409103543315 16226777959371613655314973)
        ·
          refine ⟨6085041734764355120743115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16226777959371613655314973 6085041734764355120743115)
          ·
            refine ⟨9127562602146532681114673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6085041734764355120743115 9127562602146532681114673)
            ·
              refine ⟨6845671951609899510836005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9127562602146532681114673 6845671951609899510836005)
              ·
                refine ⟨1283563490926856158281751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6845671951609899510836005 1283563490926856158281751)
                ·
                  refine ⟨1925345236390284237422627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1283563490926856158281751 1925345236390284237422627)
                  ·
                    refine ⟨2888017854585426356133941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1925345236390284237422627 2888017854585426356133941)
                    ·
                      refine ⟨270751673867383720887557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2888017854585426356133941 270751673867383720887557)
                      ·
                        rfl

theorem cell23_527287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 4, 1, 1, 5].length) (baseStart_527287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_527287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_527287 prefixEnd_527287 := by exact prefixLift 527287
  have htrace : WordTrace (prefixWord ++ tailWord_527287) baseStart_527287 baseEnd_527287 := by
    simpa [prefixWord, tailWord_527287, baseEnd_527287] using wordTrace_append hprefix tailTrace_527287
  have hstable : (prefixWord ++ tailWord_527287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_527287).length < 2 ^ (prefixWord ++ tailWord_527287).sum := by decide
  have hdescent : baseEnd_527287 < baseStart_527287 := by decide
  rcases family_descends (prefixWord ++ tailWord_527287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_527294 : List Nat := [4, 2, 1, 1, 1, 2, 4, 1, 1, 6]
def baseStart_527294 : Nat := 118140960795 + 527294 * 2 ^ 59
def prefixEnd_527294 : Nat := 4983230072969 + 3 ^ 40 * 527294 * 2
def baseEnd_527294 : Nat := 90251756077321731166675

theorem tailTrace_527294 : CollatzResearch.WordTrace tailWord_527294 prefixEnd_527294 90251756077321731166675 := by
  unfold tailWord_527294
  simp only [CollatzResearch.WordTrace]
  refine ⟨2403999018963920936336617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12821328101140911660461957 2403999018963920936336617)
  ·
    refine ⟨1802999264222940702252463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2403999018963920936336617 1802999264222940702252463)
    ·
      refine ⟨2704498896334411053378695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1802999264222940702252463 2704498896334411053378695)
      ·
        refine ⟨4056748344501616580068043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2704498896334411053378695 4056748344501616580068043)
        ·
          refine ⟨6085122516752424870102065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4056748344501616580068043 6085122516752424870102065)
          ·
            refine ⟨4563841887564318652576549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6085122516752424870102065 4563841887564318652576549)
            ·
              refine ⟨855720353918309747358103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4563841887564318652576549 855720353918309747358103)
              ·
                refine ⟨1283580530877464621037155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 855720353918309747358103 1283580530877464621037155)
                ·
                  refine ⟨1925370796316196931555733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1283580530877464621037155 1925370796316196931555733)
                  ·
                    refine ⟨90251756077321731166675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1925370796316196931555733 90251756077321731166675)
                    ·
                      rfl

theorem cell23_527294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 4, 1, 1, 6].length) (baseStart_527294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_527294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_527294 prefixEnd_527294 := by exact prefixLift 527294
  have htrace : WordTrace (prefixWord ++ tailWord_527294) baseStart_527294 baseEnd_527294 := by
    simpa [prefixWord, tailWord_527294, baseEnd_527294] using wordTrace_append hprefix tailTrace_527294
  have hstable : (prefixWord ++ tailWord_527294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_527294).length < 2 ^ (prefixWord ++ tailWord_527294).sum := by decide
  have hdescent : baseEnd_527294 < baseStart_527294 := by decide
  rcases family_descends (prefixWord ++ tailWord_527294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_527318 : List Nat := [5, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4]
def baseStart_527318 : Nat := 118140960795 + 527318 * 2 ^ 59
def prefixEnd_527318 : Nat := 4983230072969 + 3 ^ 40 * 527318 * 2
def baseEnd_527318 : Nat := 270767591767673099599915

theorem tailTrace_527318 : CollatzResearch.WordTrace tailWord_527318 prefixEnd_527318 270767591767673099599915 := by
  unfold tailWord_527318
  simp only [CollatzResearch.WordTrace]
  refine ⟨1202054218976526224347913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12821911669082946393044405 1202054218976526224347913)
  ·
    refine ⟨901540664232394668260935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1202054218976526224347913 901540664232394668260935)
    ·
      refine ⟨1352310996348592002391403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 901540664232394668260935 1352310996348592002391403)
      ·
        refine ⟨2028466494522888003587105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1352310996348592002391403 2028466494522888003587105)
        ·
          refine ⟨1521349870892166002690329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2028466494522888003587105 1521349870892166002690329)
          ·
            refine ⟨1141012403169124502017747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1521349870892166002690329 1141012403169124502017747)
            ·
              refine ⟨1711518604753686753026621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1141012403169124502017747 1711518604753686753026621)
              ·
                refine ⟨641819476782632532384983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1711518604753686753026621 641819476782632532384983)
                ·
                  refine ⟨962729215173948798577475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 641819476782632532384983 962729215173948798577475)
                  ·
                    refine ⟨1444093822760923197866213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 962729215173948798577475 1444093822760923197866213)
                    ·
                      refine ⟨270767591767673099599915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1444093822760923197866213 270767591767673099599915)
                      ·
                        rfl

theorem cell23_527318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4].length) (baseStart_527318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_527318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_527318 prefixEnd_527318 := by exact prefixLift 527318
  have htrace : WordTrace (prefixWord ++ tailWord_527318) baseStart_527318 baseEnd_527318 := by
    simpa [prefixWord, tailWord_527318, baseEnd_527318] using wordTrace_append hprefix tailTrace_527318
  have hstable : (prefixWord ++ tailWord_527318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_527318).length < 2 ^ (prefixWord ++ tailWord_527318).sum := by decide
  have hdescent : baseEnd_527318 < baseStart_527318 := by decide
  rcases family_descends (prefixWord ++ tailWord_527318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_527321 : List Nat := [1, 2, 1, 2, 5, 2, 1, 3, 1, 2, 3]
def baseStart_527321 : Nat := 118140960795 + 527321 * 2 ^ 59
def prefixEnd_527321 : Nat := 4983230072969 + 3 ^ 40 * 527321 * 2
def baseEnd_527321 : Nat := 270769132209636587862401

theorem tailTrace_527321 : CollatzResearch.WordTrace tailWord_527321 prefixEnd_527321 270769132209636587862401 := by
  unfold tailWord_527321
  simp only [CollatzResearch.WordTrace]
  refine ⟨19232976922613551101925817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12821984615075700734617211 19232976922613551101925817)
  ·
    refine ⟨14424732691960163326444363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19232976922613551101925817 14424732691960163326444363)
    ·
      refine ⟨21637099037940244989666545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14424732691960163326444363 21637099037940244989666545)
      ·
        refine ⟨16227824278455183742249909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21637099037940244989666545 16227824278455183742249909)
        ·
          refine ⟨1521358526105173475835929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16227824278455183742249909 1521358526105173475835929)
          ·
            refine ⟨1141018894578880106876947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1521358526105173475835929 1141018894578880106876947)
            ·
              refine ⟨1711528341868320160315421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1141018894578880106876947 1711528341868320160315421)
              ·
                refine ⟨641823128200620060118283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1711528341868320160315421 641823128200620060118283)
                ·
                  refine ⟨962734692300930090177425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 641823128200620060118283 962734692300930090177425)
                  ·
                    refine ⟨722051019225697567633069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 962734692300930090177425 722051019225697567633069)
                    ·
                      refine ⟨270769132209636587862401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 722051019225697567633069 270769132209636587862401)
                      ·
                        rfl

theorem cell23_527321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 1, 3, 1, 2, 3].length) (baseStart_527321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_527321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_527321 prefixEnd_527321 := by exact prefixLift 527321
  have htrace : WordTrace (prefixWord ++ tailWord_527321) baseStart_527321 baseEnd_527321 := by
    simpa [prefixWord, tailWord_527321, baseEnd_527321] using wordTrace_append hprefix tailTrace_527321
  have hstable : (prefixWord ++ tailWord_527321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_527321).length < 2 ^ (prefixWord ++ tailWord_527321).sum := by decide
  have hdescent : baseEnd_527321 < baseStart_527321 := by decide
  rcases family_descends (prefixWord ++ tailWord_527321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_527335 : List Nat := [1, 1, 5, 2, 2, 1, 2, 4, 1, 2, 2]
def baseStart_527335 : Nat := 118140960795 + 527335 * 2 ^ 59
def prefixEnd_527335 : Nat := 4983230072969 + 3 ^ 40 * 527335 * 2
def baseEnd_527335 : Nat := 270776320938799533087337

theorem tailTrace_527335 : CollatzResearch.WordTrace tailWord_527335 prefixEnd_527335 270776320938799533087337 := by
  unfold tailWord_527335
  simp only [CollatzResearch.WordTrace]
  refine ⟨19233487544562831492935459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12822325029708554328623639 19233487544562831492935459)
  ·
    refine ⟨28850231316844247239403189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19233487544562831492935459 28850231316844247239403189)
    ·
      refine ⟨2704709185954148178694049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 28850231316844247239403189 2704709185954148178694049)
      ·
        refine ⟨2028531889465611134020537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2704709185954148178694049 2028531889465611134020537)
        ·
          refine ⟨1521398917099208350515403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2028531889465611134020537 1521398917099208350515403)
          ·
            refine ⟨2282098375648812525773105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1521398917099208350515403 2282098375648812525773105)
            ·
              refine ⟨1711573781736609394329829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2282098375648812525773105 1711573781736609394329829)
              ·
                refine ⟨320920084075614261436843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1711573781736609394329829 320920084075614261436843)
                ·
                  refine ⟨481380126113421392155265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 320920084075614261436843 481380126113421392155265)
                  ·
                    refine ⟨361035094585066044116449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 481380126113421392155265 361035094585066044116449)
                    ·
                      refine ⟨270776320938799533087337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 361035094585066044116449 270776320938799533087337)
                      ·
                        rfl

theorem cell23_527335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 2, 4, 1, 2, 2].length) (baseStart_527335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_527335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_527335 prefixEnd_527335 := by exact prefixLift 527335
  have htrace : WordTrace (prefixWord ++ tailWord_527335) baseStart_527335 baseEnd_527335 := by
    simpa [prefixWord, tailWord_527335, baseEnd_527335] using wordTrace_append hprefix tailTrace_527335
  have hstable : (prefixWord ++ tailWord_527335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_527335).length < 2 ^ (prefixWord ++ tailWord_527335).sum := by decide
  have hdescent : baseEnd_527335 < baseStart_527335 := by decide
  rcases family_descends (prefixWord ++ tailWord_527335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_527358 : List Nat := [4, 2, 2, 2, 2, 2, 2, 7]
def baseStart_527358 : Nat := 118140960795 + 527358 * 2 ^ 59
def prefixEnd_527358 : Nat := 4983230072969 + 3 ^ 40 * 527358 * 2
def baseEnd_527358 : Nat := 10029190036809368262953

theorem tailTrace_527358 : CollatzResearch.WordTrace tailWord_527358 prefixEnd_527358 10029190036809368262953 := by
  unfold tailWord_527358
  simp only [CollatzResearch.WordTrace]
  refine ⟨2404290802934938302627841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12822884282319670947348485 2404290802934938302627841)
  ·
    refine ⟨1803218102201203726970881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2404290802934938302627841 1803218102201203726970881)
    ·
      refine ⟨1352413576650902795228161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1803218102201203726970881 1352413576650902795228161)
      ·
        refine ⟨1014310182488177096421121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1352413576650902795228161 1014310182488177096421121)
        ·
          refine ⟨760732636866132822315841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1014310182488177096421121 760732636866132822315841)
          ·
            refine ⟨570549477649599616736881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 760732636866132822315841 570549477649599616736881)
            ·
              refine ⟨427912108237199712552661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 570549477649599616736881 427912108237199712552661)
              ·
                refine ⟨10029190036809368262953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 427912108237199712552661 10029190036809368262953)
                ·
                  rfl

theorem cell23_527358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 2, 7].length) (baseStart_527358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_527358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_527358 prefixEnd_527358 := by exact prefixLift 527358
  have htrace : WordTrace (prefixWord ++ tailWord_527358) baseStart_527358 baseEnd_527358 := by
    simpa [prefixWord, tailWord_527358, baseEnd_527358] using wordTrace_append hprefix tailTrace_527358
  have hstable : (prefixWord ++ tailWord_527358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_527358).length < 2 ^ (prefixWord ++ tailWord_527358).sum := by decide
  have hdescent : baseEnd_527358 < baseStart_527358 := by decide
  rcases family_descends (prefixWord ++ tailWord_527358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_527402 : List Nat := [3, 1, 4, 1, 3, 2, 2, 1, 2, 1, 3]
def baseStart_527402 : Nat := 118140960795 + 527402 * 2 ^ 59
def prefixEnd_527402 : Nat := 4983230072969 + 3 ^ 40 * 527402 * 2
def baseEnd_527402 : Nat := 270810724142650770949529

theorem tailTrace_527402 : CollatzResearch.WordTrace tailWord_527402 prefixEnd_527402 270810724142650770949529 := by
  unfold tailWord_527402
  simp only [CollatzResearch.WordTrace]
  refine ⟨4808982808830025483906115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12823954156880067957082973 4808982808830025483906115)
  ·
    refine ⟨7213474213245038225859173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4808982808830025483906115 7213474213245038225859173)
    ·
      refine ⟨1352526414983444667348595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7213474213245038225859173 1352526414983444667348595)
      ·
        refine ⟨2028789622475167001022893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1352526414983444667348595 2028789622475167001022893)
        ·
          refine ⟨760796108428187625383585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2028789622475167001022893 760796108428187625383585)
          ·
            refine ⟨570597081321140719037689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 760796108428187625383585 570597081321140719037689)
            ·
              refine ⟨427947810990855539278267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 570597081321140719037689 427947810990855539278267)
              ·
                refine ⟨641921716486283308917401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 427947810990855539278267 641921716486283308917401)
                ·
                  refine ⟨481441287364712481688051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 641921716486283308917401 481441287364712481688051)
                  ·
                    refine ⟨722161931047068722532077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 481441287364712481688051 722161931047068722532077)
                    ·
                      refine ⟨270810724142650770949529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 722161931047068722532077 270810724142650770949529)
                      ·
                        rfl

theorem cell23_527402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 2, 1, 2, 1, 3].length) (baseStart_527402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_527402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_527402 prefixEnd_527402 := by exact prefixLift 527402
  have htrace : WordTrace (prefixWord ++ tailWord_527402) baseStart_527402 baseEnd_527402 := by
    simpa [prefixWord, tailWord_527402, baseEnd_527402] using wordTrace_append hprefix tailTrace_527402
  have hstable : (prefixWord ++ tailWord_527402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_527402).length < 2 ^ (prefixWord ++ tailWord_527402).sum := by decide
  have hdescent : baseEnd_527402 < baseStart_527402 := by decide
  rcases family_descends (prefixWord ++ tailWord_527402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_527408 : List Nat := [2, 1, 1, 1, 2, 4, 3, 3, 2, 2, 2]
def baseStart_527408 : Nat := 118140960795 + 527408 * 2 ^ 59
def prefixEnd_527408 : Nat := 4983230072969 + 3 ^ 40 * 527408 * 2
def baseEnd_527408 : Nat := 270813805026577747474501

theorem tailTrace_527408 : CollatzResearch.WordTrace tailWord_527408 prefixEnd_527408 270813805026577747474501 := by
  unfold tailWord_527408
  simp only [CollatzResearch.WordTrace]
  refine ⟨9618075036649182480171439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12824100048865576640228585 9618075036649182480171439)
  ·
    refine ⟨14427112554973773720257159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9618075036649182480171439 14427112554973773720257159)
    ·
      refine ⟨21640668832460660580385739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14427112554973773720257159 21640668832460660580385739)
      ·
        refine ⟨32461003248690990870578609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21640668832460660580385739 32461003248690990870578609)
        ·
          refine ⟨24345752436518243152933957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32461003248690990870578609 24345752436518243152933957)
          ·
            refine ⟨4564828581847170591175117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24345752436518243152933957 4564828581847170591175117)
            ·
              refine ⟨1711810718192688971690669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4564828581847170591175117 1711810718192688971690669)
              ·
                refine ⟨641929019322258364384001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1711810718192688971690669 641929019322258364384001)
                ·
                  refine ⟨481446764491693773288001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 641929019322258364384001 481446764491693773288001)
                  ·
                    refine ⟨361085073368770329966001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 481446764491693773288001 361085073368770329966001)
                    ·
                      refine ⟨270813805026577747474501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 361085073368770329966001 270813805026577747474501)
                      ·
                        rfl

theorem cell23_527408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3, 3, 2, 2, 2].length) (baseStart_527408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_527408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_527408 prefixEnd_527408 := by exact prefixLift 527408
  have htrace : WordTrace (prefixWord ++ tailWord_527408) baseStart_527408 baseEnd_527408 := by
    simpa [prefixWord, tailWord_527408, baseEnd_527408] using wordTrace_append hprefix tailTrace_527408
  have hstable : (prefixWord ++ tailWord_527408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_527408).length < 2 ^ (prefixWord ++ tailWord_527408).sum := by decide
  have hdescent : baseEnd_527408 < baseStart_527408 := by decide
  rcases family_descends (prefixWord ++ tailWord_527408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_527412 : List Nat := [2, 5, 1, 2, 1, 3, 1, 2, 1, 3, 2]
def baseStart_527412 : Nat := 118140960795 + 527412 * 2 ^ 59
def prefixEnd_527412 : Nat := 4983230072969 + 3 ^ 40 * 527412 * 2
def baseEnd_527412 : Nat := 270815858949195731824483

theorem tailTrace_527412 : CollatzResearch.WordTrace tailWord_527412 prefixEnd_527412 270815858949195731824483 := by
  unfold tailWord_527412
  simp only [CollatzResearch.WordTrace]
  refine ⟨9618147982641936821744245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12824197310189249095658993 9618147982641936821744245)
  ·
    refine ⟨901701373372681577038523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9618147982641936821744245 901701373372681577038523)
    ·
      refine ⟨1352552060059022365557785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 901701373372681577038523 1352552060059022365557785)
      ·
        refine ⟨1014414045044266774168339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1352552060059022365557785 1014414045044266774168339)
        ·
          refine ⟨1521621067566400161252509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1014414045044266774168339 1521621067566400161252509)
          ·
            refine ⟨570607900337400060469691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1521621067566400161252509 570607900337400060469691)
            ·
              refine ⟨855911850506100090704537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 570607900337400060469691 855911850506100090704537)
              ·
                refine ⟨641933887879575068028403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 855911850506100090704537 641933887879575068028403)
                ·
                  refine ⟨962900831819362602042605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 641933887879575068028403 962900831819362602042605)
                  ·
                    refine ⟨361087811932260975765977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 962900831819362602042605 361087811932260975765977)
                    ·
                      refine ⟨270815858949195731824483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 361087811932260975765977 270815858949195731824483)
                      ·
                        rfl

theorem cell23_527412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 1, 2, 1, 3, 2].length) (baseStart_527412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_527412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_527412 prefixEnd_527412 := by exact prefixLift 527412
  have htrace : WordTrace (prefixWord ++ tailWord_527412) baseStart_527412 baseEnd_527412 := by
    simpa [prefixWord, tailWord_527412, baseEnd_527412] using wordTrace_append hprefix tailTrace_527412
  have hstable : (prefixWord ++ tailWord_527412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_527412).length < 2 ^ (prefixWord ++ tailWord_527412).sum := by decide
  have hdescent : baseEnd_527412 < baseStart_527412 := by decide
  rcases family_descends (prefixWord ++ tailWord_527412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_527458 : List Nat := [3, 3, 2, 2, 1, 2, 1, 1, 2, 3, 3]
def baseStart_527458 : Nat := 118140960795 + 527458 * 2 ^ 59
def prefixEnd_527458 : Nat := 4983230072969 + 3 ^ 40 * 527458 * 2
def baseEnd_527458 : Nat := 270839479059302551849271

theorem tailTrace_527458 : CollatzResearch.WordTrace tailWord_527458 prefixEnd_527458 270839479059302551849271 := by
  unfold tailWord_527458
  simp only [CollatzResearch.WordTrace]
  refine ⟨4809493430779305874915757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12825315815411482333108685 4809493430779305874915757)
  ·
    refine ⟨1803560036542239703093409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4809493430779305874915757 1803560036542239703093409)
    ·
      refine ⟨1352670027406679777320057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1803560036542239703093409 1352670027406679777320057)
      ·
        refine ⟨1014502520555009832990043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1352670027406679777320057 1014502520555009832990043)
        ·
          refine ⟨1521753780832514749485065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1014502520555009832990043 1521753780832514749485065)
          ·
            refine ⟨1141315335624386062113799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1521753780832514749485065 1141315335624386062113799)
            ·
              refine ⟨1711973003436579093170699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1141315335624386062113799 1711973003436579093170699)
              ·
                refine ⟨2567959505154868639756049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1711973003436579093170699 2567959505154868639756049)
                ·
                  refine ⟨1925969628866151479817037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2567959505154868639756049 1925969628866151479817037)
                  ·
                    refine ⟨722238610824806804931389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1925969628866151479817037 722238610824806804931389)
                    ·
                      refine ⟨270839479059302551849271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 722238610824806804931389 270839479059302551849271)
                      ·
                        rfl

theorem cell23_527458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 1, 1, 2, 3, 3].length) (baseStart_527458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_527458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_527458 prefixEnd_527458 := by exact prefixLift 527458
  have htrace : WordTrace (prefixWord ++ tailWord_527458) baseStart_527458 baseEnd_527458 := by
    simpa [prefixWord, tailWord_527458, baseEnd_527458] using wordTrace_append hprefix tailTrace_527458
  have hstable : (prefixWord ++ tailWord_527458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_527458).length < 2 ^ (prefixWord ++ tailWord_527458).sum := by decide
  have hdescent : baseEnd_527458 < baseStart_527458 := by decide
  rcases family_descends (prefixWord ++ tailWord_527458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_527481 : List Nat := [1, 2, 1, 3, 5, 1, 1, 1, 1, 3, 4]
def baseStart_527481 : Nat := 118140960795 + 527481 * 2 ^ 59
def prefixEnd_527481 : Nat := 4983230072969 + 3 ^ 40 * 527481 * 2
def baseEnd_527481 : Nat := 270851289114355961861665

theorem tailTrace_527481 : CollatzResearch.WordTrace tailWord_527481 prefixEnd_527481 270851289114355961861665 := by
  unfold tailWord_527481
  simp only [CollatzResearch.WordTrace]
  refine ⟨19238812602033898427750297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12825875068022598951833531 19238812602033898427750297)
  ·
    refine ⟨14429109451525423820812723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19238812602033898427750297 14429109451525423820812723)
    ·
      refine ⟨21643664177288135731219085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14429109451525423820812723 21643664177288135731219085)
      ·
        refine ⟨8116374066483050899207157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21643664177288135731219085 8116374066483050899207157)
        ·
          refine ⟨760910068732786021800671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8116374066483050899207157 760910068732786021800671)
          ·
            refine ⟨1141365103099179032701007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 760910068732786021800671 1141365103099179032701007)
            ·
              refine ⟨1712047654648768549051511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1141365103099179032701007 1712047654648768549051511)
              ·
                refine ⟨2568071481973152823577267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1712047654648768549051511 2568071481973152823577267)
                ·
                  refine ⟨3852107222959729235365901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2568071481973152823577267 3852107222959729235365901)
                  ·
                    refine ⟨1444540208609898463262213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3852107222959729235365901 1444540208609898463262213)
                    ·
                      refine ⟨270851289114355961861665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1444540208609898463262213 270851289114355961861665)
                      ·
                        rfl

theorem cell23_527481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 1, 1, 1, 3, 4].length) (baseStart_527481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_527481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_527481 prefixEnd_527481 := by exact prefixLift 527481
  have htrace : WordTrace (prefixWord ++ tailWord_527481) baseStart_527481 baseEnd_527481 := by
    simpa [prefixWord, tailWord_527481, baseEnd_527481] using wordTrace_append hprefix tailTrace_527481
  have hstable : (prefixWord ++ tailWord_527481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_527481).length < 2 ^ (prefixWord ++ tailWord_527481).sum := by decide
  have hdescent : baseEnd_527481 < baseStart_527481 := by decide
  rcases family_descends (prefixWord ++ tailWord_527481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_527504 : List Nat := [2, 1, 1, 1, 1, 1, 4, 6, 6]
def baseStart_527504 : Nat := 118140960795 + 527504 * 2 ^ 59
def prefixEnd_527504 : Nat := 4983230072969 + 3 ^ 40 * 527504 * 2
def baseEnd_527504 : Nat := 30095899907712152430451

theorem tailTrace_527504 : CollatzResearch.WordTrace tailWord_527504 prefixEnd_527504 30095899907712152430451 := by
  unfold tailWord_527504
  simp only [CollatzResearch.WordTrace]
  refine ⟨9619825740475286677918783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12826434320633715570558377 9619825740475286677918783)
  ·
    refine ⟨14429738610712930016878175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9619825740475286677918783 14429738610712930016878175)
    ·
      refine ⟨21644607916069395025317263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14429738610712930016878175 21644607916069395025317263)
      ·
        refine ⟨32466911874104092537975895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21644607916069395025317263 32466911874104092537975895)
        ·
          refine ⟨48700367811156138806963843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32466911874104092537975895 48700367811156138806963843)
          ·
            refine ⟨73050551716734208210445765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48700367811156138806963843 73050551716734208210445765)
            ·
              refine ⟨13696978446887664039458581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 73050551716734208210445765 13696978446887664039458581)
              ·
                refine ⟨642045864697859251849621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 13696978446887664039458581 642045864697859251849621)
                ·
                  refine ⟨30095899907712152430451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 642045864697859251849621 30095899907712152430451)
                  ·
                    rfl

theorem cell23_527504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 6, 6].length) (baseStart_527504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_527504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_527504 prefixEnd_527504 := by exact prefixLift 527504
  have htrace : WordTrace (prefixWord ++ tailWord_527504) baseStart_527504 baseEnd_527504 := by
    simpa [prefixWord, tailWord_527504, baseEnd_527504] using wordTrace_append hprefix tailTrace_527504
  have hstable : (prefixWord ++ tailWord_527504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_527504).length < 2 ^ (prefixWord ++ tailWord_527504).sum := by decide
  have hdescent : baseEnd_527504 < baseStart_527504 := by decide
  rcases family_descends (prefixWord ++ tailWord_527504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_527518 : List Nat := [4, 3, 1, 1, 2, 1, 1, 2, 1, 4, 3]
def baseStart_527518 : Nat := 118140960795 + 527518 * 2 ^ 59
def prefixEnd_527518 : Nat := 4983230072969 + 3 ^ 40 * 527518 * 2
def baseEnd_527518 : Nat := 270870287898572317098995

theorem tailTrace_527518 : CollatzResearch.WordTrace tailWord_527518 prefixEnd_527518 270870287898572317098995 := by
  unfold tailWord_527518
  simp only [CollatzResearch.WordTrace]
  refine ⟨2405020262862481718355901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12826774735266569164564805 2405020262862481718355901)
  ·
    refine ⟨901882598573430644383463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2405020262862481718355901 901882598573430644383463)
    ·
      refine ⟨1352823897860145966575195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 901882598573430644383463 1352823897860145966575195)
      ·
        refine ⟨2029235846790218949862793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1352823897860145966575195 2029235846790218949862793)
        ·
          refine ⟨1521926885092664212397095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2029235846790218949862793 1521926885092664212397095)
          ·
            refine ⟨2282890327638996318595643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1521926885092664212397095 2282890327638996318595643)
            ·
              refine ⟨3424335491458494477893465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2282890327638996318595643 3424335491458494477893465)
              ·
                refine ⟨2568251618593870858420099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3424335491458494477893465 2568251618593870858420099)
                ·
                  refine ⟨3852377427890806287630149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2568251618593870858420099 3852377427890806287630149)
                  ·
                    refine ⟨722320767729526178930653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3852377427890806287630149 722320767729526178930653)
                    ·
                      refine ⟨270870287898572317098995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 722320767729526178930653 270870287898572317098995)
                      ·
                        rfl

theorem cell23_527518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 2, 1, 4, 3].length) (baseStart_527518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_527518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_527518 prefixEnd_527518 := by exact prefixLift 527518
  have htrace : WordTrace (prefixWord ++ tailWord_527518) baseStart_527518 baseEnd_527518 := by
    simpa [prefixWord, tailWord_527518, baseEnd_527518] using wordTrace_append hprefix tailTrace_527518
  have hstable : (prefixWord ++ tailWord_527518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_527518).length < 2 ^ (prefixWord ++ tailWord_527518).sum := by decide
  have hdescent : baseEnd_527518 < baseStart_527518 := by decide
  rcases family_descends (prefixWord ++ tailWord_527518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_527551 : List Nat := [1, 1, 2, 2, 2, 2, 4, 3, 1, 5]
def baseStart_527551 : Nat := 118140960795 + 527551 * 2 ^ 59
def prefixEnd_527551 : Nat := 4983230072969 + 3 ^ 40 * 527551 * 2
def baseEnd_527551 : Nat := 90295744253390229328781

theorem tailTrace_527551 : CollatzResearch.WordTrace tailWord_527551 prefixEnd_527551 90295744253390229328781 := by
  unfold tailWord_527551
  simp only [CollatzResearch.WordTrace]
  refine ⟨19241365711780300382798507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12827577141186866921865671 19241365711780300382798507)
  ·
    refine ⟨28862048567670450574197761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19241365711780300382798507 28862048567670450574197761)
    ·
      refine ⟨21646536425752837930648321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28862048567670450574197761 21646536425752837930648321)
      ·
        refine ⟨16234902319314628447986241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21646536425752837930648321 16234902319314628447986241)
        ·
          refine ⟨12176176739485971335989681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16234902319314628447986241 12176176739485971335989681)
          ·
            refine ⟨9132132554614478501992261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12176176739485971335989681 9132132554614478501992261)
            ·
              refine ⟨1712274853990214719123549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9132132554614478501992261 1712274853990214719123549)
              ·
                refine ⟨642103070246330519671331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1712274853990214719123549 642103070246330519671331)
                ·
                  refine ⟨963154605369495779506997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 642103070246330519671331 963154605369495779506997)
                  ·
                    refine ⟨90295744253390229328781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 963154605369495779506997 90295744253390229328781)
                    ·
                      rfl

theorem cell23_527551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4, 3, 1, 5].length) (baseStart_527551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_527551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_527551 prefixEnd_527551 := by exact prefixLift 527551
  have htrace : WordTrace (prefixWord ++ tailWord_527551) baseStart_527551 baseEnd_527551 := by
    simpa [prefixWord, tailWord_527551, baseEnd_527551] using wordTrace_append hprefix tailTrace_527551
  have hstable : (prefixWord ++ tailWord_527551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_527551).length < 2 ^ (prefixWord ++ tailWord_527551).sum := by decide
  have hdescent : baseEnd_527551 < baseStart_527551 := by decide
  rcases family_descends (prefixWord ++ tailWord_527551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_527572 : List Nat := [2, 4, 1, 4, 1, 2, 2, 1, 6]
def baseStart_527572 : Nat := 118140960795 + 527572 * 2 ^ 59
def prefixEnd_527572 : Nat := 4983230072969 + 3 ^ 40 * 527572 * 2
def baseEnd_527572 : Nat := 30099779539323900647083

theorem tailTrace_527572 : CollatzResearch.WordTrace tailWord_527572 prefixEnd_527572 30099779539323900647083 := by
  unfold tailWord_527572
  simp only [CollatzResearch.WordTrace]
  refine ⟨9621065822352110484656485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12828087763136147312875313 9621065822352110484656485)
  ·
    refine ⟨1803949841691020715873091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9621065822352110484656485 1803949841691020715873091)
    ·
      refine ⟨2705924762536531073809637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1803949841691020715873091 2705924762536531073809637)
      ·
        refine ⟨507360892975599576339307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2705924762536531073809637 507360892975599576339307)
        ·
          refine ⟨761041339463399364508961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 507360892975599576339307 761041339463399364508961)
          ·
            refine ⟨570781004597549523381721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 761041339463399364508961 570781004597549523381721)
            ·
              refine ⟨428085753448162142536291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 570781004597549523381721 428085753448162142536291)
              ·
                refine ⟨642128630172243213804437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 428085753448162142536291 642128630172243213804437)
                ·
                  refine ⟨30099779539323900647083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 642128630172243213804437 30099779539323900647083)
                  ·
                    rfl

theorem cell23_527572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 2, 1, 6].length) (baseStart_527572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_527572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_527572 prefixEnd_527572 := by exact prefixLift 527572
  have htrace : WordTrace (prefixWord ++ tailWord_527572) baseStart_527572 baseEnd_527572 := by
    simpa [prefixWord, tailWord_527572, baseEnd_527572] using wordTrace_append hprefix tailTrace_527572
  have hstable : (prefixWord ++ tailWord_527572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_527572).length < 2 ^ (prefixWord ++ tailWord_527572).sum := by decide
  have hdescent : baseEnd_527572 < baseStart_527572 := by decide
  rcases family_descends (prefixWord ++ tailWord_527572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_527588 : List Nat := [2, 3, 1, 1, 1, 2, 5, 2, 1, 1, 4]
def baseStart_527588 : Nat := 118140960795 + 527588 * 2 ^ 59
def prefixEnd_527588 : Nat := 4983230072969 + 3 ^ 40 * 527588 * 2
def baseEnd_527588 : Nat := 270906231544387043223673

theorem tailTrace_527588 : CollatzResearch.WordTrace tailWord_527588 prefixEnd_527588 270906231544387043223673 := by
  unfold tailWord_527588
  simp only [CollatzResearch.WordTrace]
  refine ⟨9621357606323127850947709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12828476808430837134596945 9621357606323127850947709)
  ·
    refine ⟨3608009102371172944105391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9621357606323127850947709 3608009102371172944105391)
    ·
      refine ⟨5412013653556759416158087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3608009102371172944105391 5412013653556759416158087)
      ·
        refine ⟨8118020480335139124237131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5412013653556759416158087 8118020480335139124237131)
        ·
          refine ⟨12177030720502708686355697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8118020480335139124237131 12177030720502708686355697)
          ·
            refine ⟨9132773040377031514766773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12177030720502708686355697 9132773040377031514766773)
            ·
              refine ⟨856197472535346704509385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9132773040377031514766773 856197472535346704509385)
              ·
                refine ⟨642148104401510028382039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 856197472535346704509385 642148104401510028382039)
                ·
                  refine ⟨963222156602265042573059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 642148104401510028382039 963222156602265042573059)
                  ·
                    refine ⟨1444833234903397563859589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 963222156602265042573059 1444833234903397563859589)
                    ·
                      refine ⟨270906231544387043223673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1444833234903397563859589 270906231544387043223673)
                      ·
                        rfl

theorem cell23_527588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 5, 2, 1, 1, 4].length) (baseStart_527588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_527588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_527588 prefixEnd_527588 := by exact prefixLift 527588
  have htrace : WordTrace (prefixWord ++ tailWord_527588) baseStart_527588 baseEnd_527588 := by
    simpa [prefixWord, tailWord_527588, baseEnd_527588] using wordTrace_append hprefix tailTrace_527588
  have hstable : (prefixWord ++ tailWord_527588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_527588).length < 2 ^ (prefixWord ++ tailWord_527588).sum := by decide
  have hdescent : baseEnd_527588 < baseStart_527588 := by decide
  rcases family_descends (prefixWord ++ tailWord_527588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_527621 : List Nat := [1, 3, 1, 1, 2, 1, 3, 2, 3, 3, 3]
def baseStart_527621 : Nat := 118140960795 + 527621 * 2 ^ 59
def prefixEnd_527621 : Nat := 4983230072969 + 3 ^ 40 * 527621 * 2
def baseEnd_527621 : Nat := 270923176405985414111021

theorem tailTrace_527621 : CollatzResearch.WordTrace tailWord_527621 prefixEnd_527621 270923176405985414111021 := by
  unfold tailWord_527621
  simp only [CollatzResearch.WordTrace]
  refine ⟨19243918821526702337846717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12829279214351134891897811 19243918821526702337846717)
  ·
    refine ⟨7216469558072513376692519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19243918821526702337846717 7216469558072513376692519)
    ·
      refine ⟨10824704337108770065038779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7216469558072513376692519 10824704337108770065038779)
      ·
        refine ⟨16237056505663155097558169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10824704337108770065038779 16237056505663155097558169)
        ·
          refine ⟨12177792379247366323168627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16237056505663155097558169 12177792379247366323168627)
          ·
            refine ⟨18266688568871049484752941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12177792379247366323168627 18266688568871049484752941)
            ·
              refine ⟨6850008213326643556782353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18266688568871049484752941 6850008213326643556782353)
              ·
                refine ⟨5137506159994982667586765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6850008213326643556782353 5137506159994982667586765)
                ·
                  refine ⟨1926564809998118500345037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5137506159994982667586765 1926564809998118500345037)
                  ·
                    refine ⟨722461803749294437629389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1926564809998118500345037 722461803749294437629389)
                    ·
                      refine ⟨270923176405985414111021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 722461803749294437629389 270923176405985414111021)
                      ·
                        rfl

theorem cell23_527621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 2, 3, 3, 3].length) (baseStart_527621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_527621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_527621 prefixEnd_527621 := by exact prefixLift 527621
  have htrace : WordTrace (prefixWord ++ tailWord_527621) baseStart_527621 baseEnd_527621 := by
    simpa [prefixWord, tailWord_527621, baseEnd_527621] using wordTrace_append hprefix tailTrace_527621
  have hstable : (prefixWord ++ tailWord_527621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_527621).length < 2 ^ (prefixWord ++ tailWord_527621).sum := by decide
  have hdescent : baseEnd_527621 < baseStart_527621 := by decide
  rcases family_descends (prefixWord ++ tailWord_527621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_527686 : List Nat := [6, 1, 1, 3, 2, 1, 1, 1, 1, 2, 4]
def baseStart_527686 : Nat := 118140960795 + 527686 * 2 ^ 59
def prefixEnd_527686 : Nat := 4983230072969 + 3 ^ 40 * 527686 * 2
def baseEnd_527686 : Nat := 270956552648527659798223

theorem tailTrace_527686 : CollatzResearch.WordTrace tailWord_527686 prefixEnd_527686 270956552648527659798223 := by
  unfold tailWord_527686
  simp only [CollatzResearch.WordTrace]
  refine ⟨601446548946600576217591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 12830859710860812292641941 601446548946600576217591)
  ·
    refine ⟨902169823419900864326387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 601446548946600576217591 902169823419900864326387)
    ·
      refine ⟨1353254735129851296489581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 902169823419900864326387 1353254735129851296489581)
      ·
        refine ⟨507470525673694236183593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1353254735129851296489581 507470525673694236183593)
        ·
          refine ⟨380602894255270677137695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 507470525673694236183593 380602894255270677137695)
          ·
            refine ⟨570904341382906015706543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 380602894255270677137695 570904341382906015706543)
            ·
              refine ⟨856356512074359023559815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 570904341382906015706543 856356512074359023559815)
              ·
                refine ⟨1284534768111538535339723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 856356512074359023559815 1284534768111538535339723)
                ·
                  refine ⟨1926802152167307803009585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1284534768111538535339723 1926802152167307803009585)
                  ·
                    refine ⟨1445101614125480852257189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1926802152167307803009585 1445101614125480852257189)
                    ·
                      refine ⟨270956552648527659798223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1445101614125480852257189 270956552648527659798223)
                      ·
                        rfl

theorem cell23_527686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 1, 1, 1, 2, 4].length) (baseStart_527686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_527686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_527686 prefixEnd_527686 := by exact prefixLift 527686
  have htrace : WordTrace (prefixWord ++ tailWord_527686) baseStart_527686 baseEnd_527686 := by
    simpa [prefixWord, tailWord_527686, baseEnd_527686] using wordTrace_append hprefix tailTrace_527686
  have hstable : (prefixWord ++ tailWord_527686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_527686).length < 2 ^ (prefixWord ++ tailWord_527686).sum := by decide
  have hdescent : baseEnd_527686 < baseStart_527686 := by decide
  rcases family_descends (prefixWord ++ tailWord_527686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_527735 : List Nat := [1, 1, 3, 1, 1, 2, 7, 2, 5]
def baseStart_527735 : Nat := 118140960795 + 527735 * 2 ^ 59
def prefixEnd_527735 : Nat := 4983230072969 + 3 ^ 40 * 527735 * 2
def baseEnd_527735 : Nat := 30109079244510885342833

theorem tailTrace_527735 : CollatzResearch.WordTrace tailWord_527735 prefixEnd_527735 30109079244510885342833 := by
  unfold tailWord_527735
  simp only [CollatzResearch.WordTrace]
  refine ⟨19248076743113699807496659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12832051162075799871664439 19248076743113699807496659)
  ·
    refine ⟨28872115114670549711244989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19248076743113699807496659 28872115114670549711244989)
    ·
      refine ⟨10827043168001456141716871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28872115114670549711244989 10827043168001456141716871)
      ·
        refine ⟨16240564752002184212575307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10827043168001456141716871 16240564752002184212575307)
        ·
          refine ⟨24360847128003276318862961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16240564752002184212575307 24360847128003276318862961)
          ·
            refine ⟨18270635346002457239147221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24360847128003276318862961 18270635346002457239147221)
            ·
              refine ⟨428218015921932591542513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 18270635346002457239147221 428218015921932591542513)
              ·
                refine ⟨321163511941449443656885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 428218015921932591542513 321163511941449443656885)
                ·
                  refine ⟨30109079244510885342833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 321163511941449443656885 30109079244510885342833)
                  ·
                    rfl

theorem cell23_527735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 7, 2, 5].length) (baseStart_527735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_527735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_527735 prefixEnd_527735 := by exact prefixLift 527735
  have htrace : WordTrace (prefixWord ++ tailWord_527735) baseStart_527735 baseEnd_527735 := by
    simpa [prefixWord, tailWord_527735, baseEnd_527735] using wordTrace_append hprefix tailTrace_527735
  have hstable : (prefixWord ++ tailWord_527735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_527735).length < 2 ^ (prefixWord ++ tailWord_527735).sum := by decide
  have hdescent : baseEnd_527735 < baseStart_527735 := by decide
  rcases family_descends (prefixWord ++ tailWord_527735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_527738 : List Nat := [3, 1, 1, 1, 1, 1, 2, 3, 1, 7, 2]
def baseStart_527738 : Nat := 118140960795 + 527738 * 2 ^ 59
def prefixEnd_527738 : Nat := 4983230072969 + 3 ^ 40 * 527738 * 2
def baseEnd_527738 : Nat := 270983253642561456347983

theorem tailTrace_527738 : CollatzResearch.WordTrace tailWord_527738 prefixEnd_527738 270983253642561456347983 := by
  unfold tailWord_527738
  simp only [CollatzResearch.WordTrace]
  refine ⟨4812046540525707829963967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12832124108068554213237245 4812046540525707829963967)
  ·
    refine ⟨7218069810788561744945951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4812046540525707829963967 7218069810788561744945951)
    ·
      refine ⟨10827104716182842617418927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7218069810788561744945951 10827104716182842617418927)
      ·
        refine ⟨16240657074274263926128391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10827104716182842617418927 16240657074274263926128391)
        ·
          refine ⟨24360985611411395889192587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16240657074274263926128391 24360985611411395889192587)
          ·
            refine ⟨36541478417117093833788881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24360985611411395889192587 36541478417117093833788881)
            ·
              refine ⟨27406108812837820375341661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36541478417117093833788881 27406108812837820375341661)
              ·
                refine ⟨10277290804814182640753123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27406108812837820375341661 10277290804814182640753123)
                ·
                  refine ⟨15415936207221273961129685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10277290804814182640753123 15415936207221273961129685)
                  ·
                    refine ⟨361311004856748608463977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15415936207221273961129685 361311004856748608463977)
                    ·
                      refine ⟨270983253642561456347983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 361311004856748608463977 270983253642561456347983)
                      ·
                        rfl

theorem cell23_527738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 3, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 3, 1, 7, 2].length) (baseStart_527738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_527738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_527738 prefixEnd_527738 := by exact prefixLift 527738
  have htrace : WordTrace (prefixWord ++ tailWord_527738) baseStart_527738 baseEnd_527738 := by
    simpa [prefixWord, tailWord_527738, baseEnd_527738] using wordTrace_append hprefix tailTrace_527738
  have hstable : (prefixWord ++ tailWord_527738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_527738).length < 2 ^ (prefixWord ++ tailWord_527738).sum := by decide
  have hdescent : baseEnd_527738 < baseStart_527738 := by decide
  rcases family_descends (prefixWord ++ tailWord_527738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_527746 : List Nat := [3, 4, 2, 1, 1, 2, 1, 3, 2, 2, 2]
def baseStart_527746 : Nat := 118140960795 + 527746 * 2 ^ 59
def prefixEnd_527746 : Nat := 4983230072969 + 3 ^ 40 * 527746 * 2
def baseEnd_527746 : Nat := 270987361487797425047947

theorem tailTrace_527746 : CollatzResearch.WordTrace tailWord_527746 prefixEnd_527746 270987361487797425047947 := by
  unfold tailWord_527746
  simp only [CollatzResearch.WordTrace]
  refine ⟨4812119486518462171536773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12832318630715899124098061 4812119486518462171536773)
  ·
    refine ⟨902272403722211657163145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4812119486518462171536773 902272403722211657163145)
    ·
      refine ⟨676704302791658742872359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 902272403722211657163145 676704302791658742872359)
      ·
        refine ⟨1015056454187488114308539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 676704302791658742872359 1015056454187488114308539)
        ·
          refine ⟨1522584681281232171462809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1015056454187488114308539 1522584681281232171462809)
          ·
            refine ⟨1141938510960924128597107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1522584681281232171462809 1141938510960924128597107)
            ·
              refine ⟨1712907766441386192895661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1141938510960924128597107 1712907766441386192895661)
              ·
                refine ⟨642340412415519822335873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1712907766441386192895661 642340412415519822335873)
                ·
                  refine ⟨481755309311639866751905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 642340412415519822335873 481755309311639866751905)
                  ·
                    refine ⟨361316481983729900063929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 481755309311639866751905 361316481983729900063929)
                    ·
                      refine ⟨270987361487797425047947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 361316481983729900063929 270987361487797425047947)
                      ·
                        rfl

theorem cell23_527746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 1, 3, 2, 2, 2].length) (baseStart_527746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_527746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_527746 prefixEnd_527746 := by exact prefixLift 527746
  have htrace : WordTrace (prefixWord ++ tailWord_527746) baseStart_527746 baseEnd_527746 := by
    simpa [prefixWord, tailWord_527746, baseEnd_527746] using wordTrace_append hprefix tailTrace_527746
  have hstable : (prefixWord ++ tailWord_527746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_527746).length < 2 ^ (prefixWord ++ tailWord_527746).sum := by decide
  have hdescent : baseEnd_527746 < baseStart_527746 := by decide
  rcases family_descends (prefixWord ++ tailWord_527746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_527791 : List Nat := [1, 1, 2, 1, 2, 2, 1, 5, 8]
def baseStart_527791 : Nat := 118140960795 + 527791 * 2 ^ 59
def prefixEnd_527791 : Nat := 4983230072969 + 3 ^ 40 * 527791 * 2
def baseEnd_527791 : Nat := 30112274235249972109471

theorem tailTrace_527791 : CollatzResearch.WordTrace tailWord_527791 prefixEnd_527791 30112274235249972109471 := by
  unfold tailWord_527791
  simp only [CollatzResearch.WordTrace]
  refine ⟨19250119230910821371535227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12833412820607214247690151 19250119230910821371535227)
  ·
    refine ⟨28875178846366232057302841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19250119230910821371535227 28875178846366232057302841)
    ·
      refine ⟨21656384134774674042977131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28875178846366232057302841 21656384134774674042977131)
      ·
        refine ⟨32484576202162011064465697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21656384134774674042977131 32484576202162011064465697)
        ·
          refine ⟨24363432151621508298349273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32484576202162011064465697 24363432151621508298349273)
          ·
            refine ⟨18272574113716131223761955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24363432151621508298349273 18272574113716131223761955)
            ·
              refine ⟨27408861170574196835642933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18272574113716131223761955 27408861170574196835642933)
              ·
                refine ⟨2569580734741330953341525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27408861170574196835642933 2569580734741330953341525)
                ·
                  refine ⟨30112274235249972109471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2569580734741330953341525 30112274235249972109471)
                  ·
                    rfl

theorem cell23_527791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 5, 8].length) (baseStart_527791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_527791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_527791 prefixEnd_527791 := by exact prefixLift 527791
  have htrace : WordTrace (prefixWord ++ tailWord_527791) baseStart_527791 baseEnd_527791 := by
    simpa [prefixWord, tailWord_527791, baseEnd_527791] using wordTrace_append hprefix tailTrace_527791
  have hstable : (prefixWord ++ tailWord_527791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_527791).length < 2 ^ (prefixWord ++ tailWord_527791).sum := by decide
  have hdescent : baseEnd_527791 < baseStart_527791 := by decide
  rcases family_descends (prefixWord ++ tailWord_527791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_527808 : List Nat := [2, 1, 1, 2, 3, 1, 4, 3, 6]
def baseStart_527808 : Nat := 118140960795 + 527808 * 2 ^ 59
def prefixEnd_527808 : Nat := 4983230072969 + 3 ^ 40 * 527808 * 2
def baseEnd_527808 : Nat := 30113244143152909163629

theorem tailTrace_527808 : CollatzResearch.WordTrace tailWord_527808 prefixEnd_527808 30113244143152909163629 := by
  unfold tailWord_527808
  simp only [CollatzResearch.WordTrace]
  refine ⟨9625369635924616637452039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12833826181232822183269385 9625369635924616637452039)
  ·
    refine ⟨14438054453886924956178059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9625369635924616637452039 14438054453886924956178059)
    ·
      refine ⟨21657081680830387434267089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14438054453886924956178059 21657081680830387434267089)
      ·
        refine ⟨16242811260622790575700317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21657081680830387434267089 16242811260622790575700317)
        ·
          refine ⟨6091054222733546465887619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16242811260622790575700317 6091054222733546465887619)
          ·
            refine ⟨9136581334100319698831429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6091054222733546465887619 9136581334100319698831429)
            ·
              refine ⟨1713109000143809943530893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9136581334100319698831429 1713109000143809943530893)
              ·
                refine ⟨642415875053928728824085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1713109000143809943530893 642415875053928728824085)
                ·
                  refine ⟨30113244143152909163629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 642415875053928728824085 30113244143152909163629)
                  ·
                    rfl

theorem cell23_527808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4, 3, 6].length) (baseStart_527808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_527808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_527808 prefixEnd_527808 := by exact prefixLift 527808
  have htrace : WordTrace (prefixWord ++ tailWord_527808) baseStart_527808 baseEnd_527808 := by
    simpa [prefixWord, tailWord_527808, baseEnd_527808] using wordTrace_append hprefix tailTrace_527808
  have hstable : (prefixWord ++ tailWord_527808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_527808).length < 2 ^ (prefixWord ++ tailWord_527808).sum := by decide
  have hdescent : baseEnd_527808 < baseStart_527808 := by decide
  rcases family_descends (prefixWord ++ tailWord_527808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_527812 : List Nat := [2, 3, 3, 2, 1, 2, 1, 2, 3, 4]
def baseStart_527812 : Nat := 118140960795 + 527812 * 2 ^ 59
def prefixEnd_527812 : Nat := 4983230072969 + 3 ^ 40 * 527812 * 2
def baseEnd_527812 : Nat := 90340417070331388940881

theorem tailTrace_527812 : CollatzResearch.WordTrace tailWord_527812 prefixEnd_527812 90340417070331388940881 := by
  unfold tailWord_527812
  simp only [CollatzResearch.WordTrace]
  refine ⟨9625442581917370979024845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12833923442556494638699793 9625442581917370979024845)
  ·
    refine ⟨3609540968219014117134317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9625442581917370979024845 3609540968219014117134317)
    ·
      refine ⟨1353577863082130293925369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3609540968219014117134317 1353577863082130293925369)
      ·
        refine ⟨1015183397311597720444027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1353577863082130293925369 1015183397311597720444027)
        ·
          refine ⟨1522775095967396580666041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1015183397311597720444027 1522775095967396580666041)
          ·
            refine ⟨1142081321975547435499531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1522775095967396580666041 1142081321975547435499531)
            ·
              refine ⟨1713121982963321153249297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1142081321975547435499531 1713121982963321153249297)
              ·
                refine ⟨1284841487222490864936973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1713121982963321153249297 1284841487222490864936973)
                ·
                  refine ⟨481815557708434074351365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1284841487222490864936973 481815557708434074351365)
                  ·
                    refine ⟨90340417070331388940881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 481815557708434074351365 90340417070331388940881)
                    ·
                      rfl

theorem cell23_527812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 1, 2, 3, 4].length) (baseStart_527812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_527812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_527812 prefixEnd_527812 := by exact prefixLift 527812
  have htrace : WordTrace (prefixWord ++ tailWord_527812) baseStart_527812 baseEnd_527812 := by
    simpa [prefixWord, tailWord_527812, baseEnd_527812] using wordTrace_append hprefix tailTrace_527812
  have hstable : (prefixWord ++ tailWord_527812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_527812).length < 2 ^ (prefixWord ++ tailWord_527812).sum := by decide
  have hdescent : baseEnd_527812 < baseStart_527812 := by decide
  rcases family_descends (prefixWord ++ tailWord_527812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_527862 : List Nat := [5, 1, 1, 1, 2, 2, 1, 2, 1, 5, 2]
def baseStart_527862 : Nat := 118140960795 + 527862 * 2 ^ 59
def prefixEnd_527862 : Nat := 4983230072969 + 3 ^ 40 * 527862 * 2
def baseEnd_527862 : Nat := 271046925243718971197413

theorem tailTrace_527862 : CollatzResearch.WordTrace tailWord_527862 prefixEnd_527862 271046925243718971197413 := by
  unfold tailWord_527862
  simp only [CollatzResearch.WordTrace]
  refine ⟨1203294300853350031085615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12835139209102400331579893 1203294300853350031085615)
  ·
    refine ⟨1804941451280025046628423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1203294300853350031085615 1804941451280025046628423)
    ·
      refine ⟨2707412176920037569942635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1804941451280025046628423 2707412176920037569942635)
      ·
        refine ⟨4061118265380056354913953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2707412176920037569942635 4061118265380056354913953)
        ·
          refine ⟨3045838699035042266185465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4061118265380056354913953 3045838699035042266185465)
          ·
            refine ⟨2284379024276281699639099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3045838699035042266185465 2284379024276281699639099)
            ·
              refine ⟨3426568536414422549458649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2284379024276281699639099 3426568536414422549458649)
              ·
                refine ⟨2569926402310816912093987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3426568536414422549458649 2569926402310816912093987)
                ·
                  refine ⟨3854889603466225368140981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2569926402310816912093987 3854889603466225368140981)
                  ·
                    refine ⟨361395900324958628263217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3854889603466225368140981 361395900324958628263217)
                    ·
                      refine ⟨271046925243718971197413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 361395900324958628263217 271046925243718971197413)
                      ·
                        rfl

theorem cell23_527862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 2, 1, 5, 2].length) (baseStart_527862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_527862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_527862 prefixEnd_527862 := by exact prefixLift 527862
  have htrace : WordTrace (prefixWord ++ tailWord_527862) baseStart_527862 baseEnd_527862 := by
    simpa [prefixWord, tailWord_527862, baseEnd_527862] using wordTrace_append hprefix tailTrace_527862
  have hstable : (prefixWord ++ tailWord_527862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_527862).length < 2 ^ (prefixWord ++ tailWord_527862).sum := by decide
  have hdescent : baseEnd_527862 < baseStart_527862 := by decide
  rcases family_descends (prefixWord ++ tailWord_527862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_527926 : List Nat := [5, 1, 2, 1, 3, 2, 1, 2, 1, 1, 4]
def baseStart_527926 : Nat := 118140960795 + 527926 * 2 ^ 59
def prefixEnd_527926 : Nat := 4983230072969 + 3 ^ 40 * 527926 * 2
def baseEnd_527926 : Nat := 271079788005606720797119

theorem tailTrace_527926 : CollatzResearch.WordTrace tailWord_527926 prefixEnd_527926 271079788005606720797119 := by
  unfold tailWord_527926
  simp only [CollatzResearch.WordTrace]
  refine ⟨1203440192838858714231227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12836695390281159618466421 1203440192838858714231227)
  ·
    refine ⟨1805160289258288071346841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1203440192838858714231227 1805160289258288071346841)
    ·
      refine ⟨1353870216943716053510131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1805160289258288071346841 1353870216943716053510131)
      ·
        refine ⟨2030805325415574080265197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1353870216943716053510131 2030805325415574080265197)
        ·
          refine ⟨761551997030840280099449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2030805325415574080265197 761551997030840280099449)
          ·
            refine ⟨571163997773130210074587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 761551997030840280099449 571163997773130210074587)
            ·
              refine ⟨856745996659695315111881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 571163997773130210074587 856745996659695315111881)
              ·
                refine ⟨642559497494771486333911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 856745996659695315111881 642559497494771486333911)
                ·
                  refine ⟨963839246242157229500867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 642559497494771486333911 963839246242157229500867)
                  ·
                    refine ⟨1445758869363235844251301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 963839246242157229500867 1445758869363235844251301)
                    ·
                      refine ⟨271079788005606720797119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1445758869363235844251301 271079788005606720797119)
                      ·
                        rfl

theorem cell23_527926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 1, 2, 1, 1, 4].length) (baseStart_527926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_527926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_527926 prefixEnd_527926 := by exact prefixLift 527926
  have htrace : WordTrace (prefixWord ++ tailWord_527926) baseStart_527926 baseEnd_527926 := by
    simpa [prefixWord, tailWord_527926, baseEnd_527926] using wordTrace_append hprefix tailTrace_527926
  have hstable : (prefixWord ++ tailWord_527926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_527926).length < 2 ^ (prefixWord ++ tailWord_527926).sum := by decide
  have hdescent : baseEnd_527926 < baseStart_527926 := by decide
  rcases family_descends (prefixWord ++ tailWord_527926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_527929 : List Nat := [1, 2, 1, 5, 1, 4, 1, 2, 1, 2, 3]
def baseStart_527929 : Nat := 118140960795 + 527929 * 2 ^ 59
def prefixEnd_527929 : Nat := 4983230072969 + 3 ^ 40 * 527929 * 2
def baseEnd_527929 : Nat := 271081328447570209059605

theorem tailTrace_527929 : CollatzResearch.WordTrace tailWord_527929 prefixEnd_527929 271081328447570209059605 := by
  unfold tailWord_527929
  simp only [CollatzResearch.WordTrace]
  refine ⟨19255152504410870940058841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12836768336273913960039227 19255152504410870940058841)
  ·
    refine ⟨14441364378308153205044131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19255152504410870940058841 14441364378308153205044131)
    ·
      refine ⟨21662046567462229807566197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14441364378308153205044131 21662046567462229807566197)
      ·
        refine ⟨2030816865699584044459331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 21662046567462229807566197 2030816865699584044459331)
        ·
          refine ⟨3046225298549376066688997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2030816865699584044459331 3046225298549376066688997)
          ·
            refine ⟨571167243478008012504187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3046225298549376066688997 571167243478008012504187)
            ·
              refine ⟨856750865217012018756281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 571167243478008012504187 856750865217012018756281)
              ·
                refine ⟨642563148912759014067211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 856750865217012018756281 642563148912759014067211)
                ·
                  refine ⟨963844723369138521100817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 642563148912759014067211 963844723369138521100817)
                  ·
                    refine ⟨722883542526853890825613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 963844723369138521100817 722883542526853890825613)
                    ·
                      refine ⟨271081328447570209059605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 722883542526853890825613 271081328447570209059605)
                      ·
                        rfl

theorem cell23_527929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 1, 2, 1, 2, 3].length) (baseStart_527929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_527929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_527929 prefixEnd_527929 := by exact prefixLift 527929
  have htrace : WordTrace (prefixWord ++ tailWord_527929) baseStart_527929 baseEnd_527929 := by
    simpa [prefixWord, tailWord_527929, baseEnd_527929] using wordTrace_append hprefix tailTrace_527929
  have hstable : (prefixWord ++ tailWord_527929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_527929).length < 2 ^ (prefixWord ++ tailWord_527929).sum := by decide
  have hdescent : baseEnd_527929 < baseStart_527929 := by decide
  rcases family_descends (prefixWord ++ tailWord_527929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_527959 : List Nat := [1, 1, 3, 2, 2, 4, 2, 2, 2, 1, 3]
def baseStart_527959 : Nat := 118140960795 + 527959 * 2 ^ 59
def prefixEnd_527959 : Nat := 4983230072969 + 3 ^ 40 * 527959 * 2
def baseEnd_527959 : Nat := 271096732867205091684467

theorem tailTrace_527959 : CollatzResearch.WordTrace tailWord_527959 prefixEnd_527959 271096732867205091684467 := by
  unfold tailWord_527959
  simp only [CollatzResearch.WordTrace]
  refine ⟨19256246694302186063650931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12837497796201457375767287 19256246694302186063650931)
  ·
    refine ⟨28884370041453279095476397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19256246694302186063650931 28884370041453279095476397)
    ·
      refine ⟨10831638765544979660803649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28884370041453279095476397 10831638765544979660803649)
      ·
        refine ⟨8123729074158734745602737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10831638765544979660803649 8123729074158734745602737)
        ·
          refine ⟨6092796805619051059202053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8123729074158734745602737 6092796805619051059202053)
          ·
            refine ⟨1142399401053572073600385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6092796805619051059202053 1142399401053572073600385)
            ·
              refine ⟨856799550790179055200289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1142399401053572073600385 856799550790179055200289)
              ·
                refine ⟨642599663092634291400217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 856799550790179055200289 642599663092634291400217)
                ·
                  refine ⟨481949747319475718550163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 642599663092634291400217 481949747319475718550163)
                  ·
                    refine ⟨722924620979213577825245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 481949747319475718550163 722924620979213577825245)
                    ·
                      refine ⟨271096732867205091684467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 722924620979213577825245 271096732867205091684467)
                      ·
                        rfl

theorem cell23_527959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 2, 2, 2, 1, 3].length) (baseStart_527959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_527959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_527959 prefixEnd_527959 := by exact prefixLift 527959
  have htrace : WordTrace (prefixWord ++ tailWord_527959) baseStart_527959 baseEnd_527959 := by
    simpa [prefixWord, tailWord_527959, baseEnd_527959] using wordTrace_append hprefix tailTrace_527959
  have hstable : (prefixWord ++ tailWord_527959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_527959).length < 2 ^ (prefixWord ++ tailWord_527959).sum := by decide
  have hdescent : baseEnd_527959 < baseStart_527959 := by decide
  rcases family_descends (prefixWord ++ tailWord_527959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528032 : List Nat := [2, 1, 1, 4, 3, 1, 2, 1, 2, 3, 3]
def baseStart_528032 : Nat := 118140960795 + 528032 * 2 ^ 59
def prefixEnd_528032 : Nat := 4983230072969 + 3 ^ 40 * 528032 * 2
def baseEnd_528032 : Nat := 271134216954983306071631

theorem tailTrace_528032 : CollatzResearch.WordTrace tailWord_528032 prefixEnd_528032 271134216954983306071631 := by
  unfold tailWord_528032
  simp only [CollatzResearch.WordTrace]
  refine ⟨9629454611518859765529175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12839272815358479687372233 9629454611518859765529175)
  ·
    refine ⟨14444181917278289648293763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9629454611518859765529175 14444181917278289648293763)
    ·
      refine ⟨21666272875917434472440645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14444181917278289648293763 21666272875917434472440645)
      ·
        refine ⟨4062426164234518963582621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21666272875917434472440645 4062426164234518963582621)
        ·
          refine ⟨1523409811587944611343483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4062426164234518963582621 1523409811587944611343483)
          ·
            refine ⟨2285114717381916917015225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1523409811587944611343483 2285114717381916917015225)
            ·
              refine ⟨1713836038036437687761419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2285114717381916917015225 1713836038036437687761419)
              ·
                refine ⟨2570754057054656531642129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1713836038036437687761419 2570754057054656531642129)
                ·
                  refine ⟨1928065542790992398731597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2570754057054656531642129 1928065542790992398731597)
                  ·
                    refine ⟨723024578546622149524349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1928065542790992398731597 723024578546622149524349)
                    ·
                      refine ⟨271134216954983306071631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 723024578546622149524349 271134216954983306071631)
                      ·
                        rfl

theorem cell23_528032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 1, 2, 3, 3].length) (baseStart_528032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_528032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_528032 prefixEnd_528032 := by exact prefixLift 528032
  have htrace : WordTrace (prefixWord ++ tailWord_528032) baseStart_528032 baseEnd_528032 := by
    simpa [prefixWord, tailWord_528032, baseEnd_528032] using wordTrace_append hprefix tailTrace_528032
  have hstable : (prefixWord ++ tailWord_528032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528032).length < 2 ^ (prefixWord ++ tailWord_528032).sum := by decide
  have hdescent : baseEnd_528032 < baseStart_528032 := by decide
  rcases family_descends (prefixWord ++ tailWord_528032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528033 : List Nat := [1, 2, 3, 3, 2, 2, 3, 1, 2, 2, 2]
def baseStart_528033 : Nat := 118140960795 + 528033 * 2 ^ 59
def prefixEnd_528033 : Nat := 4983230072969 + 3 ^ 40 * 528033 * 2
def baseEnd_528033 : Nat := 271134730435637802159127

theorem tailTrace_528033 : CollatzResearch.WordTrace tailWord_528033 prefixEnd_528033 271134730435637802159127 := by
  unfold tailWord_528033
  simp only [CollatzResearch.WordTrace]
  refine ⟨19258945696034096701844753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12839297130689397801229835 19258945696034096701844753)
  ·
    refine ⟨14444209272025572526383565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19258945696034096701844753 14444209272025572526383565)
    ·
      refine ⟨5416578477009589697393837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14444209272025572526383565 5416578477009589697393837)
      ·
        refine ⟨2031216928878596136522689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5416578477009589697393837 2031216928878596136522689)
        ·
          refine ⟨1523412696658947102392017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2031216928878596136522689 1523412696658947102392017)
          ·
            refine ⟨1142559522494210326794013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1523412696658947102392017 1142559522494210326794013)
            ·
              refine ⟨428459820935328872547755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1142559522494210326794013 428459820935328872547755)
              ·
                refine ⟨642689731402993308821633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 428459820935328872547755 642689731402993308821633)
                ·
                  refine ⟨482017298552244981616225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 642689731402993308821633 482017298552244981616225)
                  ·
                    refine ⟨361512973914183736212169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 482017298552244981616225 361512973914183736212169)
                    ·
                      refine ⟨271134730435637802159127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 361512973914183736212169 271134730435637802159127)
                      ·
                        rfl

theorem cell23_528033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 3, 1, 2, 2, 2].length) (baseStart_528033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_528033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_528033 prefixEnd_528033 := by exact prefixLift 528033
  have htrace : WordTrace (prefixWord ++ tailWord_528033) baseStart_528033 baseEnd_528033 := by
    simpa [prefixWord, tailWord_528033, baseEnd_528033] using wordTrace_append hprefix tailTrace_528033
  have hstable : (prefixWord ++ tailWord_528033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528033).length < 2 ^ (prefixWord ++ tailWord_528033).sum := by decide
  have hdescent : baseEnd_528033 < baseStart_528033 := by decide
  rcases family_descends (prefixWord ++ tailWord_528033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528072 : List Nat := [2, 1, 3, 1, 2, 2, 3, 2, 2, 1, 4]
def baseStart_528072 : Nat := 118140960795 + 528072 * 2 ^ 59
def prefixEnd_528072 : Nat := 4983230072969 + 3 ^ 40 * 528072 * 2
def baseEnd_528072 : Nat := 271154756181163149571447

theorem tailTrace_528072 : CollatzResearch.WordTrace tailWord_528072 prefixEnd_528072 271154756181163149571447 := by
  unfold tailWord_528072
  simp only [CollatzResearch.WordTrace]
  refine ⟨9630184071446403181257235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12840245428595204241676313 9630184071446403181257235)
  ·
    refine ⟨14445276107169604771885853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9630184071446403181257235 14445276107169604771885853)
    ·
      refine ⟨5416978540188601789457195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14445276107169604771885853 5416978540188601789457195)
      ·
        refine ⟨8125467810282902684185793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5416978540188601789457195 8125467810282902684185793)
        ·
          refine ⟨6094100857712177013139345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8125467810282902684185793 6094100857712177013139345)
          ·
            refine ⟨4570575643284132759854509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6094100857712177013139345 4570575643284132759854509)
            ·
              refine ⟨1713965866231549784945441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4570575643284132759854509 1713965866231549784945441)
              ·
                refine ⟨1285474399673662338709081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1713965866231549784945441 1285474399673662338709081)
                ·
                  refine ⟨964105799755246754031811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1285474399673662338709081 964105799755246754031811)
                  ·
                    refine ⟨1446158699632870131047717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 964105799755246754031811 1446158699632870131047717)
                    ·
                      refine ⟨271154756181163149571447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1446158699632870131047717 271154756181163149571447)
                      ·
                        rfl

theorem cell23_528072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3, 2, 2, 1, 4].length) (baseStart_528072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_528072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_528072 prefixEnd_528072 := by exact prefixLift 528072
  have htrace : WordTrace (prefixWord ++ tailWord_528072) baseStart_528072 baseEnd_528072 := by
    simpa [prefixWord, tailWord_528072, baseEnd_528072] using wordTrace_append hprefix tailTrace_528072
  have hstable : (prefixWord ++ tailWord_528072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528072).length < 2 ^ (prefixWord ++ tailWord_528072).sum := by decide
  have hdescent : baseEnd_528072 < baseStart_528072 := by decide
  rcases family_descends (prefixWord ++ tailWord_528072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528109 : List Nat := [1, 5, 1, 2, 1, 2, 1, 3, 2, 2, 3]
def baseStart_528109 : Nat := 118140960795 + 528109 * 2 ^ 59
def prefixEnd_528109 : Nat := 4983230072969 + 3 ^ 40 * 528109 * 2
def baseEnd_528109 : Nat := 271173754965379504808777

theorem tailTrace_528109 : CollatzResearch.WordTrace tailWord_528109 prefixEnd_528109 271173754965379504808777 := by
  unfold tailWord_528109
  simp only [CollatzResearch.WordTrace]
  refine ⟨19261717643758761681611381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12841145095839174454407587 19261717643758761681611381)
  ·
    refine ⟨1805786029102383907651067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 19261717643758761681611381 1805786029102383907651067)
    ·
      refine ⟨2708679043653575861476601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1805786029102383907651067 2708679043653575861476601)
      ·
        refine ⟨2031509282740181896107451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2708679043653575861476601 2031509282740181896107451)
        ·
          refine ⟨3047263924110272844161177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2031509282740181896107451 3047263924110272844161177)
          ·
            refine ⟨2285447943082704633120883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3047263924110272844161177 2285447943082704633120883)
            ·
              refine ⟨3428171914624056949681325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2285447943082704633120883 3428171914624056949681325)
              ·
                refine ⟨1285564467984021356130497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3428171914624056949681325 1285564467984021356130497)
                ·
                  refine ⟨964173350988016017097873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1285564467984021356130497 964173350988016017097873)
                  ·
                    refine ⟨723130013241012012823405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 964173350988016017097873 723130013241012012823405)
                    ·
                      refine ⟨271173754965379504808777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 723130013241012012823405 271173754965379504808777)
                      ·
                        rfl

theorem cell23_528109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 3, 2, 2, 3].length) (baseStart_528109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_528109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_528109 prefixEnd_528109 := by exact prefixLift 528109
  have htrace : WordTrace (prefixWord ++ tailWord_528109) baseStart_528109 baseEnd_528109 := by
    simpa [prefixWord, tailWord_528109, baseEnd_528109] using wordTrace_append hprefix tailTrace_528109
  have hstable : (prefixWord ++ tailWord_528109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528109).length < 2 ^ (prefixWord ++ tailWord_528109).sum := by decide
  have hdescent : baseEnd_528109 < baseStart_528109 := by decide
  rcases family_descends (prefixWord ++ tailWord_528109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528142 : List Nat := [4, 1, 1, 2, 1, 1, 3, 2, 3, 5]
def baseStart_528142 : Nat := 118140960795 + 528142 * 2 ^ 59
def prefixEnd_528142 : Nat := 4983230072969 + 3 ^ 40 * 528142 * 2
def baseEnd_528142 : Nat := 90396899942325958565375

theorem tailTrace_528142 : CollatzResearch.WordTrace tailWord_528142 prefixEnd_528142 90396899942325958565375 := by
  unfold tailWord_528142
  simp only [CollatzResearch.WordTrace]
  refine ⟨2407865156579901039695335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12841947501759472211708453 2407865156579901039695335)
  ·
    refine ⟨3611797734869851559543003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2407865156579901039695335 3611797734869851559543003)
    ·
      refine ⟨5417696602304777339314505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3611797734869851559543003 5417696602304777339314505)
      ·
        refine ⟨4063272451728583004485879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5417696602304777339314505 4063272451728583004485879)
        ·
          refine ⟨6094908677592874506728819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4063272451728583004485879 6094908677592874506728819)
          ·
            refine ⟨9142363016389311760093229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6094908677592874506728819 9142363016389311760093229)
            ·
              refine ⟨3428386131145991910034961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9142363016389311760093229 3428386131145991910034961)
              ·
                refine ⟨2571289598359493932526221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3428386131145991910034961 2571289598359493932526221)
                ·
                  refine ⟨964233599384810224697333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2571289598359493932526221 964233599384810224697333)
                  ·
                    refine ⟨90396899942325958565375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 964233599384810224697333 90396899942325958565375)
                    ·
                      rfl

theorem cell23_528142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 2, 3, 5].length) (baseStart_528142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_528142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_528142 prefixEnd_528142 := by exact prefixLift 528142
  have htrace : WordTrace (prefixWord ++ tailWord_528142) baseStart_528142 baseEnd_528142 := by
    simpa [prefixWord, tailWord_528142, baseEnd_528142] using wordTrace_append hprefix tailTrace_528142
  have hstable : (prefixWord ++ tailWord_528142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528142).length < 2 ^ (prefixWord ++ tailWord_528142).sum := by decide
  have hdescent : baseEnd_528142 < baseStart_528142 := by decide
  rcases family_descends (prefixWord ++ tailWord_528142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528155 : List Nat := [1, 1, 1, 1, 1, 1, 4, 2, 5, 6]
def baseStart_528155 : Nat := 118140960795 + 528155 * 2 ^ 59
def prefixEnd_528155 : Nat := 4983230072969 + 3 ^ 40 * 528155 * 2
def baseEnd_528155 : Nat := 90399125025162108277855

theorem tailTrace_528155 : CollatzResearch.WordTrace tailWord_528155 prefixEnd_528155 90399125025162108277855 := by
  unfold tailWord_528155
  simp only [CollatzResearch.WordTrace]
  refine ⟨19263395401592111537785919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12842263601061407691857279 19263395401592111537785919)
  ·
    refine ⟨28895093102388167306678879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19263395401592111537785919 28895093102388167306678879)
    ·
      refine ⟨43342639653582250960018319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28895093102388167306678879 43342639653582250960018319)
      ·
        refine ⟨65013959480373376440027479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43342639653582250960018319 65013959480373376440027479)
        ·
          refine ⟨97520939220560064660041219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65013959480373376440027479 97520939220560064660041219)
          ·
            refine ⟨146281408830840096990061829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97520939220560064660041219 146281408830840096990061829)
            ·
              refine ⟨27427764155782518185636593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 146281408830840096990061829 27427764155782518185636593)
              ·
                refine ⟨20570823116836888639227445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27427764155782518185636593 20570823116836888639227445)
                ·
                  refine ⟨1928514667203458309927573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20570823116836888639227445 1928514667203458309927573)
                  ·
                    refine ⟨90399125025162108277855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1928514667203458309927573 90399125025162108277855)
                    ·
                      rfl

theorem cell23_528155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2, 5, 6].length) (baseStart_528155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_528155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_528155 prefixEnd_528155 := by exact prefixLift 528155
  have htrace : WordTrace (prefixWord ++ tailWord_528155) baseStart_528155 baseEnd_528155 := by
    simpa [prefixWord, tailWord_528155, baseEnd_528155] using wordTrace_append hprefix tailTrace_528155
  have hstable : (prefixWord ++ tailWord_528155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528155).length < 2 ^ (prefixWord ++ tailWord_528155).sum := by decide
  have hdescent : baseEnd_528155 < baseStart_528155 := by decide
  rcases family_descends (prefixWord ++ tailWord_528155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528172 : List Nat := [2, 2, 1, 1, 1, 5, 2, 2, 1, 6]
def baseStart_528172 : Nat := 118140960795 + 528172 * 2 ^ 59
def prefixEnd_528172 : Nat := 4983230072969 + 3 ^ 40 * 528172 * 2
def baseEnd_528172 : Nat := 90402034748870919440329

theorem tailTrace_528172 : CollatzResearch.WordTrace tailWord_528172 prefixEnd_528172 90402034748870919440329 := by
  unfold tailWord_528172
  simp only [CollatzResearch.WordTrace]
  refine ⟨9632007721265261720577385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12842676961687015627436513 9632007721265261720577385)
  ·
    refine ⟨7224005790948946290433039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9632007721265261720577385 7224005790948946290433039)
    ·
      refine ⟨10836008686423419435649559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7224005790948946290433039 10836008686423419435649559)
      ·
        refine ⟨16254013029635129153474339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10836008686423419435649559 16254013029635129153474339)
        ·
          refine ⟨24381019544452693730211509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16254013029635129153474339 24381019544452693730211509)
          ·
            refine ⟨2285720582292440037207329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 24381019544452693730211509 2285720582292440037207329)
            ·
              refine ⟨1714290436719330027905497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2285720582292440037207329 1714290436719330027905497)
              ·
                refine ⟨1285717827539497520929123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1714290436719330027905497 1285717827539497520929123)
                ·
                  refine ⟨1928576741309246281393685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1285717827539497520929123 1928576741309246281393685)
                  ·
                    refine ⟨90402034748870919440329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1928576741309246281393685 90402034748870919440329)
                    ·
                      rfl

theorem cell23_528172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 6].length) (baseStart_528172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_528172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_528172 prefixEnd_528172 := by exact prefixLift 528172
  have htrace : WordTrace (prefixWord ++ tailWord_528172) baseStart_528172 baseEnd_528172 := by
    simpa [prefixWord, tailWord_528172, baseEnd_528172] using wordTrace_append hprefix tailTrace_528172
  have hstable : (prefixWord ++ tailWord_528172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528172).length < 2 ^ (prefixWord ++ tailWord_528172).sum := by decide
  have hdescent : baseEnd_528172 < baseStart_528172 := by decide
  rcases family_descends (prefixWord ++ tailWord_528172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528209 : List Nat := [1, 2, 2, 1, 5, 1, 3, 1, 1, 2, 4]
def baseStart_528209 : Nat := 118140960795 + 528209 * 2 ^ 59
def prefixEnd_528209 : Nat := 4983230072969 + 3 ^ 40 * 528209 * 2
def baseEnd_528209 : Nat := 271225103030829113558317

theorem tailTrace_528209 : CollatzResearch.WordTrace tailWord_528209 prefixEnd_528209 271225103030829113558317 := by
  unfold tailWord_528209
  simp only [CollatzResearch.WordTrace]
  refine ⟨19265364943396478760251681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12843576628930985840167787 19265364943396478760251681)
  ·
    refine ⟨14449023707547359070188761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19265364943396478760251681 14449023707547359070188761)
    ·
      refine ⟨10836767780660519302641571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14449023707547359070188761 10836767780660519302641571)
      ·
        refine ⟨16255151670990778953962357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10836767780660519302641571 16255151670990778953962357)
        ·
          refine ⟨1523920469155385526933971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16255151670990778953962357 1523920469155385526933971)
          ·
            refine ⟨2285880703733078290400957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1523920469155385526933971 2285880703733078290400957)
            ·
              refine ⟨857205263899904358900359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2285880703733078290400957 857205263899904358900359)
              ·
                refine ⟨1285807895849856538350539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 857205263899904358900359 1285807895849856538350539)
                ·
                  refine ⟨1928711843774784807525809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1285807895849856538350539 1928711843774784807525809)
                  ·
                    refine ⟨1446533882831088605644357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1928711843774784807525809 1446533882831088605644357)
                    ·
                      refine ⟨271225103030829113558317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1446533882831088605644357 271225103030829113558317)
                      ·
                        rfl

theorem cell23_528209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 3, 1, 1, 2, 4].length) (baseStart_528209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_528209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_528209 prefixEnd_528209 := by exact prefixLift 528209
  have htrace : WordTrace (prefixWord ++ tailWord_528209) baseStart_528209 baseEnd_528209 := by
    simpa [prefixWord, tailWord_528209, baseEnd_528209] using wordTrace_append hprefix tailTrace_528209
  have hstable : (prefixWord ++ tailWord_528209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528209).length < 2 ^ (prefixWord ++ tailWord_528209).sum := by decide
  have hdescent : baseEnd_528209 < baseStart_528209 := by decide
  rcases family_descends (prefixWord ++ tailWord_528209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528239 : List Nat := [1, 1, 2, 1, 3, 1, 1, 1, 7, 3, 2]
def baseStart_528239 : Nat := 118140960795 + 528239 * 2 ^ 59
def prefixEnd_528239 : Nat := 4983230072969 + 3 ^ 40 * 528239 * 2
def baseEnd_528239 : Nat := 271240507450463996183179

theorem tailTrace_528239 : CollatzResearch.WordTrace tailWord_528239 prefixEnd_528239 271240507450463996183179 := by
  unfold tailWord_528239
  simp only [CollatzResearch.WordTrace]
  refine ⟨19266459133287793883843771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12844306088858529255895847 19266459133287793883843771)
  ·
    refine ⟨28899688699931690825765657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19266459133287793883843771 28899688699931690825765657)
    ·
      refine ⟨21674766524948768119324243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28899688699931690825765657 21674766524948768119324243)
      ·
        refine ⟨32512149787423152178986365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21674766524948768119324243 32512149787423152178986365)
        ·
          refine ⟨12192056170283682067119887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32512149787423152178986365 12192056170283682067119887)
          ·
            refine ⟨18288084255425523100679831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12192056170283682067119887 18288084255425523100679831)
            ·
              refine ⟨27432126383138284651019747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18288084255425523100679831 27432126383138284651019747)
              ·
                refine ⟨41148189574707426976529621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27432126383138284651019747 41148189574707426976529621)
                ·
                  refine ⟨964410693157205319762413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 41148189574707426976529621 964410693157205319762413)
                  ·
                    refine ⟨361654009933951994910905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 964410693157205319762413 361654009933951994910905)
                    ·
                      refine ⟨271240507450463996183179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 361654009933951994910905 271240507450463996183179)
                      ·
                        rfl

theorem cell23_528239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 7, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 7, 3, 2].length) (baseStart_528239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_528239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_528239 prefixEnd_528239 := by exact prefixLift 528239
  have htrace : WordTrace (prefixWord ++ tailWord_528239) baseStart_528239 baseEnd_528239 := by
    simpa [prefixWord, tailWord_528239, baseEnd_528239] using wordTrace_append hprefix tailTrace_528239
  have hstable : (prefixWord ++ tailWord_528239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528239).length < 2 ^ (prefixWord ++ tailWord_528239).sum := by decide
  have hdescent : baseEnd_528239 < baseStart_528239 := by decide
  rcases family_descends (prefixWord ++ tailWord_528239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528242 : List Nat := [3, 2, 1, 2, 1, 1, 1, 1, 4, 2, 5]
def baseStart_528242 : Nat := 118140960795 + 528242 * 2 ^ 59
def prefixEnd_528242 : Nat := 4983230072969 + 3 ^ 40 * 528242 * 2
def baseEnd_528242 : Nat := 271242047892427484445665

theorem tailTrace_528242 : CollatzResearch.WordTrace tailWord_528242 prefixEnd_528242 271242047892427484445665 := by
  unfold tailWord_528242
  simp only [CollatzResearch.WordTrace]
  refine ⟨4816642138069231349050745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12844379034851283597468653 4816642138069231349050745)
  ·
    refine ⟨3612481603551923511788059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4816642138069231349050745 3612481603551923511788059)
    ·
      refine ⟨5418722405327885267682089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3612481603551923511788059 5418722405327885267682089)
      ·
        refine ⟨4064041803995913950761567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5418722405327885267682089 4064041803995913950761567)
        ·
          refine ⟨6096062705993870926142351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4064041803995913950761567 6096062705993870926142351)
          ·
            refine ⟨9144094058990806389213527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6096062705993870926142351 9144094058990806389213527)
            ·
              refine ⟨13716141088486209583820291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9144094058990806389213527 13716141088486209583820291)
              ·
                refine ⟨20574211632729314375730437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13716141088486209583820291 20574211632729314375730437)
                ·
                  refine ⟨3857664681136746445449457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20574211632729314375730437 3857664681136746445449457)
                  ·
                    refine ⟨2893248510852559834087093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3857664681136746445449457 2893248510852559834087093)
                    ·
                      refine ⟨271242047892427484445665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2893248510852559834087093 271242047892427484445665)
                      ·
                        rfl

theorem cell23_528242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 1, 4, 2, 5].length) (baseStart_528242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_528242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_528242 prefixEnd_528242 := by exact prefixLift 528242
  have htrace : WordTrace (prefixWord ++ tailWord_528242) baseStart_528242 baseEnd_528242 := by
    simpa [prefixWord, tailWord_528242, baseEnd_528242] using wordTrace_append hprefix tailTrace_528242
  have hstable : (prefixWord ++ tailWord_528242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528242).length < 2 ^ (prefixWord ++ tailWord_528242).sum := by decide
  have hdescent : baseEnd_528242 < baseStart_528242 := by decide
  rcases family_descends (prefixWord ++ tailWord_528242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528257 : List Nat := [1, 2, 4, 4, 2, 1, 2, 1, 2, 4]
def baseStart_528257 : Nat := 118140960795 + 528257 * 2 ^ 59
def prefixEnd_528257 : Nat := 4983230072969 + 3 ^ 40 * 528257 * 2
def baseEnd_528257 : Nat := 90416583367414975252699

theorem tailTrace_528257 : CollatzResearch.WordTrace tailWord_528257 prefixEnd_528257 90416583367414975252699 := by
  unfold tailWord_528257
  simp only [CollatzResearch.WordTrace]
  refine ⟨19267115647222582957999025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12844743764815055305332683 19267115647222582957999025)
  ·
    refine ⟨14450336735416937218499269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19267115647222582957999025 14450336735416937218499269)
    ·
      refine ⟨2709438137890675728468613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14450336735416937218499269 2709438137890675728468613)
      ·
        refine ⟨508019650854501699087865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2709438137890675728468613 508019650854501699087865)
        ·
          refine ⟨381014738140876274315899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 508019650854501699087865 381014738140876274315899)
          ·
            refine ⟨571522107211314411473849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 381014738140876274315899 571522107211314411473849)
            ·
              refine ⟨428641580408485808605387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 571522107211314411473849 428641580408485808605387)
              ·
                refine ⟨642962370612728712908081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 428641580408485808605387 642962370612728712908081)
                ·
                  refine ⟨482221777959546534681061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 642962370612728712908081 482221777959546534681061)
                  ·
                    refine ⟨90416583367414975252699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 482221777959546534681061 90416583367414975252699)
                    ·
                      rfl

theorem cell23_528257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 2, 1, 2, 4].length) (baseStart_528257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_528257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_528257 prefixEnd_528257 := by exact prefixLift 528257
  have htrace : WordTrace (prefixWord ++ tailWord_528257) baseStart_528257 baseEnd_528257 := by
    simpa [prefixWord, tailWord_528257, baseEnd_528257] using wordTrace_append hprefix tailTrace_528257
  have hstable : (prefixWord ++ tailWord_528257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528257).length < 2 ^ (prefixWord ++ tailWord_528257).sum := by decide
  have hdescent : baseEnd_528257 < baseStart_528257 := by decide
  rcases family_descends (prefixWord ++ tailWord_528257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528263 : List Nat := [1, 1, 4, 2, 4, 1, 1, 3, 2, 1, 3]
def baseStart_528263 : Nat := 118140960795 + 528263 * 2 ^ 59
def prefixEnd_528263 : Nat := 4983230072969 + 3 ^ 40 * 528263 * 2
def baseEnd_528263 : Nat := 271252830986171902283069

theorem tailTrace_528263 : CollatzResearch.WordTrace tailWord_528263 prefixEnd_528263 271252830986171902283069 := by
  unfold tailWord_528263
  simp only [CollatzResearch.WordTrace]
  refine ⟨19267334485200845982717443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12844889656800563988478295 19267334485200845982717443)
  ·
    refine ⟨28901001727801268974076165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19267334485200845982717443 28901001727801268974076165)
    ·
      refine ⟨5418937823962737932639281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28901001727801268974076165 5418937823962737932639281)
      ·
        refine ⟨4064203367972053449479461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5418937823962737932639281 4064203367972053449479461)
        ·
          refine ⟨762038131494760021777399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4064203367972053449479461 762038131494760021777399)
          ·
            refine ⟨1143057197242140032666099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 762038131494760021777399 1143057197242140032666099)
            ·
              refine ⟨1714585795863210048999149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1143057197242140032666099 1714585795863210048999149)
              ·
                refine ⟨642969673448703768374681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1714585795863210048999149 642969673448703768374681)
                ·
                  refine ⟨482227255086527826281011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 642969673448703768374681 482227255086527826281011)
                  ·
                    refine ⟨723340882629791739421517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 482227255086527826281011 723340882629791739421517)
                    ·
                      refine ⟨271252830986171902283069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 723340882629791739421517 271252830986171902283069)
                      ·
                        rfl

theorem cell23_528263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 1, 3, 2, 1, 3].length) (baseStart_528263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_528263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_528263 prefixEnd_528263 := by exact prefixLift 528263
  have htrace : WordTrace (prefixWord ++ tailWord_528263) baseStart_528263 baseEnd_528263 := by
    simpa [prefixWord, tailWord_528263, baseEnd_528263] using wordTrace_append hprefix tailTrace_528263
  have hstable : (prefixWord ++ tailWord_528263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528263).length < 2 ^ (prefixWord ++ tailWord_528263).sum := by decide
  have hdescent : baseEnd_528263 < baseStart_528263 := by decide
  rcases family_descends (prefixWord ++ tailWord_528263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528272 : List Nat := [2, 1, 1, 1, 1, 1, 2, 6, 2, 1, 5]
def baseStart_528272 : Nat := 118140960795 + 528272 * 2 ^ 59
def prefixEnd_528272 : Nat := 4983230072969 + 3 ^ 40 * 528272 * 2
def baseEnd_528272 : Nat := 271257452312062367070527

theorem tailTrace_528272 : CollatzResearch.WordTrace tailWord_528272 prefixEnd_528272 271257452312062367070527 := by
  unfold tailWord_528272
  simp only [CollatzResearch.WordTrace]
  refine ⟨9633831371084120259897535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12845108494778827013196713 9633831371084120259897535)
  ·
    refine ⟨14450747056626180389846303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9633831371084120259897535 14450747056626180389846303)
    ·
      refine ⟨21676120584939270584769455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14450747056626180389846303 21676120584939270584769455)
      ·
        refine ⟨32514180877408905877154183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21676120584939270584769455 32514180877408905877154183)
        ·
          refine ⟨48771271316113358815731275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32514180877408905877154183 48771271316113358815731275)
          ·
            refine ⟨73156906974170038223596913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48771271316113358815731275 73156906974170038223596913)
            ·
              refine ⟨54867680230627528667697685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73156906974170038223596913 54867680230627528667697685)
              ·
                refine ⟨2571922510810665406298329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 54867680230627528667697685 2571922510810665406298329)
                ·
                  refine ⟨1928941883107999054723747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2571922510810665406298329 1928941883107999054723747)
                  ·
                    refine ⟨2893412824661998582085621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1928941883107999054723747 2893412824661998582085621)
                    ·
                      refine ⟨271257452312062367070527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2893412824661998582085621 271257452312062367070527)
                      ·
                        rfl

theorem cell23_528272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 6, 2, 1, 5].length) (baseStart_528272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_528272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_528272 prefixEnd_528272 := by exact prefixLift 528272
  have htrace : WordTrace (prefixWord ++ tailWord_528272) baseStart_528272 baseEnd_528272 := by
    simpa [prefixWord, tailWord_528272, baseEnd_528272] using wordTrace_append hprefix tailTrace_528272
  have hstable : (prefixWord ++ tailWord_528272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528272).length < 2 ^ (prefixWord ++ tailWord_528272).sum := by decide
  have hdescent : baseEnd_528272 < baseStart_528272 := by decide
  rcases family_descends (prefixWord ++ tailWord_528272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528303 : List Nat := [1, 1, 2, 1, 2, 2, 6, 2, 2, 2, 2]
def baseStart_528303 : Nat := 118140960795 + 528303 * 2 ^ 59
def prefixEnd_528303 : Nat := 4983230072969 + 3 ^ 40 * 528303 * 2
def baseEnd_528303 : Nat := 271273370212351745782885

theorem tailTrace_528303 : CollatzResearch.WordTrace tailWord_528303 prefixEnd_528303 271273370212351745782885 := by
  unfold tailWord_528303
  simp only [CollatzResearch.WordTrace]
  refine ⟨19268793405055932814173563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12845862270037288542782375 19268793405055932814173563)
  ·
    refine ⟨28903190107583899221260345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19268793405055932814173563 28903190107583899221260345)
    ·
      refine ⟨21677392580687924415945259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28903190107583899221260345 21677392580687924415945259)
      ·
        refine ⟨32516088871031886623917889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21677392580687924415945259 32516088871031886623917889)
        ·
          refine ⟨24387066653273914967938417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32516088871031886623917889 24387066653273914967938417)
          ·
            refine ⟨18290299989955436225953813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24387066653273914967938417 18290299989955436225953813)
            ·
              refine ⟨857357812029161073091585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 18290299989955436225953813 857357812029161073091585)
              ·
                refine ⟨643018359021870804818689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 857357812029161073091585 643018359021870804818689)
                ·
                  refine ⟨482263769266403103614017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 643018359021870804818689 482263769266403103614017)
                  ·
                    refine ⟨361697826949802327710513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 482263769266403103614017 361697826949802327710513)
                    ·
                      refine ⟨271273370212351745782885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 361697826949802327710513 271273370212351745782885)
                      ·
                        rfl

theorem cell23_528303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 6, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 6, 2, 2, 2, 2].length) (baseStart_528303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_528303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_528303 prefixEnd_528303 := by exact prefixLift 528303
  have htrace : WordTrace (prefixWord ++ tailWord_528303) baseStart_528303 baseEnd_528303 := by
    simpa [prefixWord, tailWord_528303, baseEnd_528303] using wordTrace_append hprefix tailTrace_528303
  have hstable : (prefixWord ++ tailWord_528303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528303).length < 2 ^ (prefixWord ++ tailWord_528303).sum := by decide
  have hdescent : baseEnd_528303 < baseStart_528303 := by decide
  rcases family_descends (prefixWord ++ tailWord_528303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528319 : List Nat := [1, 1, 2, 2, 2, 1, 5, 1, 2, 3, 3]
def baseStart_528319 : Nat := 118140960795 + 528319 * 2 ^ 59
def prefixEnd_528319 : Nat := 4983230072969 + 3 ^ 40 * 528319 * 2
def baseEnd_528319 : Nat := 271281585902823683182811

theorem tailTrace_528319 : CollatzResearch.WordTrace tailWord_528319 prefixEnd_528319 271281585902823683182811 := by
  unfold tailWord_528319
  simp only [CollatzResearch.WordTrace]
  refine ⟨19269376972997967546756011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12846251315331978364504007 19269376972997967546756011)
  ·
    refine ⟨28904065459496951320134017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19269376972997967546756011 28904065459496951320134017)
    ·
      refine ⟨21678049094622713490100513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28904065459496951320134017 21678049094622713490100513)
      ·
        refine ⟨16258536820967035117575385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21678049094622713490100513 16258536820967035117575385)
        ·
          refine ⟨12193902615725276338181539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16258536820967035117575385 12193902615725276338181539)
          ·
            refine ⟨18290853923587914507272309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12193902615725276338181539 18290853923587914507272309)
            ·
              refine ⟨1714767555336366985056779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18290853923587914507272309 1714767555336366985056779)
              ·
                refine ⟨2572151333004550477585169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1714767555336366985056779 2572151333004550477585169)
                ·
                  refine ⟨1929113499753412858188877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2572151333004550477585169 1929113499753412858188877)
                  ·
                    refine ⟨723417562407529821820829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1929113499753412858188877 723417562407529821820829)
                    ·
                      refine ⟨271281585902823683182811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 723417562407529821820829 271281585902823683182811)
                      ·
                        rfl

theorem cell23_528319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5, 1, 2, 3, 3].length) (baseStart_528319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_528319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_528319 prefixEnd_528319 := by exact prefixLift 528319
  have htrace : WordTrace (prefixWord ++ tailWord_528319) baseStart_528319 baseEnd_528319 := by
    simpa [prefixWord, tailWord_528319, baseEnd_528319] using wordTrace_append hprefix tailTrace_528319
  have hstable : (prefixWord ++ tailWord_528319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528319).length < 2 ^ (prefixWord ++ tailWord_528319).sum := by decide
  have hdescent : baseEnd_528319 < baseStart_528319 := by decide
  rcases family_descends (prefixWord ++ tailWord_528319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
