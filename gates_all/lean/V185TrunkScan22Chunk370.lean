import V185TrunkScan22Chunk369

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_3301204 : List Nat := [2, 4, 1, 1, 3, 2, 3, 1, 2, 3]
def baseStart_3301204 : Nat := 118140960795 + 3301204 * 2 ^ 59
def prefixEnd_3301204 : Nat := 4983230072969 + 3 ^ 40 * 3301204 * 2
def baseEnd_3301204 : Nat := 1130069593696804838578697

theorem tailTrace_3301204 : CollatzResearch.WordTrace tailWord_3301204 prefixEnd_3301204 1130069593696804838578697 := by
  unfold tailWord_3301204
  simp only [CollatzResearch.WordTrace]
  refine ⟨60202400766154591800919333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80269867688206122401225777 60202400766154591800919333)
  ·
    refine ⟨11287950143653985962672375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60202400766154591800919333 11287950143653985962672375)
    ·
      refine ⟨16931925215480978944008563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11287950143653985962672375 16931925215480978944008563)
      ·
        refine ⟨25397887823221468416012845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16931925215480978944008563 25397887823221468416012845)
        ·
          refine ⟨9524207933708050656004817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25397887823221468416012845 9524207933708050656004817)
          ·
            refine ⟨7143155950281037992003613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9524207933708050656004817 7143155950281037992003613)
            ·
              refine ⟨2678683481355389247001355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7143155950281037992003613 2678683481355389247001355)
              ·
                refine ⟨4018025222033083870502033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2678683481355389247001355 4018025222033083870502033)
                ·
                  refine ⟨3013518916524812902876525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4018025222033083870502033 3013518916524812902876525)
                  ·
                    refine ⟨1130069593696804838578697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3013518916524812902876525 1130069593696804838578697)
                    ·
                      rfl

theorem cell22_3301204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 3, 1, 2, 3].length) (baseStart_3301204 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3301204 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3301204 prefixEnd_3301204 := by exact prefixLift 3301204
  have htrace : WordTrace (prefixWord ++ tailWord_3301204) baseStart_3301204 baseEnd_3301204 := by
    simpa [prefixWord, tailWord_3301204, baseEnd_3301204] using wordTrace_append hprefix tailTrace_3301204
  have hstable : (prefixWord ++ tailWord_3301204).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3301204).length < 2 ^ (prefixWord ++ tailWord_3301204).sum := by decide
  have hdescent : baseEnd_3301204 < baseStart_3301204 := by decide
  rcases family_descends (prefixWord ++ tailWord_3301204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3301215 : List Nat := [1, 1, 2, 3, 1, 4, 2, 2, 3, 3]
def baseStart_3301215 : Nat := 118140960795 + 3301215 * 2 ^ 59
def prefixEnd_3301215 : Nat := 4983230072969 + 3 ^ 40 * 3301215 * 2
def baseEnd_3301215 : Nat := 1130073359221604476553663

theorem tailTrace_3301215 : CollatzResearch.WordTrace tailWord_3301215 prefixEnd_3301215 1130073359221604476553663 := by
  unfold tailWord_3301215
  simp only [CollatzResearch.WordTrace]
  refine ⟨120405202735269332480489099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80270135156846221653659399 120405202735269332480489099)
  ·
    refine ⟨180607804102903998720733649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120405202735269332480489099 180607804102903998720733649)
    ·
      refine ⟨135455853077177999040550237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180607804102903998720733649 135455853077177999040550237)
      ·
        refine ⟨50795944903941749640206339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135455853077177999040550237 50795944903941749640206339)
        ·
          refine ⟨76193917355912624460309509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50795944903941749640206339 76193917355912624460309509)
          ·
            refine ⟨14286359504233617086308033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76193917355912624460309509 14286359504233617086308033)
            ·
              refine ⟨10714769628175212814731025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14286359504233617086308033 10714769628175212814731025)
              ·
                refine ⟨8036077221131409611048269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10714769628175212814731025 8036077221131409611048269)
                ·
                  refine ⟨3013528957924278604143101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8036077221131409611048269 3013528957924278604143101)
                  ·
                    refine ⟨1130073359221604476553663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3013528957924278604143101 1130073359221604476553663)
                    ·
                      rfl

theorem cell22_3301215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 2, 2, 3, 3].length) (baseStart_3301215 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3301215 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3301215 prefixEnd_3301215 := by exact prefixLift 3301215
  have htrace : WordTrace (prefixWord ++ tailWord_3301215) baseStart_3301215 baseEnd_3301215 := by
    simpa [prefixWord, tailWord_3301215, baseEnd_3301215] using wordTrace_append hprefix tailTrace_3301215
  have hstable : (prefixWord ++ tailWord_3301215).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3301215).length < 2 ^ (prefixWord ++ tailWord_3301215).sum := by decide
  have hdescent : baseEnd_3301215 < baseStart_3301215 := by decide
  rcases family_descends (prefixWord ++ tailWord_3301215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3301228 : List Nat := [2, 2, 1, 1, 4, 2, 1, 2, 7]
def baseStart_3301228 : Nat := 118140960795 + 3301228 * 2 ^ 59
def prefixEnd_3301228 : Nat := 4983230072969 + 3 ^ 40 * 3301228 * 2
def baseEnd_3301228 : Nat := 376692603129092258659541

theorem tailTrace_3301228 : CollatzResearch.WordTrace tailWord_3301228 prefixEnd_3301228 376692603129092258659541 := by
  unfold tailWord_3301228
  simp only [CollatzResearch.WordTrace]
  refine ⟨60202838442111117850356169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80270451256148157133808225 60202838442111117850356169)
  ·
    refine ⟨45152128831583338387767127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60202838442111117850356169 45152128831583338387767127)
    ·
      refine ⟨67728193247375007581650691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45152128831583338387767127 67728193247375007581650691)
      ·
        refine ⟨101592289871062511372476037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67728193247375007581650691 101592289871062511372476037)
        ·
          refine ⟨19048554350824220882339257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 101592289871062511372476037 19048554350824220882339257)
          ·
            refine ⟨14286415763118165661754443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19048554350824220882339257 14286415763118165661754443)
            ·
              refine ⟨21429623644677248492631665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14286415763118165661754443 21429623644677248492631665)
              ·
                refine ⟨16072217733507936369473749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21429623644677248492631665 16072217733507936369473749)
                ·
                  refine ⟨376692603129092258659541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16072217733507936369473749 376692603129092258659541)
                  ·
                    rfl

theorem cell22_3301228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 7].length) (baseStart_3301228 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3301228 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3301228 prefixEnd_3301228 := by exact prefixLift 3301228
  have htrace : WordTrace (prefixWord ++ tailWord_3301228) baseStart_3301228 baseEnd_3301228 := by
    simpa [prefixWord, tailWord_3301228, baseEnd_3301228] using wordTrace_append hprefix tailTrace_3301228
  have hstable : (prefixWord ++ tailWord_3301228).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3301228).length < 2 ^ (prefixWord ++ tailWord_3301228).sum := by decide
  have hdescent : baseEnd_3301228 < baseStart_3301228 := by decide
  rcases family_descends (prefixWord ++ tailWord_3301228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3301273 : List Nat := [1, 2, 1, 2, 1, 3, 2, 4, 6]
def baseStart_3301273 : Nat := 118140960795 + 3301273 * 2 ^ 59
def prefixEnd_3301273 : Nat := 4983230072969 + 3 ^ 40 * 3301273 * 2
def baseEnd_3301273 : Nat := 376697737935637219534495

theorem tailTrace_3301273 : CollatzResearch.WordTrace tailWord_3301273 prefixEnd_3301273 376697737935637219534495 := by
  unfold tailWord_3301273
  simp only [CollatzResearch.WordTrace]
  refine ⟨120407318169059208386100473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80271545446039472257400315 120407318169059208386100473)
  ·
    refine ⟨90305488626794406289575355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120407318169059208386100473 90305488626794406289575355)
    ·
      refine ⟨135458232940191609434363033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90305488626794406289575355 135458232940191609434363033)
      ·
        refine ⟨101593674705143707075772275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135458232940191609434363033 101593674705143707075772275)
        ·
          refine ⟨152390512057715560613658413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101593674705143707075772275 152390512057715560613658413)
          ·
            refine ⟨57146442021643335230121905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 152390512057715560613658413 57146442021643335230121905)
            ·
              refine ⟨42859831516232501422591429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57146442021643335230121905 42859831516232501422591429)
              ·
                refine ⟨8036218409293594016735893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42859831516232501422591429 8036218409293594016735893)
                ·
                  refine ⟨376697737935637219534495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8036218409293594016735893 376697737935637219534495)
                  ·
                    rfl

theorem cell22_3301273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 4, 6].length) (baseStart_3301273 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3301273 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3301273 prefixEnd_3301273 := by exact prefixLift 3301273
  have htrace : WordTrace (prefixWord ++ tailWord_3301273) baseStart_3301273 baseEnd_3301273 := by
    simpa [prefixWord, tailWord_3301273, baseEnd_3301273] using wordTrace_append hprefix tailTrace_3301273
  have hstable : (prefixWord ++ tailWord_3301273).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3301273).length < 2 ^ (prefixWord ++ tailWord_3301273).sum := by decide
  have hdescent : baseEnd_3301273 < baseStart_3301273 := by decide
  rcases family_descends (prefixWord ++ tailWord_3301273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3301300 : List Nat := [2, 5, 2, 1, 2, 2, 2, 2, 1, 3]
def baseStart_3301300 : Nat := 118140960795 + 3301300 * 2 ^ 59
def prefixEnd_3301300 : Nat := 4983230072969 + 3 ^ 40 * 3301300 * 2
def baseEnd_3301300 : Nat := 1130102456458692588178403

theorem tailTrace_3301300 : CollatzResearch.WordTrace tailWord_3301300 prefixEnd_3301300 1130102456458692588178403 := by
  unfold tailWord_3301300
  simp only [CollatzResearch.WordTrace]
  refine ⟨60204151469980695998666677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80272201959974261331555569 60204151469980695998666677)
  ·
    refine ⟨5644139200310690249875001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 60204151469980695998666677 5644139200310690249875001)
    ·
      refine ⟨4233104400233017687406251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5644139200310690249875001 4233104400233017687406251)
      ·
        refine ⟨6349656600349526531109377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4233104400233017687406251 6349656600349526531109377)
        ·
          refine ⟨4762242450262144898332033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6349656600349526531109377 4762242450262144898332033)
          ·
            refine ⟨3571681837696608673749025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4762242450262144898332033 3571681837696608673749025)
            ·
              refine ⟨2678761378272456505311769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3571681837696608673749025 2678761378272456505311769)
              ·
                refine ⟨2009071033704342378983827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2678761378272456505311769 2009071033704342378983827)
                ·
                  refine ⟨3013606550556513568475741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2009071033704342378983827 3013606550556513568475741)
                  ·
                    refine ⟨1130102456458692588178403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3013606550556513568475741 1130102456458692588178403)
                    ·
                      rfl

theorem cell22_3301300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 2, 2, 1, 3].length) (baseStart_3301300 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3301300 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3301300 prefixEnd_3301300 := by exact prefixLift 3301300
  have htrace : WordTrace (prefixWord ++ tailWord_3301300) baseStart_3301300 baseEnd_3301300 := by
    simpa [prefixWord, tailWord_3301300, baseEnd_3301300] using wordTrace_append hprefix tailTrace_3301300
  have hstable : (prefixWord ++ tailWord_3301300).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3301300).length < 2 ^ (prefixWord ++ tailWord_3301300).sum := by decide
  have hdescent : baseEnd_3301300 < baseStart_3301300 := by decide
  rcases family_descends (prefixWord ++ tailWord_3301300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3301303 : List Nat := [1, 1, 3, 1, 3, 1, 1, 2, 3, 6]
def baseStart_3301303 : Nat := 118140960795 + 3301303 * 2 ^ 59
def prefixEnd_3301303 : Nat := 4983230072969 + 3 ^ 40 * 3301303 * 2
def baseEnd_3301303 : Nat := 1130103483420001580353393

theorem tailTrace_3301303 : CollatzResearch.WordTrace tailWord_3301303 prefixEnd_3301303 1130103483420001580353393 := by
  unfold tailWord_3301303
  simp only [CollatzResearch.WordTrace]
  refine ⟨120408412358950523509692563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80272274905967015673128375 120408412358950523509692563)
  ·
    refine ⟨180612618538425785264538845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120408412358950523509692563 180612618538425785264538845)
    ·
      refine ⟨67729731951909669474202067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 180612618538425785264538845 67729731951909669474202067)
      ·
        refine ⟨101594597927864504211303101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67729731951909669474202067 101594597927864504211303101)
        ·
          refine ⟨38097974222949189079238663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101594597927864504211303101 38097974222949189079238663)
          ·
            refine ⟨57146961334423783618857995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38097974222949189079238663 57146961334423783618857995)
            ·
              refine ⟨85720442001635675428286993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57146961334423783618857995 85720442001635675428286993)
              ·
                refine ⟨64290331501226756571215245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85720442001635675428286993 64290331501226756571215245)
                ·
                  refine ⟨24108874312960033714205717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64290331501226756571215245 24108874312960033714205717)
                  ·
                    refine ⟨1130103483420001580353393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24108874312960033714205717 1130103483420001580353393)
                    ·
                      rfl

theorem cell22_3301303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 2, 3, 6].length) (baseStart_3301303 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3301303 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3301303 prefixEnd_3301303 := by exact prefixLift 3301303
  have htrace : WordTrace (prefixWord ++ tailWord_3301303) baseStart_3301303 baseEnd_3301303 := by
    simpa [prefixWord, tailWord_3301303, baseEnd_3301303] using wordTrace_append hprefix tailTrace_3301303
  have hstable : (prefixWord ++ tailWord_3301303).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3301303).length < 2 ^ (prefixWord ++ tailWord_3301303).sum := by decide
  have hdescent : baseEnd_3301303 < baseStart_3301303 := by decide
  rcases family_descends (prefixWord ++ tailWord_3301303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3301322 : List Nat := [3, 1, 2, 1, 2, 1, 4, 3, 2, 3]
def baseStart_3301322 : Nat := 118140960795 + 3301322 * 2 ^ 59
def prefixEnd_3301322 : Nat := 4983230072969 + 3 ^ 40 * 3301322 * 2
def baseEnd_3301322 : Nat := 1130109987508291864128335

theorem tailTrace_3301322 : CollatzResearch.WordTrace tailWord_3301322 prefixEnd_3301322 1130109987508291864128335 := by
  unfold tailWord_3301322
  simp only [CollatzResearch.WordTrace]
  refine ⟨30102276336470422438658555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80272736897254459836422813 30102276336470422438658555)
  ·
    refine ⟨45153414504705633657987833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30102276336470422438658555 45153414504705633657987833)
    ·
      refine ⟨33865060878529225243490875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45153414504705633657987833 33865060878529225243490875)
      ·
        refine ⟨50797591317793837865236313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33865060878529225243490875 50797591317793837865236313)
        ·
          refine ⟨38098193488345378398927235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50797591317793837865236313 38098193488345378398927235)
          ·
            refine ⟨57147290232518067598390853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38098193488345378398927235 57147290232518067598390853)
            ·
              refine ⟨10715116918597137674698285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57147290232518067598390853 10715116918597137674698285)
              ·
                refine ⟨4018168844473926628011857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10715116918597137674698285 4018168844473926628011857)
                ·
                  refine ⟨3013626633355444971008893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4018168844473926628011857 3013626633355444971008893)
                  ·
                    refine ⟨1130109987508291864128335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3013626633355444971008893 1130109987508291864128335)
                    ·
                      rfl

theorem cell22_3301322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4, 3, 2, 3].length) (baseStart_3301322 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3301322 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3301322 prefixEnd_3301322 := by exact prefixLift 3301322
  have htrace : WordTrace (prefixWord ++ tailWord_3301322) baseStart_3301322 baseEnd_3301322 := by
    simpa [prefixWord, tailWord_3301322, baseEnd_3301322] using wordTrace_append hprefix tailTrace_3301322
  have hstable : (prefixWord ++ tailWord_3301322).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3301322).length < 2 ^ (prefixWord ++ tailWord_3301322).sum := by decide
  have hdescent : baseEnd_3301322 < baseStart_3301322 := by decide
  rcases family_descends (prefixWord ++ tailWord_3301322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3301335 : List Nat := [1, 1, 3, 2, 1, 1, 7, 6]
def baseStart_3301335 : Nat := 118140960795 + 3301335 * 2 ^ 59
def prefixEnd_3301335 : Nat := 4983230072969 + 3 ^ 40 * 3301335 * 2
def baseEnd_3301335 : Nat := 125568270852662684839255

theorem tailTrace_3301335 : CollatzResearch.WordTrace tailWord_3301335 prefixEnd_3301335 125568270852662684839255 := by
  unfold tailWord_3301335
  simp only [CollatzResearch.WordTrace]
  refine ⟨120409579494834592974857459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80273052996556395316571639 120409579494834592974857459)
  ·
    refine ⟨180614369242251889462286189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120409579494834592974857459 180614369242251889462286189)
    ·
      refine ⟨67730388465844458548357321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 180614369242251889462286189 67730388465844458548357321)
      ·
        refine ⟨50797791349383343911267991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67730388465844458548357321 50797791349383343911267991)
        ·
          refine ⟨76196687024075015866901987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50797791349383343911267991 76196687024075015866901987)
          ·
            refine ⟨114295030536112523800352981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76196687024075015866901987 114295030536112523800352981)
            ·
              refine ⟨2678789778190137276570773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 114295030536112523800352981 2678789778190137276570773)
              ·
                refine ⟨125568270852662684839255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2678789778190137276570773 125568270852662684839255)
                ·
                  rfl

theorem cell22_3301335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 7, 6].length) (baseStart_3301335 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3301335 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3301335 prefixEnd_3301335 := by exact prefixLift 3301335
  have htrace : WordTrace (prefixWord ++ tailWord_3301335) baseStart_3301335 baseEnd_3301335 := by
    simpa [prefixWord, tailWord_3301335, baseEnd_3301335] using wordTrace_append hprefix tailTrace_3301335
  have hstable : (prefixWord ++ tailWord_3301335).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3301335).length < 2 ^ (prefixWord ++ tailWord_3301335).sum := by decide
  have hdescent : baseEnd_3301335 < baseStart_3301335 := by decide
  rcases family_descends (prefixWord ++ tailWord_3301335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3301418 : List Nat := [3, 1, 4, 1, 2, 2, 3, 2, 1, 3]
def baseStart_3301418 : Nat := 118140960795 + 3301418 * 2 ^ 59
def prefixEnd_3301418 : Nat := 4983230072969 + 3 ^ 40 * 3301418 * 2
def baseEnd_3301418 : Nat := 1130142850270179613728041

theorem tailTrace_3301418 : CollatzResearch.WordTrace tailWord_3301418 prefixEnd_3301418 1130142850270179613728041 := by
  unfold tailWord_3301418
  simp only [CollatzResearch.WordTrace]
  refine ⟨30103151688383474537532227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80275071169022598766752605 30103151688383474537532227)
  ·
    refine ⟨45154727532575211806298341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30103151688383474537532227 45154727532575211806298341)
    ·
      refine ⟨8466511412357852213680939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45154727532575211806298341 8466511412357852213680939)
      ·
        refine ⟨12699767118536778320521409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8466511412357852213680939 12699767118536778320521409)
        ·
          refine ⟨9524825338902583740391057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12699767118536778320521409 9524825338902583740391057)
          ·
            refine ⟨7143619004176937805293293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9524825338902583740391057 7143619004176937805293293)
            ·
              refine ⟨2678857126566351676984985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7143619004176937805293293 2678857126566351676984985)
              ·
                refine ⟨2009142844924763757738739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2678857126566351676984985 2009142844924763757738739)
                ·
                  refine ⟨3013714267387145636608109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2009142844924763757738739 3013714267387145636608109)
                  ·
                    refine ⟨1130142850270179613728041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3013714267387145636608109 1130142850270179613728041)
                    ·
                      rfl

theorem cell22_3301418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 3, 2, 1, 3].length) (baseStart_3301418 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3301418 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3301418 prefixEnd_3301418 := by exact prefixLift 3301418
  have htrace : WordTrace (prefixWord ++ tailWord_3301418) baseStart_3301418 baseEnd_3301418 := by
    simpa [prefixWord, tailWord_3301418, baseEnd_3301418] using wordTrace_append hprefix tailTrace_3301418
  have hstable : (prefixWord ++ tailWord_3301418).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3301418).length < 2 ^ (prefixWord ++ tailWord_3301418).sum := by decide
  have hdescent : baseEnd_3301418 < baseStart_3301418 := by decide
  rcases family_descends (prefixWord ++ tailWord_3301418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3301455 : List Nat := [1, 1, 2, 1, 1, 2, 2, 2, 6, 4]
def baseStart_3301455 : Nat := 118140960795 + 3301455 * 2 ^ 59
def prefixEnd_3301455 : Nat := 4983230072969 + 3 ^ 40 * 3301455 * 2
def baseEnd_3301455 : Nat := 1130155516126323850552927

theorem tailTrace_3301455 : CollatzResearch.WordTrace tailWord_3301455 prefixEnd_3301455 1130155516126323850552927 := by
  unfold tailWord_3301455
  simp only [CollatzResearch.WordTrace]
  refine ⟨120413956254399853469225819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80275970836266568979483879 120413956254399853469225819)
  ·
    refine ⟨180620934381599780203838729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120413956254399853469225819 180620934381599780203838729)
    ·
      refine ⟨135465700786199835152879047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180620934381599780203838729 135465700786199835152879047)
      ·
        refine ⟨203198551179299752729318571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135465700786199835152879047 203198551179299752729318571)
        ·
          refine ⟨304797826768949629093977857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203198551179299752729318571 304797826768949629093977857)
          ·
            refine ⟨228598370076712221820483393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 304797826768949629093977857 228598370076712221820483393)
            ·
              refine ⟨171448777557534166365362545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 228598370076712221820483393 171448777557534166365362545)
              ·
                refine ⟨128586583168150624774021909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 171448777557534166365362545 128586583168150624774021909)
                ·
                  refine ⟨6027496086007060536282277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 128586583168150624774021909 6027496086007060536282277)
                  ·
                    refine ⟨1130155516126323850552927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6027496086007060536282277 1130155516126323850552927)
                    ·
                      rfl

theorem cell22_3301455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 2, 6, 4].length) (baseStart_3301455 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3301455 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3301455 prefixEnd_3301455 := by exact prefixLift 3301455
  have htrace : WordTrace (prefixWord ++ tailWord_3301455) baseStart_3301455 baseEnd_3301455 := by
    simpa [prefixWord, tailWord_3301455, baseEnd_3301455] using wordTrace_append hprefix tailTrace_3301455
  have hstable : (prefixWord ++ tailWord_3301455).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3301455).length < 2 ^ (prefixWord ++ tailWord_3301455).sum := by decide
  have hdescent : baseEnd_3301455 < baseStart_3301455 := by decide
  rcases family_descends (prefixWord ++ tailWord_3301455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3301472 : List Nat := [2, 1, 1, 3, 2, 3, 2, 2, 2, 4]
def baseStart_3301472 : Nat := 118140960795 + 3301472 * 2 ^ 59
def prefixEnd_3301472 : Nat := 4983230072969 + 3 ^ 40 * 3301472 * 2
def baseEnd_3301472 : Nat := 1130161335573741472877875

theorem tailTrace_3301472 : CollatzResearch.WordTrace tailWord_3301472 prefixEnd_3301472 1130161335573741472877875 := by
  unfold tailWord_3301472
  simp only [CollatzResearch.WordTrace]
  refine ⟨60207288147669132686297335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80276384196892176915063113 60207288147669132686297335)
  ·
    refine ⟨90310932221503699029446003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60207288147669132686297335 90310932221503699029446003)
    ·
      refine ⟨135466398332255548544169005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90310932221503699029446003 135466398332255548544169005)
      ·
        refine ⟨50799899374595830704063377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135466398332255548544169005 50799899374595830704063377)
        ·
          refine ⟨38099924530946873028047533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50799899374595830704063377 38099924530946873028047533)
          ·
            refine ⟨14287471699105077385517825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38099924530946873028047533 14287471699105077385517825)
            ·
              refine ⟨10715603774328808039138369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14287471699105077385517825 10715603774328808039138369)
              ·
                refine ⟨8036702830746606029353777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10715603774328808039138369 8036702830746606029353777)
                ·
                  refine ⟨6027527123059954522015333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8036702830746606029353777 6027527123059954522015333)
                  ·
                    refine ⟨1130161335573741472877875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6027527123059954522015333 1130161335573741472877875)
                    ·
                      rfl

theorem cell22_3301472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 2, 2, 2, 4].length) (baseStart_3301472 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3301472 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3301472 prefixEnd_3301472 := by exact prefixLift 3301472
  have htrace : WordTrace (prefixWord ++ tailWord_3301472) baseStart_3301472 baseEnd_3301472 := by
    simpa [prefixWord, tailWord_3301472, baseEnd_3301472] using wordTrace_append hprefix tailTrace_3301472
  have hstable : (prefixWord ++ tailWord_3301472).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3301472).length < 2 ^ (prefixWord ++ tailWord_3301472).sum := by decide
  have hdescent : baseEnd_3301472 < baseStart_3301472 := by decide
  rcases family_descends (prefixWord ++ tailWord_3301472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3301487 : List Nat := [1, 1, 2, 1, 3, 6, 1, 7]
def baseStart_3301487 : Nat := 118140960795 + 3301487 * 2 ^ 59
def prefixEnd_3301487 : Nat := 4983230072969 + 3 ^ 40 * 3301487 * 2
def baseEnd_3301487 : Nat := 125574052264476270416981

theorem tailTrace_3301487 : CollatzResearch.WordTrace tailWord_3301487 prefixEnd_3301487 125574052264476270416981 := by
  unfold tailWord_3301487
  simp only [CollatzResearch.WordTrace]
  refine ⟨120415123390283922934390715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80276748926855948622927143 120415123390283922934390715)
  ·
    refine ⟨180622685085425884401586073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120415123390283922934390715 180622685085425884401586073)
    ·
      refine ⟨135467013814069413301189555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180622685085425884401586073 135467013814069413301189555)
      ·
        refine ⟨203200520721104119951784333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135467013814069413301189555 203200520721104119951784333)
        ·
          refine ⟨76200195270414044981919125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 203200520721104119951784333 76200195270414044981919125)
          ·
            refine ⟨3571884153300658358527459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 76200195270414044981919125 3571884153300658358527459)
            ·
              refine ⟨5357826229950987537791189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3571884153300658358527459 5357826229950987537791189)
              ·
                refine ⟨125574052264476270416981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5357826229950987537791189 125574052264476270416981)
                ·
                  rfl

theorem cell22_3301487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 1, 7].length) (baseStart_3301487 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3301487 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3301487 prefixEnd_3301487 := by exact prefixLift 3301487
  have htrace : WordTrace (prefixWord ++ tailWord_3301487) baseStart_3301487 baseEnd_3301487 := by
    simpa [prefixWord, tailWord_3301487, baseEnd_3301487] using wordTrace_append hprefix tailTrace_3301487
  have hstable : (prefixWord ++ tailWord_3301487).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3301487).length < 2 ^ (prefixWord ++ tailWord_3301487).sum := by decide
  have hdescent : baseEnd_3301487 < baseStart_3301487 := by decide
  rcases family_descends (prefixWord ++ tailWord_3301487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3301532 : List Nat := [2, 2, 3, 2, 1, 1, 3, 1, 7]
def baseStart_3301532 : Nat := 118140960795 + 3301532 * 2 ^ 59
def prefixEnd_3301532 : Nat := 4983230072969 + 3 ^ 40 * 3301532 * 2
def baseEnd_3301532 : Nat := 376727291599973772125897

theorem tailTrace_3301532 : CollatzResearch.WordTrace tailWord_3301532 prefixEnd_3301532 376727291599973772125897 := by
  unfold tailWord_3301532
  simp only [CollatzResearch.WordTrace]
  refine ⟨60208382337560447809889425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80277843116747263746519233 60208382337560447809889425)
  ·
    refine ⟨45156286753170335857417069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60208382337560447809889425 45156286753170335857417069)
    ·
      refine ⟨16933607532438875946531401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45156286753170335857417069 16933607532438875946531401)
      ·
        refine ⟨12700205649329156959898551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16933607532438875946531401 12700205649329156959898551)
        ·
          refine ⟨19050308473993735439847827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12700205649329156959898551 19050308473993735439847827)
          ·
            refine ⟨28575462710990603159771741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19050308473993735439847827 28575462710990603159771741)
            ·
              refine ⟨10715798516621476184914403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28575462710990603159771741 10715798516621476184914403)
              ·
                refine ⟨16073697774932214277371605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10715798516621476184914403 16073697774932214277371605)
                ·
                  refine ⟨376727291599973772125897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16073697774932214277371605 376727291599973772125897)
                  ·
                    rfl

theorem cell22_3301532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 3, 1, 7].length) (baseStart_3301532 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3301532 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3301532 prefixEnd_3301532 := by exact prefixLift 3301532
  have htrace : WordTrace (prefixWord ++ tailWord_3301532) baseStart_3301532 baseEnd_3301532 := by
    simpa [prefixWord, tailWord_3301532, baseEnd_3301532] using wordTrace_append hprefix tailTrace_3301532
  have hstable : (prefixWord ++ tailWord_3301532).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3301532).length < 2 ^ (prefixWord ++ tailWord_3301532).sum := by decide
  have hdescent : baseEnd_3301532 < baseStart_3301532 := by decide
  rcases family_descends (prefixWord ++ tailWord_3301532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3301536 : List Nat := [2, 1, 1, 4, 2, 2, 2, 4, 1, 3]
def baseStart_3301536 : Nat := 118140960795 + 3301536 * 2 ^ 59
def prefixEnd_3301536 : Nat := 4983230072969 + 3 ^ 40 * 3301536 * 2
def baseEnd_3301536 : Nat := 1130183244081666639277679

theorem tailTrace_3301536 : CollatzResearch.WordTrace tailWord_3301536 prefixEnd_3301536 1130183244081666639277679 := by
  unfold tailWord_3301536
  simp only [CollatzResearch.WordTrace]
  refine ⟨60208455283553202151462231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80277940378070936201949641 60208455283553202151462231)
  ·
    refine ⟨90312682925329803227193347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60208455283553202151462231 90312682925329803227193347)
    ·
      refine ⟨135469024387994704840790021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90312682925329803227193347 135469024387994704840790021)
      ·
        refine ⟨25400442072749007157648129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 135469024387994704840790021 25400442072749007157648129)
        ·
          refine ⟨19050331554561755368236097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25400442072749007157648129 19050331554561755368236097)
          ·
            refine ⟨14287748665921316526177073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19050331554561755368236097 14287748665921316526177073)
            ·
              refine ⟨10715811499440987394632805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14287748665921316526177073 10715811499440987394632805)
              ·
                refine ⟨2009214656145185136493651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10715811499440987394632805 2009214656145185136493651)
                ·
                  refine ⟨3013821984217777704740477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2009214656145185136493651 3013821984217777704740477)
                  ·
                    refine ⟨1130183244081666639277679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3013821984217777704740477 1130183244081666639277679)
                    ·
                      rfl

theorem cell22_3301536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2, 4, 1, 3].length) (baseStart_3301536 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3301536 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3301536 prefixEnd_3301536 := by exact prefixLift 3301536
  have htrace : WordTrace (prefixWord ++ tailWord_3301536) baseStart_3301536 baseEnd_3301536 := by
    simpa [prefixWord, tailWord_3301536, baseEnd_3301536] using wordTrace_append hprefix tailTrace_3301536
  have hstable : (prefixWord ++ tailWord_3301536).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3301536).length < 2 ^ (prefixWord ++ tailWord_3301536).sum := by decide
  have hdescent : baseEnd_3301536 < baseStart_3301536 := by decide
  rcases family_descends (prefixWord ++ tailWord_3301536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3301562 : List Nat := [3, 1, 1, 1, 2, 2, 2, 3, 3, 4]
def baseStart_3301562 : Nat := 118140960795 + 3301562 * 2 ^ 59
def prefixEnd_3301562 : Nat := 4983230072969 + 3 ^ 40 * 3301562 * 2
def baseEnd_3301562 : Nat := 1130192144413011238127599

theorem tailTrace_3301562 : CollatzResearch.WordTrace tailWord_3301562 prefixEnd_3301562 1130192144413011238127599 := by
  unfold tailWord_3301562
  simp only [CollatzResearch.WordTrace]
  refine ⟨30104464716253052685842735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80278572576674807162247293 30104464716253052685842735)
  ·
    refine ⟨45156697074379579028764103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30104464716253052685842735 45156697074379579028764103)
    ·
      refine ⟨67735045611569368543146155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45156697074379579028764103 67735045611569368543146155)
      ·
        refine ⟨101602568417354052814719233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67735045611569368543146155 101602568417354052814719233)
        ·
          refine ⟨76201926313015539611039425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101602568417354052814719233 76201926313015539611039425)
          ·
            refine ⟨57151444734761654708279569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76201926313015539611039425 57151444734761654708279569)
            ·
              refine ⟨42863583551071241031209677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57151444734761654708279569 42863583551071241031209677)
              ·
                refine ⟨16073843831651715386703629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42863583551071241031209677 16073843831651715386703629)
                ·
                  refine ⟨6027691436869393270013861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16073843831651715386703629 6027691436869393270013861)
                  ·
                    refine ⟨1130192144413011238127599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6027691436869393270013861 1130192144413011238127599)
                    ·
                      rfl

theorem cell22_3301562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 3, 3, 4].length) (baseStart_3301562 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3301562 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3301562 prefixEnd_3301562 := by exact prefixLift 3301562
  have htrace : WordTrace (prefixWord ++ tailWord_3301562) baseStart_3301562 baseEnd_3301562 := by
    simpa [prefixWord, tailWord_3301562, baseEnd_3301562] using wordTrace_append hprefix tailTrace_3301562
  have hstable : (prefixWord ++ tailWord_3301562).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3301562).length < 2 ^ (prefixWord ++ tailWord_3301562).sum := by decide
  have hdescent : baseEnd_3301562 < baseStart_3301562 := by decide
  rcases family_descends (prefixWord ++ tailWord_3301562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3301594 : List Nat := [3, 1, 1, 2, 2, 1, 2, 6, 4]
def baseStart_3301594 : Nat := 118140960795 + 3301594 * 2 ^ 59
def prefixEnd_3301594 : Nat := 4983230072969 + 3 ^ 40 * 3301594 * 2
def baseEnd_3301594 : Nat := 376734366222324607109167

theorem tailTrace_3301594 : CollatzResearch.WordTrace tailWord_3301594 prefixEnd_3301594 376734366222324607109167 := by
  unfold tailWord_3301594
  simp only [CollatzResearch.WordTrace]
  refine ⟨30104756500224070052133959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80279350667264186805690557 30104756500224070052133959)
  ·
    refine ⟨45157134750336105078200939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30104756500224070052133959 45157134750336105078200939)
    ·
      refine ⟨67735702125504157617301409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45157134750336105078200939 67735702125504157617301409)
      ·
        refine ⟨50801776594128118212976057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67735702125504157617301409 50801776594128118212976057)
        ·
          refine ⟨38101332445596088659732043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50801776594128118212976057 38101332445596088659732043)
          ·
            refine ⟨57151998668394132989598065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38101332445596088659732043 57151998668394132989598065)
            ·
              refine ⟨42863999001295599742198549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57151998668394132989598065 42863999001295599742198549)
              ·
                refine ⟨2009249953185731237915557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 42863999001295599742198549 2009249953185731237915557)
                ·
                  refine ⟨376734366222324607109167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2009249953185731237915557 376734366222324607109167)
                  ·
                    rfl

theorem cell22_3301594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 6, 4].length) (baseStart_3301594 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3301594 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3301594 prefixEnd_3301594 := by exact prefixLift 3301594
  have htrace : WordTrace (prefixWord ++ tailWord_3301594) baseStart_3301594 baseEnd_3301594 := by
    simpa [prefixWord, tailWord_3301594, baseEnd_3301594] using wordTrace_append hprefix tailTrace_3301594
  have hstable : (prefixWord ++ tailWord_3301594).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3301594).length < 2 ^ (prefixWord ++ tailWord_3301594).sum := by decide
  have hdescent : baseEnd_3301594 < baseStart_3301594 := by decide
  rcases family_descends (prefixWord ++ tailWord_3301594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3301609 : List Nat := [1, 2, 1, 1, 1, 2, 2, 7, 2, 3]
def baseStart_3301609 : Nat := 118140960795 + 3301609 * 2 ^ 59
def prefixEnd_3301609 : Nat := 4983230072969 + 3 ^ 40 * 3301609 * 2
def baseEnd_3301609 : Nat := 1130208233473518782202455

theorem tailTrace_3301609 : CollatzResearch.WordTrace tailWord_3301609 prefixEnd_3301609 1130208233473518782202455 := by
  unfold tailWord_3301609
  simp only [CollatzResearch.WordTrace]
  refine ⟨120419573095841937770331881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80279715397227958513554587 120419573095841937770331881)
  ·
    refine ⟨90314679821881453327748911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120419573095841937770331881 90314679821881453327748911)
    ·
      refine ⟨135472019732822179991623367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90314679821881453327748911 135472019732822179991623367)
      ·
        refine ⟨203208029599233269987435051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135472019732822179991623367 203208029599233269987435051)
        ·
          refine ⟨304812044398849904981152577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203208029599233269987435051 304812044398849904981152577)
          ·
            refine ⟨228609033299137428735864433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 304812044398849904981152577 228609033299137428735864433)
            ·
              refine ⟨171456774974353071551898325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 228609033299137428735864433 171456774974353071551898325)
              ·
                refine ⟨4018518163461400114497617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 171456774974353071551898325 4018518163461400114497617)
                ·
                  refine ⟨3013888622596050085873213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4018518163461400114497617 3013888622596050085873213)
                  ·
                    refine ⟨1130208233473518782202455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3013888622596050085873213 1130208233473518782202455)
                    ·
                      rfl

theorem cell22_3301609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 7, 2, 3].length) (baseStart_3301609 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3301609 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3301609 prefixEnd_3301609 := by exact prefixLift 3301609
  have htrace : WordTrace (prefixWord ++ tailWord_3301609) baseStart_3301609 baseEnd_3301609 := by
    simpa [prefixWord, tailWord_3301609, baseEnd_3301609] using wordTrace_append hprefix tailTrace_3301609
  have hstable : (prefixWord ++ tailWord_3301609).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3301609).length < 2 ^ (prefixWord ++ tailWord_3301609).sum := by decide
  have hdescent : baseEnd_3301609 < baseStart_3301609 := by decide
  rcases family_descends (prefixWord ++ tailWord_3301609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3301613 : List Nat := [1, 5, 1, 2, 3, 2, 1, 2, 1, 4]
def baseStart_3301613 : Nat := 118140960795 + 3301613 * 2 ^ 59
def prefixEnd_3301613 : Nat := 4983230072969 + 3 ^ 40 * 3301613 * 2
def baseEnd_3301613 : Nat := 1130209602755264105102443

theorem tailTrace_3301613 : CollatzResearch.WordTrace tailWord_3301613 prefixEnd_3301613 1130209602755264105102443 := by
  unfold tailWord_3301613
  simp only [CollatzResearch.WordTrace]
  refine ⟨120419718987827446453477493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80279812658551630968984995 120419718987827446453477493)
  ·
    refine ⟨11289348655108823105013515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 120419718987827446453477493 11289348655108823105013515)
    ·
      refine ⟨16934022982663234657520273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11289348655108823105013515 16934022982663234657520273)
      ·
        refine ⟨12700517236997425993140205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16934022982663234657520273 12700517236997425993140205)
        ·
          refine ⟨4762693963874034747427577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12700517236997425993140205 4762693963874034747427577)
          ·
            refine ⟨3572020472905526060570683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4762693963874034747427577 3572020472905526060570683)
            ·
              refine ⟨5358030709358289090856025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3572020472905526060570683 5358030709358289090856025)
              ·
                refine ⟨4018523032018716818142019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5358030709358289090856025 4018523032018716818142019)
                ·
                  refine ⟨6027784548028075227213029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4018523032018716818142019 6027784548028075227213029)
                  ·
                    refine ⟨1130209602755264105102443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6027784548028075227213029 1130209602755264105102443)
                    ·
                      rfl

theorem cell22_3301613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 1, 2, 1, 4].length) (baseStart_3301613 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3301613 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3301613 prefixEnd_3301613 := by exact prefixLift 3301613
  have htrace : WordTrace (prefixWord ++ tailWord_3301613) baseStart_3301613 baseEnd_3301613 := by
    simpa [prefixWord, tailWord_3301613, baseEnd_3301613] using wordTrace_append hprefix tailTrace_3301613
  have hstable : (prefixWord ++ tailWord_3301613).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3301613).length < 2 ^ (prefixWord ++ tailWord_3301613).sum := by decide
  have hdescent : baseEnd_3301613 < baseStart_3301613 := by decide
  rcases family_descends (prefixWord ++ tailWord_3301613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3301639 : List Nat := [1, 1, 4, 5, 1, 10]
def baseStart_3301639 : Nat := 118140960795 + 3301639 * 2 ^ 59
def prefixEnd_3301639 : Nat := 4983230072969 + 3 ^ 40 * 3301639 * 2
def baseEnd_3301639 : Nat := 13953314852921095110523

theorem tailTrace_3301639 : CollatzResearch.WordTrace tailWord_3301639 prefixEnd_3301639 13953314852921095110523 := by
  unfold tailWord_3301639
  simp only [CollatzResearch.WordTrace]
  refine ⟨120420667285733252893923971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80280444857155501929282647 120420667285733252893923971)
  ·
    refine ⟨180631000928599879340885957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120420667285733252893923971 180631000928599879340885957)
    ·
      refine ⟨33868312674112477376416117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 180631000928599879340885957 33868312674112477376416117)
      ·
        refine ⟨3175154313198044754039011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 33868312674112477376416117 3175154313198044754039011)
        ·
          refine ⟨4762731469797067131058517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3175154313198044754039011 4762731469797067131058517)
          ·
            refine ⟨13953314852921095110523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4762731469797067131058517 13953314852921095110523)
            ·
              rfl

theorem cell22_3301639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 10].length) (baseStart_3301639 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3301639 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3301639 prefixEnd_3301639 := by exact prefixLift 3301639
  have htrace : WordTrace (prefixWord ++ tailWord_3301639) baseStart_3301639 baseEnd_3301639 := by
    simpa [prefixWord, tailWord_3301639, baseEnd_3301639] using wordTrace_append hprefix tailTrace_3301639
  have hstable : (prefixWord ++ tailWord_3301639).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3301639).length < 2 ^ (prefixWord ++ tailWord_3301639).sum := by decide
  have hdescent : baseEnd_3301639 < baseStart_3301639 := by decide
  rcases family_descends (prefixWord ++ tailWord_3301639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3301714 : List Nat := [3, 2, 2, 1, 1, 1, 2, 1, 5, 4]
def baseStart_3301714 : Nat := 118140960795 + 3301714 * 2 ^ 59
def prefixEnd_3301714 : Nat := 4983230072969 + 3 ^ 40 * 3301714 * 2
def baseEnd_3301714 : Nat := 1130244177119333508327133

theorem tailTrace_3301714 : CollatzResearch.WordTrace tailWord_3301714 prefixEnd_3301714 1130244177119333508327133 := by
  unfold tailWord_3301714
  simp only [CollatzResearch.WordTrace]
  refine ⟨30105850690115385175726049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80282268506974360468602797 30105850690115385175726049)
  ·
    refine ⟨22579388017586538881794537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30105850690115385175726049 22579388017586538881794537)
    ·
      refine ⟨16934541013189904161345903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22579388017586538881794537 16934541013189904161345903)
      ·
        refine ⟨25401811519784856242018855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16934541013189904161345903 25401811519784856242018855)
        ·
          refine ⟨38102717279677284363028283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25401811519784856242018855 38102717279677284363028283)
          ·
            refine ⟨57154075919515926544542425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38102717279677284363028283 57154075919515926544542425)
            ·
              refine ⟨42865556939636944908406819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57154075919515926544542425 42865556939636944908406819)
              ·
                refine ⟨64298335409455417362610229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42865556939636944908406819 64298335409455417362610229)
                ·
                  refine ⟨6027968944636445377744709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 64298335409455417362610229 6027968944636445377744709)
                  ·
                    refine ⟨1130244177119333508327133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6027968944636445377744709 1130244177119333508327133)
                    ·
                      rfl

theorem cell22_3301714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 1, 5, 4].length) (baseStart_3301714 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3301714 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3301714 prefixEnd_3301714 := by exact prefixLift 3301714
  have htrace : WordTrace (prefixWord ++ tailWord_3301714) baseStart_3301714 baseEnd_3301714 := by
    simpa [prefixWord, tailWord_3301714, baseEnd_3301714] using wordTrace_append hprefix tailTrace_3301714
  have hstable : (prefixWord ++ tailWord_3301714).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3301714).length < 2 ^ (prefixWord ++ tailWord_3301714).sum := by decide
  have hdescent : baseEnd_3301714 < baseStart_3301714 := by decide
  rcases family_descends (prefixWord ++ tailWord_3301714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3301731 : List Nat := [1, 1, 1, 5, 2, 1, 4, 2, 1, 4]
def baseStart_3301731 : Nat := 118140960795 + 3301731 * 2 ^ 59
def prefixEnd_3301731 : Nat := 4983230072969 + 3 ^ 40 * 3301731 * 2
def baseEnd_3301731 : Nat := 1130249996566751130652081

theorem tailTrace_3301731 : CollatzResearch.WordTrace tailWord_3301731 prefixEnd_3301731 1130249996566751130652081 := by
  unfold tailWord_3301731
  simp only [CollatzResearch.WordTrace]
  refine ⟨120424022801399952606273047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80282681867599968404182031 120424022801399952606273047)
  ·
    refine ⟨180636034202099928909409571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120424022801399952606273047 180636034202099928909409571)
    ·
      refine ⟨270954051303149893364114357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180636034202099928909409571 270954051303149893364114357)
      ·
        refine ⟨25401942309670302502885721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 270954051303149893364114357 25401942309670302502885721)
        ·
          refine ⟨19051456732252726877164291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25401942309670302502885721 19051456732252726877164291)
          ·
            refine ⟨28577185098379090315746437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19051456732252726877164291 28577185098379090315746437)
            ·
              refine ⟨5358222205946079434202457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28577185098379090315746437 5358222205946079434202457)
              ·
                refine ⟨4018666654459559575651843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5358222205946079434202457 4018666654459559575651843)
                ·
                  refine ⟨6027999981689339363477765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4018666654459559575651843 6027999981689339363477765)
                  ·
                    refine ⟨1130249996566751130652081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6027999981689339363477765 1130249996566751130652081)
                    ·
                      rfl

theorem cell22_3301731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 4, 2, 1, 4].length) (baseStart_3301731 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3301731 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3301731 prefixEnd_3301731 := by exact prefixLift 3301731
  have htrace : WordTrace (prefixWord ++ tailWord_3301731) baseStart_3301731 baseEnd_3301731 := by
    simpa [prefixWord, tailWord_3301731, baseEnd_3301731] using wordTrace_append hprefix tailTrace_3301731
  have hstable : (prefixWord ++ tailWord_3301731).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3301731).length < 2 ^ (prefixWord ++ tailWord_3301731).sum := by decide
  have hdescent : baseEnd_3301731 < baseStart_3301731 := by decide
  rcases family_descends (prefixWord ++ tailWord_3301731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3301759 : List Nat := [1, 1, 2, 2, 1, 1, 2, 6, 2, 4]
def baseStart_3301759 : Nat := 118140960795 + 3301759 * 2 ^ 59
def prefixEnd_3301759 : Nat := 4983230072969 + 3 ^ 40 * 3301759 * 2
def baseEnd_3301759 : Nat := 1130259581538968390951995

theorem tailTrace_3301759 : CollatzResearch.WordTrace tailWord_3301759 prefixEnd_3301759 1130259581538968390951995 := by
  unfold tailWord_3301759
  simp only [CollatzResearch.WordTrace]
  refine ⟨120425044045298513388292331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80283362696865675592194887 120425044045298513388292331)
  ·
    refine ⟨180637566067947770082438497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120425044045298513388292331 180637566067947770082438497)
    ·
      refine ⟨135478174550960827561828873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180637566067947770082438497 135478174550960827561828873)
      ·
        refine ⟨101608630913220620671371655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135478174550960827561828873 101608630913220620671371655)
        ·
          refine ⟨152412946369830931007057483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101608630913220620671371655 152412946369830931007057483)
          ·
            refine ⟨228619419554746396510586225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152412946369830931007057483 228619419554746396510586225)
            ·
              refine ⟨171464564666059797382939669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 228619419554746396510586225 171464564666059797382939669)
              ·
                refine ⟨8037401468721553002325297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 171464564666059797382939669 8037401468721553002325297)
                ·
                  refine ⟨6028051101541164751743973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8037401468721553002325297 6028051101541164751743973)
                  ·
                    refine ⟨1130259581538968390951995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6028051101541164751743973 1130259581538968390951995)
                    ·
                      rfl

theorem cell22_3301759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 6, 2, 4].length) (baseStart_3301759 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3301759 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3301759 prefixEnd_3301759 := by exact prefixLift 3301759
  have htrace : WordTrace (prefixWord ++ tailWord_3301759) baseStart_3301759 baseEnd_3301759 := by
    simpa [prefixWord, tailWord_3301759, baseEnd_3301759] using wordTrace_append hprefix tailTrace_3301759
  have hstable : (prefixWord ++ tailWord_3301759).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3301759).length < 2 ^ (prefixWord ++ tailWord_3301759).sum := by decide
  have hdescent : baseEnd_3301759 < baseStart_3301759 := by decide
  rcases family_descends (prefixWord ++ tailWord_3301759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3301763 : List Nat := [1, 1, 1, 3, 7, 1, 1, 1, 6]
def baseStart_3301763 : Nat := 118140960795 + 3301763 * 2 ^ 59
def prefixEnd_3301763 : Nat := 4983230072969 + 3 ^ 40 * 3301763 * 2
def baseEnd_3301763 : Nat := 376753650273571237950661

theorem tailTrace_3301763 : CollatzResearch.WordTrace tailWord_3301763 prefixEnd_3301763 376753650273571237950661 := by
  unfold tailWord_3301763
  simp only [CollatzResearch.WordTrace]
  refine ⟨120425189937284022071437943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80283459958189348047625295 120425189937284022071437943)
  ·
    refine ⟨180637784905926033107156915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120425189937284022071437943 180637784905926033107156915)
    ·
      refine ⟨270956677358889049660735373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180637784905926033107156915 270956677358889049660735373)
      ·
        refine ⟨101608754009583393622775765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 270956677358889049660735373 101608754009583393622775765)
        ·
          refine ⟨2381455172099610788033807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 101608754009583393622775765 2381455172099610788033807)
          ·
            refine ⟨3572182758149416182050711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2381455172099610788033807 3572182758149416182050711)
            ·
              refine ⟨5358274137224124273076067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3572182758149416182050711 5358274137224124273076067)
              ·
                refine ⟨8037411205836186409614101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5358274137224124273076067 8037411205836186409614101)
                ·
                  refine ⟨376753650273571237950661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8037411205836186409614101 376753650273571237950661)
                  ·
                    rfl

theorem cell22_3301763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 1, 1, 6].length) (baseStart_3301763 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3301763 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3301763 prefixEnd_3301763 := by exact prefixLift 3301763
  have htrace : WordTrace (prefixWord ++ tailWord_3301763) baseStart_3301763 baseEnd_3301763 := by
    simpa [prefixWord, tailWord_3301763, baseEnd_3301763] using wordTrace_append hprefix tailTrace_3301763
  have hstable : (prefixWord ++ tailWord_3301763).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3301763).length < 2 ^ (prefixWord ++ tailWord_3301763).sum := by decide
  have hdescent : baseEnd_3301763 < baseStart_3301763 := by decide
  rcases family_descends (prefixWord ++ tailWord_3301763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3301782 : List Nat := [5, 3, 1, 2, 1, 1, 1, 1, 3, 4]
def baseStart_3301782 : Nat := 118140960795 + 3301782 * 2 ^ 59
def prefixEnd_3301782 : Nat := 4983230072969 + 3 ^ 40 * 3301782 * 2
def baseEnd_3301782 : Nat := 1130267454909003997626925

theorem tailTrace_3301782 : CollatzResearch.WordTrace tailWord_3301782 prefixEnd_3301782 1130267454909003997626925 := by
  unfold tailWord_3301782
  simp only [CollatzResearch.WordTrace]
  refine ⟨7526617682763449269773725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 80283921949476792210919733 7526617682763449269773725)
  ·
    refine ⟨2822481631036293476165147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7526617682763449269773725 2822481631036293476165147)
    ·
      refine ⟨4233722446554440214247721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2822481631036293476165147 4233722446554440214247721)
      ·
        refine ⟨3175291834915830160685791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4233722446554440214247721 3175291834915830160685791)
        ·
          refine ⟨4762937752373745241028687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3175291834915830160685791 4762937752373745241028687)
          ·
            refine ⟨7144406628560617861543031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4762937752373745241028687 7144406628560617861543031)
            ·
              refine ⟨10716609942840926792314547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7144406628560617861543031 10716609942840926792314547)
              ·
                refine ⟨16074914914261390188471821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10716609942840926792314547 16074914914261390188471821)
                ·
                  refine ⟨6028093092848021320676933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16074914914261390188471821 6028093092848021320676933)
                  ·
                    refine ⟨1130267454909003997626925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6028093092848021320676933 1130267454909003997626925)
                    ·
                      rfl

theorem cell22_3301782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 1, 1, 3, 4].length) (baseStart_3301782 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3301782 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3301782 prefixEnd_3301782 := by exact prefixLift 3301782
  have htrace : WordTrace (prefixWord ++ tailWord_3301782) baseStart_3301782 baseEnd_3301782 := by
    simpa [prefixWord, tailWord_3301782, baseEnd_3301782] using wordTrace_append hprefix tailTrace_3301782
  have hstable : (prefixWord ++ tailWord_3301782).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3301782).length < 2 ^ (prefixWord ++ tailWord_3301782).sum := by decide
  have hdescent : baseEnd_3301782 < baseStart_3301782 := by decide
  rcases family_descends (prefixWord ++ tailWord_3301782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3301928 : List Nat := [2, 1, 5, 2, 1, 1, 1, 1, 4, 4]
def baseStart_3301928 : Nat := 118140960795 + 3301928 * 2 ^ 59
def prefixEnd_3301928 : Nat := 4983230072969 + 3 ^ 40 * 3301928 * 2
def baseEnd_3301928 : Nat := 1130317433692708283476477

theorem tailTrace_3301928 : CollatzResearch.WordTrace tailWord_3301928 prefixEnd_3301928 1130317433692708283476477 := by
  unfold tailWord_3301928
  simp only [CollatzResearch.WordTrace]
  refine ⟨60215603990843127625597219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80287471987790836834129625 60215603990843127625597219)
  ·
    refine ⟨90323405986264691438395829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60215603990843127625597219 90323405986264691438395829)
    ·
      refine ⟨8467819311212314822349609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 90323405986264691438395829 8467819311212314822349609)
      ·
        refine ⟨6350864483409236116762207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8467819311212314822349609 6350864483409236116762207)
        ·
          refine ⟨9526296725113854175143311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6350864483409236116762207 9526296725113854175143311)
          ·
            refine ⟨14289445087670781262714967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9526296725113854175143311 14289445087670781262714967)
            ·
              refine ⟨21434167631506171894072451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14289445087670781262714967 21434167631506171894072451)
              ·
                refine ⟨32151251447259257841108677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21434167631506171894072451 32151251447259257841108677)
                ·
                  refine ⟨6028359646361110845207877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32151251447259257841108677 6028359646361110845207877)
                  ·
                    refine ⟨1130317433692708283476477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6028359646361110845207877 1130317433692708283476477)
                    ·
                      rfl

theorem cell22_3301928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 1, 4, 4].length) (baseStart_3301928 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3301928 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3301928 prefixEnd_3301928 := by exact prefixLift 3301928
  have htrace : WordTrace (prefixWord ++ tailWord_3301928) baseStart_3301928 baseEnd_3301928 := by
    simpa [prefixWord, tailWord_3301928, baseEnd_3301928] using wordTrace_append hprefix tailTrace_3301928
  have hstable : (prefixWord ++ tailWord_3301928).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3301928).length < 2 ^ (prefixWord ++ tailWord_3301928).sum := by decide
  have hdescent : baseEnd_3301928 < baseStart_3301928 := by decide
  rcases family_descends (prefixWord ++ tailWord_3301928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3301975 : List Nat := [1, 1, 3, 2, 2, 2, 2, 5, 1, 3]
def baseStart_3301975 : Nat := 118140960795 + 3301975 * 2 ^ 59
def prefixEnd_3301975 : Nat := 4983230072969 + 3 ^ 40 * 3301975 * 2
def baseEnd_3301975 : Nat := 1130333522753215827551333

theorem tailTrace_3301975 : CollatzResearch.WordTrace tailWord_3301975 prefixEnd_3301975 1130333522753215827551333 := by
  unfold tailWord_3301975
  simp only [CollatzResearch.WordTrace]
  refine ⟨120432922212515982278155379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80288614808343988185436919 120432922212515982278155379)
  ·
    refine ⟨180649383318773973417233069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120432922212515982278155379 180649383318773973417233069)
    ·
      refine ⟨67743518744540240031462401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 180649383318773973417233069 67743518744540240031462401)
      ·
        refine ⟨50807639058405180023596801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67743518744540240031462401 50807639058405180023596801)
        ·
          refine ⟨38105729293803885017697601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50807639058405180023596801 38105729293803885017697601)
          ·
            refine ⟨28579296970352913763273201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38105729293803885017697601 28579296970352913763273201)
            ·
              refine ⟨21434472727764685322454901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28579296970352913763273201 21434472727764685322454901)
              ·
                refine ⟨2009481818227939248980147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21434472727764685322454901 2009481818227939248980147)
                ·
                  refine ⟨3014222727341908873470221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2009481818227939248980147 3014222727341908873470221)
                  ·
                    refine ⟨1130333522753215827551333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3014222727341908873470221 1130333522753215827551333)
                    ·
                      rfl

theorem cell22_3301975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 5, 1, 3].length) (baseStart_3301975 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3301975 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3301975 prefixEnd_3301975 := by exact prefixLift 3301975
  have htrace : WordTrace (prefixWord ++ tailWord_3301975) baseStart_3301975 baseEnd_3301975 := by
    simpa [prefixWord, tailWord_3301975, baseEnd_3301975] using wordTrace_append hprefix tailTrace_3301975
  have hstable : (prefixWord ++ tailWord_3301975).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3301975).length < 2 ^ (prefixWord ++ tailWord_3301975).sum := by decide
  have hdescent : baseEnd_3301975 < baseStart_3301975 := by decide
  rcases family_descends (prefixWord ++ tailWord_3301975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3301988 : List Nat := [2, 3, 1, 1, 2, 2, 4, 2, 5]
def baseStart_3301988 : Nat := 118140960795 + 3301988 * 2 ^ 59
def prefixEnd_3301988 : Nat := 4983230072969 + 3 ^ 40 * 3301988 * 2
def baseEnd_3301988 : Nat := 376779324306296042325431

theorem tailTrace_3301988 : CollatzResearch.WordTrace tailWord_3301988 prefixEnd_3301988 376779324306296042325431 := by
  unfold tailWord_3301988
  simp only [CollatzResearch.WordTrace]
  refine ⟨60216698180734442749189309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80288930907645923665585745 60216698180734442749189309)
  ·
    refine ⟨22581261817775416030945991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60216698180734442749189309 22581261817775416030945991)
    ·
      refine ⟨33871892726663124046418987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22581261817775416030945991 33871892726663124046418987)
      ·
        refine ⟨50807839089994686069628481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33871892726663124046418987 50807839089994686069628481)
        ·
          refine ⟨38105879317496014552221361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50807839089994686069628481 38105879317496014552221361)
          ·
            refine ⟨28579409488122010914166021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38105879317496014552221361 28579409488122010914166021)
            ·
              refine ⟨5358639279022877046406129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28579409488122010914166021 5358639279022877046406129)
              ·
                refine ⟨4018979459267157784804597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5358639279022877046406129 4018979459267157784804597)
                ·
                  refine ⟨376779324306296042325431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4018979459267157784804597 376779324306296042325431)
                  ·
                    rfl

theorem cell22_3301988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 4, 2, 5].length) (baseStart_3301988 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3301988 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3301988 prefixEnd_3301988 := by exact prefixLift 3301988
  have htrace : WordTrace (prefixWord ++ tailWord_3301988) baseStart_3301988 baseEnd_3301988 := by
    simpa [prefixWord, tailWord_3301988, baseEnd_3301988] using wordTrace_append hprefix tailTrace_3301988
  have hstable : (prefixWord ++ tailWord_3301988).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3301988).length < 2 ^ (prefixWord ++ tailWord_3301988).sum := by decide
  have hdescent : baseEnd_3301988 < baseStart_3301988 := by decide
  rcases family_descends (prefixWord ++ tailWord_3301988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3302016 : List Nat := [2, 1, 1, 2, 1, 5, 1, 1, 8]
def baseStart_3302016 : Nat := 118140960795 + 3302016 * 2 ^ 59
def prefixEnd_3302016 : Nat := 4983230072969 + 3 ^ 40 * 3302016 * 2
def baseEnd_3302016 : Nat := 376782519297035129092069

theorem tailTrace_3302016 : CollatzResearch.WordTrace tailWord_3302016 prefixEnd_3302016 376782519297035129092069 := by
  unfold tailWord_3302016
  simp only [CollatzResearch.WordTrace]
  refine ⟨60217208802683723140198951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80289611736911630853598601 60217208802683723140198951)
  ·
    refine ⟨90325813204025584710298427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60217208802683723140198951 90325813204025584710298427)
    ·
      refine ⟨135488719806038377065447641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90325813204025584710298427 135488719806038377065447641)
      ·
        refine ⟨101616539854528782799085731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135488719806038377065447641 101616539854528782799085731)
        ·
          refine ⟨152424809781793174198628597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101616539854528782799085731 152424809781793174198628597)
          ·
            refine ⟨14289825917043110081121431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 152424809781793174198628597 14289825917043110081121431)
            ·
              refine ⟨21434738875564665121682147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14289825917043110081121431 21434738875564665121682147)
              ·
                refine ⟨32152108313346997682523221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21434738875564665121682147 32152108313346997682523221)
                ·
                  refine ⟨376782519297035129092069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 32152108313346997682523221 376782519297035129092069)
                  ·
                    rfl

theorem cell22_3302016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 1, 8].length) (baseStart_3302016 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3302016 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3302016 prefixEnd_3302016 := by exact prefixLift 3302016
  have htrace : WordTrace (prefixWord ++ tailWord_3302016) baseStart_3302016 baseEnd_3302016 := by
    simpa [prefixWord, tailWord_3302016, baseEnd_3302016] using wordTrace_append hprefix tailTrace_3302016
  have hstable : (prefixWord ++ tailWord_3302016).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3302016).length < 2 ^ (prefixWord ++ tailWord_3302016).sum := by decide
  have hdescent : baseEnd_3302016 < baseStart_3302016 := by decide
  rcases family_descends (prefixWord ++ tailWord_3302016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3302078 : List Nat := [4, 2, 1, 1, 2, 1, 3, 8]
def baseStart_3302078 : Nat := 118140960795 + 3302078 * 2 ^ 59
def prefixEnd_3302078 : Nat := 4983230072969 + 3 ^ 40 * 3302078 * 2
def baseEnd_3302078 : Nat := 125596531306461988025113

theorem tailTrace_3302078 : CollatzResearch.WordTrace tailWord_3302078 prefixEnd_3302078 125596531306461988025113 := by
  unfold tailWord_3302078
  simp only [CollatzResearch.WordTrace]
  refine ⟨15054584866392853858644361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80291119287428553912769925 15054584866392853858644361)
  ·
    refine ⟨11290938649794640393983271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15054584866392853858644361 11290938649794640393983271)
    ·
      refine ⟨16936407974691960590974907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11290938649794640393983271 16936407974691960590974907)
      ·
        refine ⟨25404611962037940886462361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16936407974691960590974907 25404611962037940886462361)
        ·
          refine ⟨19053458971528455664846771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25404611962037940886462361 19053458971528455664846771)
          ·
            refine ⟨28580188457292683497270157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19053458971528455664846771 28580188457292683497270157)
            ·
              refine ⟨10717570671484756311476309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28580188457292683497270157 10717570671484756311476309)
              ·
                refine ⟨125596531306461988025113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10717570671484756311476309 125596531306461988025113)
                ·
                  rfl

theorem cell22_3302078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 3, 8].length) (baseStart_3302078 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3302078 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3302078 prefixEnd_3302078 := by exact prefixLift 3302078
  have htrace : WordTrace (prefixWord ++ tailWord_3302078) baseStart_3302078 baseEnd_3302078 := by
    simpa [prefixWord, tailWord_3302078, baseEnd_3302078] using wordTrace_append hprefix tailTrace_3302078
  have hstable : (prefixWord ++ tailWord_3302078).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3302078).length < 2 ^ (prefixWord ++ tailWord_3302078).sum := by decide
  have hdescent : baseEnd_3302078 < baseStart_3302078 := by decide
  rcases family_descends (prefixWord ++ tailWord_3302078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3302091 : List Nat := [1, 1, 1, 1, 3, 2, 1, 1, 3, 8]
def baseStart_3302091 : Nat := 118140960795 + 3302091 * 2 ^ 59
def prefixEnd_3302091 : Nat := 4983230072969 + 3 ^ 40 * 3302091 * 2
def baseEnd_3302091 : Nat := 1130373231923830191650977

theorem tailTrace_3302091 : CollatzResearch.WordTrace tailWord_3302091 prefixEnd_3302091 1130373231923830191650977 := by
  unfold tailWord_3302091
  simp only [CollatzResearch.WordTrace]
  refine ⟨120437153080095734089378127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80291435386730489392918751 120437153080095734089378127)
  ·
    refine ⟨180655729620143601134067191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120437153080095734089378127 180655729620143601134067191)
    ·
      refine ⟨270983594430215401701100787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180655729620143601134067191 270983594430215401701100787)
      ·
        refine ⟨406475391645323102551651181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 270983594430215401701100787 406475391645323102551651181)
        ·
          refine ⟨152428271866996163456869193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 406475391645323102551651181 152428271866996163456869193)
          ·
            refine ⟨114321203900247122592651895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 152428271866996163456869193 114321203900247122592651895)
            ·
              refine ⟨171481805850370683888977843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114321203900247122592651895 171481805850370683888977843)
              ·
                refine ⟨257222708775556025833466765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 171481805850370683888977843 257222708775556025833466765)
                ·
                  refine ⟨96458515790833509687550037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 257222708775556025833466765 96458515790833509687550037)
                  ·
                    refine ⟨1130373231923830191650977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 96458515790833509687550037 1130373231923830191650977)
                    ·
                      rfl

theorem cell22_3302091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 3, 8].length) (baseStart_3302091 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3302091 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3302091 prefixEnd_3302091 := by exact prefixLift 3302091
  have htrace : WordTrace (prefixWord ++ tailWord_3302091) baseStart_3302091 baseEnd_3302091 := by
    simpa [prefixWord, tailWord_3302091, baseEnd_3302091] using wordTrace_append hprefix tailTrace_3302091
  have hstable : (prefixWord ++ tailWord_3302091).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3302091).length < 2 ^ (prefixWord ++ tailWord_3302091).sum := by decide
  have hdescent : baseEnd_3302091 < baseStart_3302091 := by decide
  rcases family_descends (prefixWord ++ tailWord_3302091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3302168 : List Nat := [2, 1, 2, 3, 1, 1, 1, 5, 6]
def baseStart_3302168 : Nat := 118140960795 + 3302168 * 2 ^ 59
def prefixEnd_3302168 : Nat := 4983230072969 + 3 ^ 40 * 3302168 * 2
def baseEnd_3302168 : Nat := 376799863532475885825247

theorem tailTrace_3302168 : CollatzResearch.WordTrace tailWord_3302168 prefixEnd_3302168 376799863532475885825247 := by
  unfold tailWord_3302168
  simp only [CollatzResearch.WordTrace]
  refine ⟨60219980750408388119965579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80293307667211184159954105 60219980750408388119965579)
  ·
    refine ⟨90329971125612582179948369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60219980750408388119965579 90329971125612582179948369)
    ·
      refine ⟨67747478344209436634961277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90329971125612582179948369 67747478344209436634961277)
      ·
        refine ⟨25405304379078538738110479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67747478344209436634961277 25405304379078538738110479)
        ·
          refine ⟨38107956568617808107165719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25405304379078538738110479 38107956568617808107165719)
          ·
            refine ⟨57161934852926712160748579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38107956568617808107165719 57161934852926712160748579)
            ·
              refine ⟨85742902279390068241122869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57161934852926712160748579 85742902279390068241122869)
              ·
                refine ⟨8038397088692818897605269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 85742902279390068241122869 8038397088692818897605269)
                ·
                  refine ⟨376799863532475885825247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8038397088692818897605269 376799863532475885825247)
                  ·
                    rfl

theorem cell22_3302168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 5, 6].length) (baseStart_3302168 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3302168 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3302168 prefixEnd_3302168 := by exact prefixLift 3302168
  have htrace : WordTrace (prefixWord ++ tailWord_3302168) baseStart_3302168 baseEnd_3302168 := by
    simpa [prefixWord, tailWord_3302168, baseEnd_3302168] using wordTrace_append hprefix tailTrace_3302168
  have hstable : (prefixWord ++ tailWord_3302168).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3302168).length < 2 ^ (prefixWord ++ tailWord_3302168).sum := by decide
  have hdescent : baseEnd_3302168 < baseStart_3302168 := by decide
  rcases family_descends (prefixWord ++ tailWord_3302168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3302200 : List Nat := [2, 1, 2, 1, 3, 2, 2, 2, 4, 3]
def baseStart_3302200 : Nat := 118140960795 + 3302200 * 2 ^ 59
def prefixEnd_3302200 : Nat := 4983230072969 + 3 ^ 40 * 3302200 * 2
def baseEnd_3302200 : Nat := 1130410544851390240675643

theorem tailTrace_3302200 : CollatzResearch.WordTrace tailWord_3302200 prefixEnd_3302200 1130410544851390240675643 := by
  unfold tailWord_3302200
  simp only [CollatzResearch.WordTrace]
  refine ⟨60220564318350422852548027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80294085757800563803397369 60220564318350422852548027)
  ·
    refine ⟨90330846477525634278822041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60220564318350422852548027 90330846477525634278822041)
    ·
      refine ⟨67748134858144225709116531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90330846477525634278822041 67748134858144225709116531)
      ·
        refine ⟨101622202287216338563674797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67748134858144225709116531 101622202287216338563674797)
        ·
          refine ⟨38108325857706126961378049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101622202287216338563674797 38108325857706126961378049)
          ·
            refine ⟨28581244393279595221033537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38108325857706126961378049 28581244393279595221033537)
            ·
              refine ⟨21435933294959696415775153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28581244393279595221033537 21435933294959696415775153)
              ·
                refine ⟨16076949971219772311831365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21435933294959696415775153 16076949971219772311831365)
                ·
                  refine ⟨3014428119603707308468381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16076949971219772311831365 3014428119603707308468381)
                  ·
                    refine ⟨1130410544851390240675643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3014428119603707308468381 1130410544851390240675643)
                    ·
                      rfl

theorem cell22_3302200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 2, 4, 3].length) (baseStart_3302200 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3302200 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3302200 prefixEnd_3302200 := by exact prefixLift 3302200
  have htrace : WordTrace (prefixWord ++ tailWord_3302200) baseStart_3302200 baseEnd_3302200 := by
    simpa [prefixWord, tailWord_3302200, baseEnd_3302200] using wordTrace_append hprefix tailTrace_3302200
  have hstable : (prefixWord ++ tailWord_3302200).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3302200).length < 2 ^ (prefixWord ++ tailWord_3302200).sum := by decide
  have hdescent : baseEnd_3302200 < baseStart_3302200 := by decide
  rcases family_descends (prefixWord ++ tailWord_3302200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3302217 : List Nat := [1, 2, 1, 1, 2, 5, 3, 2, 2, 3]
def baseStart_3302217 : Nat := 118140960795 + 3302217 * 2 ^ 59
def prefixEnd_3302217 : Nat := 4983230072969 + 3 ^ 40 * 3302217 * 2
def baseEnd_3302217 : Nat := 1130416364298807863000591

theorem tailTrace_3302217 : CollatzResearch.WordTrace tailWord_3302217 prefixEnd_3302217 1130416364298807863000591 := by
  unfold tailWord_3302217
  simp only [CollatzResearch.WordTrace]
  refine ⟨120441748677639257608464905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80294499118426171738976603 120441748677639257608464905)
  ·
    refine ⟨90331311508229443206348679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120441748677639257608464905 90331311508229443206348679)
    ·
      refine ⟨135496967262344164809523019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90331311508229443206348679 135496967262344164809523019)
      ·
        refine ⟨203245450893516247214284529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135496967262344164809523019 203245450893516247214284529)
        ·
          refine ⟨152434088170137185410713397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 203245450893516247214284529 152434088170137185410713397)
          ·
            refine ⟨14290695765950361132254381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 152434088170137185410713397 14290695765950361132254381)
            ·
              refine ⟨5359010912231385424595393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14290695765950361132254381 5359010912231385424595393)
              ·
                refine ⟨4019258184173539068446545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5359010912231385424595393 4019258184173539068446545)
                ·
                  refine ⟨3014443638130154301334909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4019258184173539068446545 3014443638130154301334909)
                  ·
                    refine ⟨1130416364298807863000591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3014443638130154301334909 1130416364298807863000591)
                    ·
                      rfl

theorem cell22_3302217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 3, 2, 2, 3].length) (baseStart_3302217 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3302217 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3302217 prefixEnd_3302217 := by exact prefixLift 3302217
  have htrace : WordTrace (prefixWord ++ tailWord_3302217) baseStart_3302217 baseEnd_3302217 := by
    simpa [prefixWord, tailWord_3302217, baseEnd_3302217] using wordTrace_append hprefix tailTrace_3302217
  have hstable : (prefixWord ++ tailWord_3302217).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3302217).length < 2 ^ (prefixWord ++ tailWord_3302217).sum := by decide
  have hdescent : baseEnd_3302217 < baseStart_3302217 := by decide
  rcases family_descends (prefixWord ++ tailWord_3302217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3302234 : List Nat := [3, 1, 1, 2, 1, 5, 3, 1, 2, 3]
def baseStart_3302234 : Nat := 118140960795 + 3302234 * 2 ^ 59
def prefixEnd_3302234 : Nat := 4983230072969 + 3 ^ 40 * 3302234 * 2
def baseEnd_3302234 : Nat := 1130422183746225485325539

theorem tailTrace_3302234 : CollatzResearch.WordTrace tailWord_3302234 prefixEnd_3302234 1130422183746225485325539 := by
  unfold tailWord_3302234
  simp only [CollatzResearch.WordTrace]
  refine ⟨30110592179644417377958439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80294912479051779674555837 30110592179644417377958439)
  ·
    refine ⟨45165888269466626066937659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30110592179644417377958439 45165888269466626066937659)
    ·
      refine ⟨67748832404199939100406489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45165888269466626066937659 67748832404199939100406489)
      ·
        refine ⟨50811624303149954325304867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67748832404199939100406489 50811624303149954325304867)
        ·
          refine ⟨76217436454724931487957301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50811624303149954325304867 76217436454724931487957301)
          ·
            refine ⟨7145384667630462326995997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 76217436454724931487957301 7145384667630462326995997)
            ·
              refine ⟨2679519250361423372623499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7145384667630462326995997 2679519250361423372623499)
              ·
                refine ⟨4019278875542135058935249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2679519250361423372623499 4019278875542135058935249)
                ·
                  refine ⟨3014459156656601294201437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4019278875542135058935249 3014459156656601294201437)
                  ·
                    refine ⟨1130422183746225485325539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3014459156656601294201437 1130422183746225485325539)
                    ·
                      rfl

theorem cell22_3302234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 3, 1, 2, 3].length) (baseStart_3302234 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3302234 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3302234 prefixEnd_3302234 := by exact prefixLift 3302234
  have htrace : WordTrace (prefixWord ++ tailWord_3302234) baseStart_3302234 baseEnd_3302234 := by
    simpa [prefixWord, tailWord_3302234, baseEnd_3302234] using wordTrace_append hprefix tailTrace_3302234
  have hstable : (prefixWord ++ tailWord_3302234).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3302234).length < 2 ^ (prefixWord ++ tailWord_3302234).sum := by decide
  have hdescent : baseEnd_3302234 < baseStart_3302234 := by decide
  rcases family_descends (prefixWord ++ tailWord_3302234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3302247 : List Nat := [1, 1, 5, 1, 2, 4, 2, 6]
def baseStart_3302247 : Nat := 118140960795 + 3302247 * 2 ^ 59
def prefixEnd_3302247 : Nat := 4983230072969 + 3 ^ 40 * 3302247 * 2
def baseEnd_3302247 : Nat := 125602959323544198305611

theorem tailTrace_3302247 : CollatzResearch.WordTrace tailWord_3302247 prefixEnd_3302247 125602959323544198305611 := by
  unfold tailWord_3302247
  simp only [CollatzResearch.WordTrace]
  refine ⟨120442842867530572732056995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80295228578353715154704663 120442842867530572732056995)
  ·
    refine ⟨180664264301295859098085493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120442842867530572732056995 180664264301295859098085493)
    ·
      refine ⟨16937274778246486790445515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 180664264301295859098085493 16937274778246486790445515)
      ·
        refine ⟨25405912167369730185668273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16937274778246486790445515 25405912167369730185668273)
        ·
          refine ⟨19054434125527297639251205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25405912167369730185668273 19054434125527297639251205)
          ·
            refine ⟨3572706398536368307359601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19054434125527297639251205 3572706398536368307359601)
            ·
              refine ⟨2679529798902276230519701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3572706398536368307359601 2679529798902276230519701)
              ·
                refine ⟨125602959323544198305611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2679529798902276230519701 125602959323544198305611)
                ·
                  rfl

theorem cell22_3302247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 2, 6].length) (baseStart_3302247 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3302247 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3302247 prefixEnd_3302247 := by exact prefixLift 3302247
  have htrace : WordTrace (prefixWord ++ tailWord_3302247) baseStart_3302247 baseEnd_3302247 := by
    simpa [prefixWord, tailWord_3302247, baseEnd_3302247] using wordTrace_append hprefix tailTrace_3302247
  have hstable : (prefixWord ++ tailWord_3302247).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3302247).length < 2 ^ (prefixWord ++ tailWord_3302247).sum := by decide
  have hdescent : baseEnd_3302247 < baseStart_3302247 := by decide
  rcases family_descends (prefixWord ++ tailWord_3302247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3302275 : List Nat := [1, 1, 1, 3, 4, 1, 2, 4, 5]
def baseStart_3302275 : Nat := 118140960795 + 3302275 * 2 ^ 59
def prefixEnd_3302275 : Nat := 4983230072969 + 3 ^ 40 * 3302275 * 2
def baseEnd_3302275 : Nat := 376812072961371681683471

theorem tailTrace_3302275 : CollatzResearch.WordTrace tailWord_3302275 prefixEnd_3302275 376812072961371681683471 := by
  unfold tailWord_3302275
  simp only [CollatzResearch.WordTrace]
  refine ⟨120443864111429133514076279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80295909407619422342717519 120443864111429133514076279)
  ·
    refine ⟨180665796167143700271114419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120443864111429133514076279 180665796167143700271114419)
    ·
      refine ⟨270998694250715550406671629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180665796167143700271114419 270998694250715550406671629)
      ·
        refine ⟨101624510344018331402501861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 270998694250715550406671629 101624510344018331402501861)
        ·
          refine ⟨19054595689503437137969099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 101624510344018331402501861 19054595689503437137969099)
          ·
            refine ⟨28581893534255155706953649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19054595689503437137969099 28581893534255155706953649)
            ·
              refine ⟨21436420150691366780215237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28581893534255155706953649 21436420150691366780215237)
              ·
                refine ⟨4019328778254631271290357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21436420150691366780215237 4019328778254631271290357)
                ·
                  refine ⟨376812072961371681683471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4019328778254631271290357 376812072961371681683471)
                  ·
                    rfl

theorem cell22_3302275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 4, 5].length) (baseStart_3302275 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3302275 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3302275 prefixEnd_3302275 := by exact prefixLift 3302275
  have htrace : WordTrace (prefixWord ++ tailWord_3302275) baseStart_3302275 baseEnd_3302275 := by
    simpa [prefixWord, tailWord_3302275, baseEnd_3302275] using wordTrace_append hprefix tailTrace_3302275
  have hstable : (prefixWord ++ tailWord_3302275).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3302275).length < 2 ^ (prefixWord ++ tailWord_3302275).sum := by decide
  have hdescent : baseEnd_3302275 < baseStart_3302275 := by decide
  rcases family_descends (prefixWord ++ tailWord_3302275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3302279 : List Nat := [1, 1, 4, 2, 3, 3, 1, 1, 3, 3]
def baseStart_3302279 : Nat := 118140960795 + 3302279 * 2 ^ 59
def prefixEnd_3302279 : Nat := 4983230072969 + 3 ^ 40 * 3302279 * 2
def baseEnd_3302279 : Nat := 1130437588165860367950401

theorem tailTrace_3302279 : CollatzResearch.WordTrace tailWord_3302279 prefixEnd_3302279 1130437588165860367950401 := by
  unfold tailWord_3302279
  simp only [CollatzResearch.WordTrace]
  refine ⟨120444010003414642197221891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80296006668943094798147927 120444010003414642197221891)
  ·
    refine ⟨180666015005121963295832837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120444010003414642197221891 180666015005121963295832837)
    ·
      refine ⟨33874877813460368117968657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 180666015005121963295832837 33874877813460368117968657)
      ·
        refine ⟨25406158360095276088476493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33874877813460368117968657 25406158360095276088476493)
        ·
          refine ⟨9527309385035728533178685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25406158360095276088476493 9527309385035728533178685)
          ·
            refine ⟨3572741019388398199942007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9527309385035728533178685 3572741019388398199942007)
            ·
              refine ⟨5359111529082597299913011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3572741019388398199942007 5359111529082597299913011)
              ·
                refine ⟨8038667293623895949869517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5359111529082597299913011 8038667293623895949869517)
                ·
                  refine ⟨3014500235108960981201069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8038667293623895949869517 3014500235108960981201069)
                  ·
                    refine ⟨1130437588165860367950401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3014500235108960981201069 1130437588165860367950401)
                    ·
                      rfl

theorem cell22_3302279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 1, 1, 3, 3].length) (baseStart_3302279 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3302279 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3302279 prefixEnd_3302279 := by exact prefixLift 3302279
  have htrace : WordTrace (prefixWord ++ tailWord_3302279) baseStart_3302279 baseEnd_3302279 := by
    simpa [prefixWord, tailWord_3302279, baseEnd_3302279] using wordTrace_append hprefix tailTrace_3302279
  have hstable : (prefixWord ++ tailWord_3302279).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3302279).length < 2 ^ (prefixWord ++ tailWord_3302279).sum := by decide
  have hdescent : baseEnd_3302279 < baseStart_3302279 := by decide
  rcases family_descends (prefixWord ++ tailWord_3302279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3302292 : List Nat := [2, 4, 2, 1, 1, 1, 3, 3, 5]
def baseStart_3302292 : Nat := 118140960795 + 3302292 * 2 ^ 59
def prefixEnd_3302292 : Nat := 4983230072969 + 3 ^ 40 * 3302292 * 2
def baseEnd_3302292 : Nat := 376814012777177555791787

theorem tailTrace_3302292 : CollatzResearch.WordTrace tailWord_3302292 prefixEnd_3302292 376814012777177555791787 := by
  unfold tailWord_3302292
  simp only [CollatzResearch.WordTrace]
  refine ⟨60222242076183772708722565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80296322768245030278296753 60222242076183772708722565)
  ·
    refine ⟨11291670389284457382885481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60222242076183772708722565 11291670389284457382885481)
    ·
      refine ⟨8468752791963343037164111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11291670389284457382885481 8468752791963343037164111)
      ·
        refine ⟨12703129187945014555746167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8468752791963343037164111 12703129187945014555746167)
        ·
          refine ⟨19054693781917521833619251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12703129187945014555746167 19054693781917521833619251)
          ·
            refine ⟨28582040672876282750428877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19054693781917521833619251 28582040672876282750428877)
            ·
              refine ⟨10718265252328606031410829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28582040672876282750428877 10718265252328606031410829)
              ·
                refine ⟨4019349469623227261779061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10718265252328606031410829 4019349469623227261779061)
                ·
                  refine ⟨376814012777177555791787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4019349469623227261779061 376814012777177555791787)
                  ·
                    rfl

theorem cell22_3302292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 3, 3, 5].length) (baseStart_3302292 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3302292 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3302292 prefixEnd_3302292 := by exact prefixLift 3302292
  have htrace : WordTrace (prefixWord ++ tailWord_3302292) baseStart_3302292 baseEnd_3302292 := by
    simpa [prefixWord, tailWord_3302292, baseEnd_3302292] using wordTrace_append hprefix tailTrace_3302292
  have hstable : (prefixWord ++ tailWord_3302292).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3302292).length < 2 ^ (prefixWord ++ tailWord_3302292).sum := by decide
  have hdescent : baseEnd_3302292 < baseStart_3302292 := by decide
  rcases family_descends (prefixWord ++ tailWord_3302292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3302367 : List Nat := [1, 1, 2, 3, 5, 1, 1, 1, 1, 6]
def baseStart_3302367 : Nat := 118140960795 + 3302367 * 2 ^ 59
def prefixEnd_3302367 : Nat := 4983230072969 + 3 ^ 40 * 3302367 * 2
def baseEnd_3302367 : Nat := 1130467712364257471750131

theorem tailTrace_3302367 : CollatzResearch.WordTrace tailWord_3302367 prefixEnd_3302367 1130467712364257471750131 := by
  unfold tailWord_3302367
  simp only [CollatzResearch.WordTrace]
  refine ⟨120447219627095833226425355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80298146418063888817616903 120447219627095833226425355)
  ·
    refine ⟨180670829440643749839638033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120447219627095833226425355 180670829440643749839638033)
    ·
      refine ⟨135503122080482812379728525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180670829440643749839638033 135503122080482812379728525)
      ·
        refine ⟨50813670780181054642398197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135503122080482812379728525 50813670780181054642398197)
        ·
          refine ⟨4763781635641973872724831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 50813670780181054642398197 4763781635641973872724831)
          ·
            refine ⟨7145672453462960809087247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4763781635641973872724831 7145672453462960809087247)
            ·
              refine ⟨10718508680194441213630871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7145672453462960809087247 10718508680194441213630871)
              ·
                refine ⟨16077763020291661820446307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10718508680194441213630871 16077763020291661820446307)
                ·
                  refine ⟨24116644530437492730669461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16077763020291661820446307 24116644530437492730669461)
                  ·
                    refine ⟨1130467712364257471750131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24116644530437492730669461 1130467712364257471750131)
                    ·
                      rfl

theorem cell22_3302367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 1, 1, 1, 6].length) (baseStart_3302367 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3302367 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3302367 prefixEnd_3302367 := by exact prefixLift 3302367
  have htrace : WordTrace (prefixWord ++ tailWord_3302367) baseStart_3302367 baseEnd_3302367 := by
    simpa [prefixWord, tailWord_3302367, baseEnd_3302367] using wordTrace_append hprefix tailTrace_3302367
  have hstable : (prefixWord ++ tailWord_3302367).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3302367).length < 2 ^ (prefixWord ++ tailWord_3302367).sum := by decide
  have hdescent : baseEnd_3302367 < baseStart_3302367 := by decide
  rcases family_descends (prefixWord ++ tailWord_3302367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3302373 : List Nat := [1, 3, 1, 6, 1, 2, 2, 1, 1, 4]
def baseStart_3302373 : Nat := 118140960795 + 3302373 * 2 ^ 59
def prefixEnd_3302373 : Nat := 4983230072969 + 3 ^ 40 * 3302373 * 2
def baseEnd_3302373 : Nat := 1130469766286875456100113

theorem tailTrace_3302373 : CollatzResearch.WordTrace tailWord_3302373 prefixEnd_3302373 1130469766286875456100113 := by
  unfold tailWord_3302373
  simp only [CollatzResearch.WordTrace]
  refine ⟨120447438465074096251143773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80298292310049397500762515 120447438465074096251143773)
  ·
    refine ⟨45167789424402786094178915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120447438465074096251143773 45167789424402786094178915)
    ·
      refine ⟨67751684136604179141268373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45167789424402786094178915 67751684136604179141268373)
      ·
        refine ⟨3175860193903320897246955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 67751684136604179141268373 3175860193903320897246955)
        ·
          refine ⟨4763790290854981345870433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3175860193903320897246955 4763790290854981345870433)
          ·
            refine ⟨3572842718141236009402825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4763790290854981345870433 3572842718141236009402825)
            ·
              refine ⟨2679632038605927007052119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3572842718141236009402825 2679632038605927007052119)
              ·
                refine ⟨4019448057908890510578179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2679632038605927007052119 4019448057908890510578179)
                ·
                  refine ⟨6029172086863335765867269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4019448057908890510578179 6029172086863335765867269)
                  ·
                    refine ⟨1130469766286875456100113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6029172086863335765867269 1130469766286875456100113)
                    ·
                      rfl

theorem cell22_3302373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 2, 1, 1, 4].length) (baseStart_3302373 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3302373 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3302373 prefixEnd_3302373 := by exact prefixLift 3302373
  have htrace : WordTrace (prefixWord ++ tailWord_3302373) baseStart_3302373 baseEnd_3302373 := by
    simpa [prefixWord, tailWord_3302373, baseEnd_3302373] using wordTrace_append hprefix tailTrace_3302373
  have hstable : (prefixWord ++ tailWord_3302373).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3302373).length < 2 ^ (prefixWord ++ tailWord_3302373).sum := by decide
  have hdescent : baseEnd_3302373 < baseStart_3302373 := by decide
  rcases family_descends (prefixWord ++ tailWord_3302373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3302382 : List Nat := [4, 1, 2, 1, 4, 1, 9]
def baseStart_3302382 : Nat := 118140960795 + 3302382 * 2 ^ 59
def prefixEnd_3302382 : Nat := 4983230072969 + 3 ^ 40 * 3302382 * 2
def baseEnd_3302382 : Nat := 41869364710029719726855

theorem tailTrace_3302382 : CollatzResearch.WordTrace tailWord_3302382 prefixEnd_3302382 41869364710029719726855 := by
  unfold tailWord_3302382
  simp only [CollatzResearch.WordTrace]
  refine ⟨15055970840255186348527675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80298511148027660525480933 15055970840255186348527675)
  ·
    refine ⟨22583956260382779522791513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15055970840255186348527675 22583956260382779522791513)
    ·
      refine ⟨16937967195287084642093635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22583956260382779522791513 16937967195287084642093635)
      ·
        refine ⟨25406950792930626963140453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16937967195287084642093635 25406950792930626963140453)
        ·
          refine ⟨4763803273674492555588835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25406950792930626963140453 4763803273674492555588835)
          ·
            refine ⟨7145704910511738833383253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4763803273674492555588835 7145704910511738833383253)
            ·
              refine ⟨41869364710029719726855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7145704910511738833383253 41869364710029719726855)
              ·
                rfl

theorem cell22_3302382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 9].length) (baseStart_3302382 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3302382 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3302382 prefixEnd_3302382 := by exact prefixLift 3302382
  have htrace : WordTrace (prefixWord ++ tailWord_3302382) baseStart_3302382 baseEnd_3302382 := by
    simpa [prefixWord, tailWord_3302382, baseEnd_3302382] using wordTrace_append hprefix tailTrace_3302382
  have hstable : (prefixWord ++ tailWord_3302382).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3302382).length < 2 ^ (prefixWord ++ tailWord_3302382).sum := by decide
  have hdescent : baseEnd_3302382 < baseStart_3302382 := by decide
  rcases family_descends (prefixWord ++ tailWord_3302382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3302386 : List Nat := [3, 2, 1, 5, 1, 1, 1, 1, 4, 3]
def baseStart_3302386 : Nat := 118140960795 + 3302386 * 2 ^ 59
def prefixEnd_3302386 : Nat := 4983230072969 + 3 ^ 40 * 3302386 * 2
def baseEnd_3302386 : Nat := 1130474216452547755525073

theorem tailTrace_3302386 : CollatzResearch.WordTrace tailWord_3302386 prefixEnd_3302386 1130474216452547755525073 := by
  unfold tailWord_3302386
  simp only [CollatzResearch.WordTrace]
  refine ⟨30111978153506749867841753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80298608409351332980911341 30111978153506749867841753)
  ·
    refine ⟨22583983615130062400881315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30111978153506749867841753 22583983615130062400881315)
    ·
      refine ⟨33875975422695093601321973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22583983615130062400881315 33875975422695093601321973)
      ·
        refine ⟨3175872695877665025123935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 33875975422695093601321973 3175872695877665025123935)
        ·
          refine ⟨4763809043816497537685903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3175872695877665025123935 4763809043816497537685903)
          ·
            refine ⟨7145713565724746306528855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4763809043816497537685903 7145713565724746306528855)
            ·
              refine ⟨10718570348587119459793283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7145713565724746306528855 10718570348587119459793283)
              ·
                refine ⟨16077855522880679189689925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10718570348587119459793283 16077855522880679189689925)
                ·
                  refine ⟨3014597910540127348066861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16077855522880679189689925 3014597910540127348066861)
                  ·
                    refine ⟨1130474216452547755525073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3014597910540127348066861 1130474216452547755525073)
                    ·
                      rfl

theorem cell22_3302386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 1, 1, 4, 3].length) (baseStart_3302386 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3302386 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3302386 prefixEnd_3302386 := by exact prefixLift 3302386
  have htrace : WordTrace (prefixWord ++ tailWord_3302386) baseStart_3302386 baseEnd_3302386 := by
    simpa [prefixWord, tailWord_3302386, baseEnd_3302386] using wordTrace_append hprefix tailTrace_3302386
  have hstable : (prefixWord ++ tailWord_3302386).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3302386).length < 2 ^ (prefixWord ++ tailWord_3302386).sum := by decide
  have hdescent : baseEnd_3302386 < baseStart_3302386 := by decide
  rcases family_descends (prefixWord ++ tailWord_3302386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3302414 : List Nat := [4, 1, 1, 2, 2, 2, 2, 2, 3, 3]
def baseStart_3302414 : Nat := 118140960795 + 3302414 * 2 ^ 59
def prefixEnd_3302414 : Nat := 4983230072969 + 3 ^ 40 * 3302414 * 2
def baseEnd_3302414 : Nat := 1130483801424765015824987

theorem tailTrace_3302414 : CollatzResearch.WordTrace tailWord_3302414 prefixEnd_3302414 1130483801424765015824987 := by
  unfold tailWord_3302414
  simp only [CollatzResearch.WordTrace]
  refine ⟨15056116732240695031673287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80299289238617040168924197 15056116732240695031673287)
  ·
    refine ⟨22584175098361042547509931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15056116732240695031673287 22584175098361042547509931)
    ·
      refine ⟨33876262647541563821264897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22584175098361042547509931 33876262647541563821264897)
      ·
        refine ⟨25407196985656172865948673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33876262647541563821264897 25407196985656172865948673)
        ·
          refine ⟨19055397739242129649461505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25407196985656172865948673 19055397739242129649461505)
          ·
            refine ⟨14291548304431597237096129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19055397739242129649461505 14291548304431597237096129)
            ·
              refine ⟨10718661228323697927822097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14291548304431597237096129 10718661228323697927822097)
              ·
                refine ⟨8038995921242773445866573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10718661228323697927822097 8038995921242773445866573)
                ·
                  refine ⟨3014623470466040042199965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8038995921242773445866573 3014623470466040042199965)
                  ·
                    refine ⟨1130483801424765015824987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3014623470466040042199965 1130483801424765015824987)
                    ·
                      rfl

theorem cell22_3302414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 2, 2, 3, 3].length) (baseStart_3302414 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3302414 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3302414 prefixEnd_3302414 := by exact prefixLift 3302414
  have htrace : WordTrace (prefixWord ++ tailWord_3302414) baseStart_3302414 baseEnd_3302414 := by
    simpa [prefixWord, tailWord_3302414, baseEnd_3302414] using wordTrace_append hprefix tailTrace_3302414
  have hstable : (prefixWord ++ tailWord_3302414).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3302414).length < 2 ^ (prefixWord ++ tailWord_3302414).sum := by decide
  have hdescent : baseEnd_3302414 < baseStart_3302414 := by decide
  rcases family_descends (prefixWord ++ tailWord_3302414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3302425 : List Nat := [1, 2, 1, 2, 1, 1, 4, 2, 1, 7]
def baseStart_3302425 : Nat := 118140960795 + 3302425 * 2 ^ 59
def prefixEnd_3302425 : Nat := 4983230072969 + 3 ^ 40 * 3302425 * 2
def baseEnd_3302425 : Nat := 1130487566949564653799953

theorem tailTrace_3302425 : CollatzResearch.WordTrace tailWord_3302425 prefixEnd_3302425 1130487566949564653799953 := by
  unfold tailWord_3302425
  simp only [CollatzResearch.WordTrace]
  refine ⟨120449335060885709132036729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80299556707257139421357819 120449335060885709132036729)
  ·
    refine ⟨90337001295664281849027547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120449335060885709132036729 90337001295664281849027547)
    ·
      refine ⟨135505501943496422773541321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90337001295664281849027547 135505501943496422773541321)
      ·
        refine ⟨101629126457622317080155991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135505501943496422773541321 101629126457622317080155991)
        ·
          refine ⟨152443689686433475620233987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101629126457622317080155991 152443689686433475620233987)
          ·
            refine ⟨228665534529650213430350981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152443689686433475620233987 228665534529650213430350981)
            ·
              refine ⟨42874787724309415018190809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 228665534529650213430350981 42874787724309415018190809)
              ·
                refine ⟨32156090793232061263643107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42874787724309415018190809 32156090793232061263643107)
                ·
                  refine ⟨48234136189848091895464661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32156090793232061263643107 48234136189848091895464661)
                  ·
                    refine ⟨1130487566949564653799953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48234136189848091895464661 1130487566949564653799953)
                    ·
                      rfl

theorem cell22_3302425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 2, 1, 7].length) (baseStart_3302425 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3302425 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3302425 prefixEnd_3302425 := by exact prefixLift 3302425
  have htrace : WordTrace (prefixWord ++ tailWord_3302425) baseStart_3302425 baseEnd_3302425 := by
    simpa [prefixWord, tailWord_3302425, baseEnd_3302425] using wordTrace_append hprefix tailTrace_3302425
  have hstable : (prefixWord ++ tailWord_3302425).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3302425).length < 2 ^ (prefixWord ++ tailWord_3302425).sum := by decide
  have hdescent : baseEnd_3302425 < baseStart_3302425 := by decide
  rcases family_descends (prefixWord ++ tailWord_3302425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3302431 : List Nat := [1, 1, 2, 4, 1, 3, 3, 3, 1, 3]
def baseStart_3302431 : Nat := 118140960795 + 3302431 * 2 ^ 59
def prefixEnd_3302431 : Nat := 4983230072969 + 3 ^ 40 * 3302431 * 2
def baseEnd_3302431 : Nat := 1130489620872182638149935

theorem tailTrace_3302431 : CollatzResearch.WordTrace tailWord_3302431 prefixEnd_3302431 1130489620872182638149935 := by
  unfold tailWord_3302431
  simp only [CollatzResearch.WordTrace]
  refine ⟨120449553898863972156755147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80299702599242648104503431 120449553898863972156755147)
  ·
    refine ⟨180674330848295958235132721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120449553898863972156755147 180674330848295958235132721)
    ·
      refine ⟨135505748136221968676349541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180674330848295958235132721 135505748136221968676349541)
      ·
        refine ⟨25407327775541619126815539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 135505748136221968676349541 25407327775541619126815539)
        ·
          refine ⟨38110991663312428690223309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25407327775541619126815539 38110991663312428690223309)
          ·
            refine ⟨14291621873742160758833741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38110991663312428690223309 14291621873742160758833741)
            ·
              refine ⟨5359358202653310284562653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14291621873742160758833741 5359358202653310284562653)
              ·
                refine ⟨2009759325994991356710995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5359358202653310284562653 2009759325994991356710995)
                ·
                  refine ⟨3014638988992487035066493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2009759325994991356710995 3014638988992487035066493)
                  ·
                    refine ⟨1130489620872182638149935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3014638988992487035066493 1130489620872182638149935)
                    ·
                      rfl

theorem cell22_3302431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 3, 3, 1, 3].length) (baseStart_3302431 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3302431 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3302431 prefixEnd_3302431 := by exact prefixLift 3302431
  have htrace : WordTrace (prefixWord ++ tailWord_3302431) baseStart_3302431 baseEnd_3302431 := by
    simpa [prefixWord, tailWord_3302431, baseEnd_3302431] using wordTrace_append hprefix tailTrace_3302431
  have hstable : (prefixWord ++ tailWord_3302431).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3302431).length < 2 ^ (prefixWord ++ tailWord_3302431).sum := by decide
  have hdescent : baseEnd_3302431 < baseStart_3302431 := by decide
  rcases family_descends (prefixWord ++ tailWord_3302431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3302461 : List Nat := [1, 4, 1, 3, 1, 4, 2, 1, 5]
def baseStart_3302461 : Nat := 118140960795 + 3302461 * 2 ^ 59
def prefixEnd_3302461 : Nat := 4983230072969 + 3 ^ 40 * 3302461 * 2
def baseEnd_3302461 : Nat := 376833296828424186633281

theorem tailTrace_3302461 : CollatzResearch.WordTrace tailWord_3302461 prefixEnd_3302461 376833296828424186633281 := by
  unfold tailWord_3302461
  simp only [CollatzResearch.WordTrace]
  refine ⟨120450648088755287280347237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80300432059170191520231491 120450648088755287280347237)
  ·
    refine ⟨22584496516641616365065107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 120450648088755287280347237 22584496516641616365065107)
    ·
      refine ⟨33876744774962424547597661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22584496516641616365065107 33876744774962424547597661)
      ·
        refine ⟨12703779290610909205349123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33876744774962424547597661 12703779290610909205349123)
        ·
          refine ⟨19055668935916363808023685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12703779290610909205349123 19055668935916363808023685)
          ·
            refine ⟨3572937925484318214004441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19055668935916363808023685 3572937925484318214004441)
            ·
              refine ⟨2679703444113238660503331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3572937925484318214004441 2679703444113238660503331)
              ·
                refine ⟨4019555166169857990754997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2679703444113238660503331 4019555166169857990754997)
                ·
                  refine ⟨376833296828424186633281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4019555166169857990754997 376833296828424186633281)
                  ·
                    rfl

theorem cell22_3302461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 2, 1, 5].length) (baseStart_3302461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3302461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3302461 prefixEnd_3302461 := by exact prefixLift 3302461
  have htrace : WordTrace (prefixWord ++ tailWord_3302461) baseStart_3302461 baseEnd_3302461 := by
    simpa [prefixWord, tailWord_3302461, baseEnd_3302461] using wordTrace_append hprefix tailTrace_3302461
  have hstable : (prefixWord ++ tailWord_3302461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3302461).length < 2 ^ (prefixWord ++ tailWord_3302461).sum := by decide
  have hdescent : baseEnd_3302461 < baseStart_3302461 := by decide
  rcases family_descends (prefixWord ++ tailWord_3302461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3302474 : List Nat := [3, 1, 2, 1, 1, 2, 5, 2, 1, 4]
def baseStart_3302474 : Nat := 118140960795 + 3302474 * 2 ^ 59
def prefixEnd_3302474 : Nat := 4983230072969 + 3 ^ 40 * 3302474 * 2
def baseEnd_3302474 : Nat := 1130504340650944859324803

theorem tailTrace_3302474 : CollatzResearch.WordTrace tailWord_3302474 prefixEnd_3302474 1130504340650944859324803 := by
  unfold tailWord_3302474
  simp only [CollatzResearch.WordTrace]
  refine ⟨30112780559427047625142619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80300748158472127000380317 30112780559427047625142619)
  ·
    refine ⟨45169170839140571437713929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30112780559427047625142619 45169170839140571437713929)
    ·
      refine ⟨33876878129355428578285447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45169170839140571437713929 33876878129355428578285447)
      ·
        refine ⟨50815317194033142867428171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33876878129355428578285447 50815317194033142867428171)
        ·
          refine ⟨76222975791049714301142257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50815317194033142867428171 76222975791049714301142257)
          ·
            refine ⟨57167231843287285725856693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76222975791049714301142257 57167231843287285725856693)
            ·
              refine ⟨5359427985308183036799065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 57167231843287285725856693 5359427985308183036799065)
              ·
                refine ⟨4019570988981137277599299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5359427985308183036799065 4019570988981137277599299)
                ·
                  refine ⟨6029356483471705916398949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4019570988981137277599299 6029356483471705916398949)
                  ·
                    refine ⟨1130504340650944859324803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6029356483471705916398949 1130504340650944859324803)
                    ·
                      rfl

theorem cell22_3302474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 5, 2, 1, 4].length) (baseStart_3302474 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3302474 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3302474 prefixEnd_3302474 := by exact prefixLift 3302474
  have htrace : WordTrace (prefixWord ++ tailWord_3302474) baseStart_3302474 baseEnd_3302474 := by
    simpa [prefixWord, tailWord_3302474, baseEnd_3302474] using wordTrace_append hprefix tailTrace_3302474
  have hstable : (prefixWord ++ tailWord_3302474).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3302474).length < 2 ^ (prefixWord ++ tailWord_3302474).sum := by decide
  have hdescent : baseEnd_3302474 < baseStart_3302474 := by decide
  rcases family_descends (prefixWord ++ tailWord_3302474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3302506 : List Nat := [3, 1, 3, 2, 2, 2, 1, 4, 4]
def baseStart_3302506 : Nat := 118140960795 + 3302506 * 2 ^ 59
def prefixEnd_3302506 : Nat := 4983230072969 + 3 ^ 40 * 3302506 * 2
def baseEnd_3302506 : Nat := 376838431634969147508235

theorem tailTrace_3302506 : CollatzResearch.WordTrace tailWord_3302506 prefixEnd_3302506 376838431634969147508235 := by
  unfold tailWord_3302506
  simp only [CollatzResearch.WordTrace]
  refine ⟨30113072343398064991433843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80301526249061506643823581 30113072343398064991433843)
  ·
    refine ⟨45169608515097097487150765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30113072343398064991433843 45169608515097097487150765)
    ·
      refine ⟨16938603193161411557681537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45169608515097097487150765 16938603193161411557681537)
      ·
        refine ⟨12703952394871058668261153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16938603193161411557681537 12703952394871058668261153)
        ·
          refine ⟨9527964296153294001195865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12703952394871058668261153 9527964296153294001195865)
          ·
            refine ⟨7145973222114970500896899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9527964296153294001195865 7145973222114970500896899)
            ·
              refine ⟨10718959833172455751345349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7145973222114970500896899 10718959833172455751345349)
              ·
                refine ⟨2009804968719835453377253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10718959833172455751345349 2009804968719835453377253)
                ·
                  refine ⟨376838431634969147508235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2009804968719835453377253 376838431634969147508235)
                  ·
                    rfl

theorem cell22_3302506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 1, 4, 4].length) (baseStart_3302506 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3302506 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3302506 prefixEnd_3302506 := by exact prefixLift 3302506
  have htrace : WordTrace (prefixWord ++ tailWord_3302506) baseStart_3302506 baseEnd_3302506 := by
    simpa [prefixWord, tailWord_3302506, baseEnd_3302506] using wordTrace_append hprefix tailTrace_3302506
  have hstable : (prefixWord ++ tailWord_3302506).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3302506).length < 2 ^ (prefixWord ++ tailWord_3302506).sum := by decide
  have hdescent : baseEnd_3302506 < baseStart_3302506 := by decide
  rcases family_descends (prefixWord ++ tailWord_3302506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3302624 : List Nat := [2, 1, 1, 3, 1, 4, 3, 1, 6]
def baseStart_3302624 : Nat := 118140960795 + 3302624 * 2 ^ 59
def prefixEnd_3302624 : Nat := 4983230072969 + 3 ^ 40 * 3302624 * 2
def baseEnd_3302624 : Nat := 376851896238798156024781

theorem tailTrace_3302624 : CollatzResearch.WordTrace tailWord_3302624 prefixEnd_3302624 376851896238798156024781 := by
  unfold tailWord_3302624
  simp only [CollatzResearch.WordTrace]
  refine ⟨60228296593582383059265463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80304395458109844079020617 60228296593582383059265463)
  ·
    refine ⟨90342444890373574588898195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60228296593582383059265463 90342444890373574588898195)
    ·
      refine ⟨135513667335560361883347293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90342444890373574588898195 135513667335560361883347293)
      ·
        refine ⟨50817625250835135706255235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135513667335560361883347293 50817625250835135706255235)
        ·
          refine ⟨76226437876252703559382853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50817625250835135706255235 76226437876252703559382853)
          ·
            refine ⟨14292457101797381917384285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76226437876252703559382853 14292457101797381917384285)
            ·
              refine ⟨5359671413174018219019107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14292457101797381917384285 5359671413174018219019107)
              ·
                refine ⟨8039507119761027328528661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5359671413174018219019107 8039507119761027328528661)
                ·
                  refine ⟨376851896238798156024781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8039507119761027328528661 376851896238798156024781)
                  ·
                    rfl

theorem cell22_3302624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 3, 1, 6].length) (baseStart_3302624 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3302624 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3302624 prefixEnd_3302624 := by exact prefixLift 3302624
  have htrace : WordTrace (prefixWord ++ tailWord_3302624) baseStart_3302624 baseEnd_3302624 := by
    simpa [prefixWord, tailWord_3302624, baseEnd_3302624] using wordTrace_append hprefix tailTrace_3302624
  have hstable : (prefixWord ++ tailWord_3302624).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3302624).length < 2 ^ (prefixWord ++ tailWord_3302624).sum := by decide
  have hdescent : baseEnd_3302624 < baseStart_3302624 := by decide
  rcases family_descends (prefixWord ++ tailWord_3302624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3302669 : List Nat := [1, 7, 14]
def baseStart_3302669 : Nat := 118140960795 + 3302669 * 2 ^ 59
def prefixEnd_3302669 : Nat := 4983230072969 + 3 ^ 40 * 3302669 * 2
def baseEnd_3302669 : Nat := 516950659870155167215

theorem tailTrace_3302669 : CollatzResearch.WordTrace tailWord_3302669 prefixEnd_3302669 516950659870155167215 := by
  unfold tailWord_3302669
  simp only [CollatzResearch.WordTrace]
  refine ⟨120458234472001738803919061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80305489648001159202612707 120458234472001738803919061)
  ·
    refine ⟨2823239870437540753216853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 120458234472001738803919061 2823239870437540753216853)
    ·
      refine ⟨516950659870155167215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 14 2823239870437540753216853 516950659870155167215)
      ·
        rfl

theorem cell22_3302669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 14].length) (baseStart_3302669 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3302669 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3302669 prefixEnd_3302669 := by exact prefixLift 3302669
  have htrace : WordTrace (prefixWord ++ tailWord_3302669) baseStart_3302669 baseEnd_3302669 := by
    simpa [prefixWord, tailWord_3302669, baseEnd_3302669] using wordTrace_append hprefix tailTrace_3302669
  have hstable : (prefixWord ++ tailWord_3302669).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3302669).length < 2 ^ (prefixWord ++ tailWord_3302669).sum := by decide
  have hdescent : baseEnd_3302669 < baseStart_3302669 := by decide
  rcases family_descends (prefixWord ++ tailWord_3302669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3302714 : List Nat := [3, 1, 1, 1, 4, 1, 2, 2, 7]
def baseStart_3302714 : Nat := 118140960795 + 3302714 * 2 ^ 59
def prefixEnd_3302714 : Nat := 4983230072969 + 3 ^ 40 * 3302714 * 2
def baseEnd_3302714 : Nat := 376862165851888077774689

theorem tailTrace_3302714 : CollatzResearch.WordTrace tailWord_3302714 prefixEnd_3302714 376862165851888077774689 := by
  unfold tailWord_3302714
  simp only [CollatzResearch.WordTrace]
  refine ⟨30114968939209677872326799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80306583837892474326204797 30114968939209677872326799)
  ·
    refine ⟨45172453408814516808490199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30114968939209677872326799 45172453408814516808490199)
    ·
      refine ⟨67758680113221775212735299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45172453408814516808490199 67758680113221775212735299)
      ·
        refine ⟨101638020169832662819102949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67758680113221775212735299 101638020169832662819102949)
        ·
          refine ⟨19057128781843624278581803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 101638020169832662819102949 19057128781843624278581803)
          ·
            refine ⟨28585693172765436417872705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19057128781843624278581803 28585693172765436417872705)
            ·
              refine ⟨21439269879574077313404529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28585693172765436417872705 21439269879574077313404529)
              ·
                refine ⟨16079452409680557985053397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21439269879574077313404529 16079452409680557985053397)
                ·
                  refine ⟨376862165851888077774689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16079452409680557985053397 376862165851888077774689)
                  ·
                    rfl

theorem cell22_3302714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 2, 7].length) (baseStart_3302714 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3302714 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3302714 prefixEnd_3302714 := by exact prefixLift 3302714
  have htrace : WordTrace (prefixWord ++ tailWord_3302714) baseStart_3302714 baseEnd_3302714 := by
    simpa [prefixWord, tailWord_3302714, baseEnd_3302714] using wordTrace_append hprefix tailTrace_3302714
  have hstable : (prefixWord ++ tailWord_3302714).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3302714).length < 2 ^ (prefixWord ++ tailWord_3302714).sum := by decide
  have hdescent : baseEnd_3302714 < baseStart_3302714 := by decide
  rcases family_descends (prefixWord ++ tailWord_3302714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3302729 : List Nat := [1, 2, 1, 1, 2, 3, 3, 2, 2, 5]
def baseStart_3302729 : Nat := 118140960795 + 3302729 * 2 ^ 59
def prefixEnd_3302729 : Nat := 4983230072969 + 3 ^ 40 * 3302729 * 2
def baseEnd_3302729 : Nat := 1130591632362209194199021

theorem tailTrace_3302729 : CollatzResearch.WordTrace tailWord_3302729 prefixEnd_3302729 1130591632362209194199021 := by
  unfold tailWord_3302729
  simp only [CollatzResearch.WordTrace]
  refine ⟨120460422851784369051103241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80306948567856246034068827 120460422851784369051103241)
  ·
    refine ⟨90345317138838276788327431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120460422851784369051103241 90345317138838276788327431)
    ·
      refine ⟨135517975708257415182491147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90345317138838276788327431 135517975708257415182491147)
      ·
        refine ⟨203276963562386122773736721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135517975708257415182491147 203276963562386122773736721)
        ·
          refine ⟨152457722671789592080302541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 203276963562386122773736721 152457722671789592080302541)
          ·
            refine ⟨57171646001921097030113453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 152457722671789592080302541 57171646001921097030113453)
            ·
              refine ⟨21439367250720411386292545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57171646001921097030113453 21439367250720411386292545)
              ·
                refine ⟨16079525438040308539719409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21439367250720411386292545 16079525438040308539719409)
                ·
                  refine ⟨12059644078530231404789557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16079525438040308539719409 12059644078530231404789557)
                  ·
                    refine ⟨1130591632362209194199021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12059644078530231404789557 1130591632362209194199021)
                    ·
                      rfl

theorem cell22_3302729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 2, 2, 5].length) (baseStart_3302729 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3302729 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3302729 prefixEnd_3302729 := by exact prefixLift 3302729
  have htrace : WordTrace (prefixWord ++ tailWord_3302729) baseStart_3302729 baseEnd_3302729 := by
    simpa [prefixWord, tailWord_3302729, baseEnd_3302729] using wordTrace_append hprefix tailTrace_3302729
  have hstable : (prefixWord ++ tailWord_3302729).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3302729).length < 2 ^ (prefixWord ++ tailWord_3302729).sum := by decide
  have hdescent : baseEnd_3302729 < baseStart_3302729 := by decide
  rcases family_descends (prefixWord ++ tailWord_3302729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3302793 : List Nat := [1, 2, 1, 1, 7, 2, 1, 1, 6]
def baseStart_3302793 : Nat := 118140960795 + 3302793 * 2 ^ 59
def prefixEnd_3302793 : Nat := 4983230072969 + 3 ^ 40 * 3302793 * 2
def baseEnd_3302793 : Nat := 376871180290044786866275

theorem tailTrace_3302793 : CollatzResearch.WordTrace tailWord_3302793 prefixEnd_3302793 376871180290044786866275 := by
  unfold tailWord_3302793
  simp only [CollatzResearch.WordTrace]
  refine ⟨120462757123552507981433033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80308504749035005320955355 120462757123552507981433033)
  ·
    refine ⟨90347067842664380986074775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120462757123552507981433033 90347067842664380986074775)
    ·
      refine ⟨135520601763996571479112163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90347067842664380986074775 135520601763996571479112163)
      ·
        refine ⟨203280902645994857218668245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135520601763996571479112163 203280902645994857218668245)
        ·
          refine ⟨4764396155765504466062537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 203280902645994857218668245 4764396155765504466062537)
          ·
            refine ⟨3573297116824128349546903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4764396155765504466062537 3573297116824128349546903)
            ·
              refine ⟨5359945675236192524320355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3573297116824128349546903 5359945675236192524320355)
              ·
                refine ⟨8039918512854288786480533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5359945675236192524320355 8039918512854288786480533)
                ·
                  refine ⟨376871180290044786866275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8039918512854288786480533 376871180290044786866275)
                  ·
                    rfl

theorem cell22_3302793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 1, 1, 6].length) (baseStart_3302793 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3302793 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3302793 prefixEnd_3302793 := by exact prefixLift 3302793
  have htrace : WordTrace (prefixWord ++ tailWord_3302793) baseStart_3302793 baseEnd_3302793 := by
    simpa [prefixWord, tailWord_3302793, baseEnd_3302793] using wordTrace_append hprefix tailTrace_3302793
  have hstable : (prefixWord ++ tailWord_3302793).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3302793).length < 2 ^ (prefixWord ++ tailWord_3302793).sum := by decide
  have hdescent : baseEnd_3302793 < baseStart_3302793 := by decide
  rcases family_descends (prefixWord ++ tailWord_3302793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3302812 : List Nat := [2, 2, 3, 4, 1, 2, 1, 2, 1, 4]
def baseStart_3302812 : Nat := 118140960795 + 3302812 * 2 ^ 59
def prefixEnd_3302812 : Nat := 4983230072969 + 3 ^ 40 * 3302812 * 2
def baseEnd_3302812 : Nat := 1130620044958424644373767

theorem tailTrace_3302812 : CollatzResearch.WordTrace tailWord_3302812 prefixEnd_3302812 1130620044958424644373767 := by
  unfold tailWord_3302812
  simp only [CollatzResearch.WordTrace]
  refine ⟨60231725055241837113187345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80308966740322449484249793 60231725055241837113187345)
  ·
    refine ⟨45173793791431377834890509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60231725055241837113187345 45173793791431377834890509)
    ·
      refine ⟨16940172671786766688083941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45173793791431377834890509 16940172671786766688083941)
      ·
        refine ⟨3176282375960018754015739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16940172671786766688083941 3176282375960018754015739)
        ·
          refine ⟨4764423563940028131023609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3176282375960018754015739 4764423563940028131023609)
          ·
            refine ⟨3573317672955021098267707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4764423563940028131023609 3573317672955021098267707)
            ·
              refine ⟨5359976509432531647401561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3573317672955021098267707 5359976509432531647401561)
              ·
                refine ⟨4019982382074398735551171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5359976509432531647401561 4019982382074398735551171)
                ·
                  refine ⟨6029973573111598103326757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4019982382074398735551171 6029973573111598103326757)
                  ·
                    refine ⟨1130620044958424644373767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6029973573111598103326757 1130620044958424644373767)
                    ·
                      rfl

theorem cell22_3302812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 1, 2, 1, 4].length) (baseStart_3302812 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3302812 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3302812 prefixEnd_3302812 := by exact prefixLift 3302812
  have htrace : WordTrace (prefixWord ++ tailWord_3302812) baseStart_3302812 baseEnd_3302812 := by
    simpa [prefixWord, tailWord_3302812, baseEnd_3302812] using wordTrace_append hprefix tailTrace_3302812
  have hstable : (prefixWord ++ tailWord_3302812).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3302812).length < 2 ^ (prefixWord ++ tailWord_3302812).sum := by decide
  have hdescent : baseEnd_3302812 < baseStart_3302812 := by decide
  rcases family_descends (prefixWord ++ tailWord_3302812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3302823 : List Nat := [1, 1, 6, 1, 1, 1, 4, 1, 2, 4]
def baseStart_3302823 : Nat := 118140960795 + 3302823 * 2 ^ 59
def prefixEnd_3302823 : Nat := 4983230072969 + 3 ^ 40 * 3302823 * 2
def baseEnd_3302823 : Nat := 1130623810483224282348733

theorem tailTrace_3302823 : CollatzResearch.WordTrace tailWord_3302823 prefixEnd_3302823 1130623810483224282348733 := by
  unfold tailWord_3302823
  simp only [CollatzResearch.WordTrace]
  refine ⟨120463851313443823105025123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80309234208962548736683415 120463851313443823105025123)
  ·
    refine ⟨180695776970165734657537685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120463851313443823105025123 180695776970165734657537685)
    ·
      refine ⟨8470114545476518812072079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 180695776970165734657537685 8470114545476518812072079)
      ·
        refine ⟨12705171818214778218108119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8470114545476518812072079 12705171818214778218108119)
        ·
          refine ⟨19057757727322167327162179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12705171818214778218108119 19057757727322167327162179)
          ·
            refine ⟨28586636590983250990743269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19057757727322167327162179 28586636590983250990743269)
            ·
              refine ⟨5359994360809359560764363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28586636590983250990743269 5359994360809359560764363)
              ·
                refine ⟨8039991541214039341146545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5359994360809359560764363 8039991541214039341146545)
                ·
                  refine ⟨6029993655910529505859909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8039991541214039341146545 6029993655910529505859909)
                  ·
                    refine ⟨1130623810483224282348733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6029993655910529505859909 1130623810483224282348733)
                    ·
                      rfl

theorem cell22_3302823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 4, 1, 2, 4].length) (baseStart_3302823 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3302823 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3302823 prefixEnd_3302823 := by exact prefixLift 3302823
  have htrace : WordTrace (prefixWord ++ tailWord_3302823) baseStart_3302823 baseEnd_3302823 := by
    simpa [prefixWord, tailWord_3302823, baseEnd_3302823] using wordTrace_append hprefix tailTrace_3302823
  have hstable : (prefixWord ++ tailWord_3302823).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3302823).length < 2 ^ (prefixWord ++ tailWord_3302823).sum := by decide
  have hdescent : baseEnd_3302823 < baseStart_3302823 := by decide
  rcases family_descends (prefixWord ++ tailWord_3302823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3302844 : List Nat := [2, 2, 2, 4, 3, 1, 2, 2, 4]
def baseStart_3302844 : Nat := 118140960795 + 3302844 * 2 ^ 59
def prefixEnd_3302844 : Nat := 4983230072969 + 3 ^ 40 * 3302844 * 2
def baseEnd_3302844 : Nat := 376876999737462409191223

theorem tailTrace_3302844 : CollatzResearch.WordTrace tailWord_3302844 prefixEnd_3302844 376876999737462409191223 := by
  unfold tailWord_3302844
  simp only [CollatzResearch.WordTrace]
  refine ⟨60232308623183871845769793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80309744830911829127693057 60232308623183871845769793)
  ·
    refine ⟨45174231467387903884327345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60232308623183871845769793 45174231467387903884327345)
    ·
      refine ⟨33880673600540927913245509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45174231467387903884327345 33880673600540927913245509)
      ·
        refine ⟨6352626300101423983733533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33880673600540927913245509 6352626300101423983733533)
        ·
          refine ⟨2382234862538033993900075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6352626300101423983733533 2382234862538033993900075)
          ·
            refine ⟨3573352293807050990850113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2382234862538033993900075 3573352293807050990850113)
            ·
              refine ⟨2680014220355288243137585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3573352293807050990850113 2680014220355288243137585)
              ·
                refine ⟨2010010665266466182353189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2680014220355288243137585 2010010665266466182353189)
                ·
                  refine ⟨376876999737462409191223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2010010665266466182353189 376876999737462409191223)
                  ·
                    rfl

theorem cell22_3302844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 2, 2, 4].length) (baseStart_3302844 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3302844 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3302844 prefixEnd_3302844 := by exact prefixLift 3302844
  have htrace : WordTrace (prefixWord ++ tailWord_3302844) baseStart_3302844 baseEnd_3302844 := by
    simpa [prefixWord, tailWord_3302844, baseEnd_3302844] using wordTrace_append hprefix tailTrace_3302844
  have hstable : (prefixWord ++ tailWord_3302844).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3302844).length < 2 ^ (prefixWord ++ tailWord_3302844).sum := by decide
  have hdescent : baseEnd_3302844 < baseStart_3302844 := by decide
  rcases family_descends (prefixWord ++ tailWord_3302844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3302870 : List Nat := [5, 2, 1, 1, 1, 2, 1, 1, 5, 3]
def baseStart_3302870 : Nat := 118140960795 + 3302870 * 2 ^ 59
def prefixEnd_3302870 : Nat := 4983230072969 + 3 ^ 40 * 3302870 * 2
def baseEnd_3302870 : Nat := 1130639899543731826423589

theorem tailTrace_3302870 : CollatzResearch.WordTrace tailWord_3302870 prefixEnd_3302870 1130639899543731826423589 := by
  unfold tailWord_3302870
  simp only [CollatzResearch.WordTrace]
  refine ⟨7529097846517096883249129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 80310377029515700087990709 7529097846517096883249129)
  ·
    refine ⟨5646823384887822662436847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7529097846517096883249129 5646823384887822662436847)
    ·
      refine ⟨8470235077331733993655271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5646823384887822662436847 8470235077331733993655271)
      ·
        refine ⟨12705352615997600990482907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8470235077331733993655271 12705352615997600990482907)
        ·
          refine ⟨19058028923996401485724361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12705352615997600990482907 19058028923996401485724361)
          ·
            refine ⟨14293521692997301114293271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19058028923996401485724361 14293521692997301114293271)
            ·
              refine ⟨21440282539495951671439907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14293521692997301114293271 21440282539495951671439907)
              ·
                refine ⟨32160423809243927507159861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21440282539495951671439907 32160423809243927507159861)
                ·
                  refine ⟨3015039732116618203796237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32160423809243927507159861 3015039732116618203796237)
                  ·
                    refine ⟨1130639899543731826423589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3015039732116618203796237 1130639899543731826423589)
                    ·
                      rfl

theorem cell22_3302870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 1, 5, 3].length) (baseStart_3302870 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3302870 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3302870 prefixEnd_3302870 := by exact prefixLift 3302870
  have htrace : WordTrace (prefixWord ++ tailWord_3302870) baseStart_3302870 baseEnd_3302870 := by
    simpa [prefixWord, tailWord_3302870, baseEnd_3302870] using wordTrace_append hprefix tailTrace_3302870
  have hstable : (prefixWord ++ tailWord_3302870).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3302870).length < 2 ^ (prefixWord ++ tailWord_3302870).sum := by decide
  have hdescent : baseEnd_3302870 < baseStart_3302870 := by decide
  rcases family_descends (prefixWord ++ tailWord_3302870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3302887 : List Nat := [1, 1, 5, 2, 1, 3, 2, 3, 1, 3]
def baseStart_3302887 : Nat := 118140960795 + 3302887 * 2 ^ 59
def prefixEnd_3302887 : Nat := 4983230072969 + 3 ^ 40 * 3302887 * 2
def baseEnd_3302887 : Nat := 1130645718991149448748537

theorem tailTrace_3302887 : CollatzResearch.WordTrace tailWord_3302887 prefixEnd_3302887 1130645718991149448748537 := by
  unfold tailWord_3302887
  simp only [CollatzResearch.WordTrace]
  refine ⟨120466185585211962035354915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80310790390141308023569943 120466185585211962035354915)
  ·
    refine ⟨180699278377817943053032373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120466185585211962035354915 180699278377817943053032373)
    ·
      refine ⟨16940557347920432161221785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 180699278377817943053032373 16940557347920432161221785)
      ·
        refine ⟨12705418010940324120916339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16940557347920432161221785 12705418010940324120916339)
        ·
          refine ⟨19058127016410486181374509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12705418010940324120916339 19058127016410486181374509)
          ·
            refine ⟨7146797631153932318015441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19058127016410486181374509 7146797631153932318015441)
            ·
              refine ⟨5360098223365449238511581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7146797631153932318015441 5360098223365449238511581)
              ·
                refine ⟨2010036833762043464441843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5360098223365449238511581 2010036833762043464441843)
                ·
                  refine ⟨3015055250643065196662765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2010036833762043464441843 3015055250643065196662765)
                  ·
                    refine ⟨1130645718991149448748537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3015055250643065196662765 1130645718991149448748537)
                    ·
                      rfl

theorem cell22_3302887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 2, 3, 1, 3].length) (baseStart_3302887 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3302887 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3302887 prefixEnd_3302887 := by exact prefixLift 3302887
  have htrace : WordTrace (prefixWord ++ tailWord_3302887) baseStart_3302887 baseEnd_3302887 := by
    simpa [prefixWord, tailWord_3302887, baseEnd_3302887] using wordTrace_append hprefix tailTrace_3302887
  have hstable : (prefixWord ++ tailWord_3302887).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3302887).length < 2 ^ (prefixWord ++ tailWord_3302887).sum := by decide
  have hdescent : baseEnd_3302887 < baseStart_3302887 := by decide
  rcases family_descends (prefixWord ++ tailWord_3302887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3302898 : List Nat := [3, 2, 1, 4, 1, 1, 1, 2, 2, 5]
def baseStart_3302898 : Nat := 118140960795 + 3302898 * 2 ^ 59
def prefixEnd_3302898 : Nat := 4983230072969 + 3 ^ 40 * 3302898 * 2
def baseEnd_3302898 : Nat := 1130649484515949086723503

theorem tailTrace_3302898 : CollatzResearch.WordTrace tailWord_3302898 prefixEnd_3302898 1130649484515949086723503 := by
  unfold tailWord_3302898
  simp only [CollatzResearch.WordTrace]
  refine ⟨30116646697043027728501337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80311057858781407276003565 30116646697043027728501337)
  ·
    refine ⟨22587485022782270796376003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30116646697043027728501337 22587485022782270796376003)
    ·
      refine ⟨33881227534173406194564005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22587485022782270796376003 33881227534173406194564005)
      ·
        refine ⟨6352730162657513661480751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33881227534173406194564005 6352730162657513661480751)
        ·
          refine ⟨9529095243986270492221127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6352730162657513661480751 9529095243986270492221127)
          ·
            refine ⟨14293642865979405738331691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9529095243986270492221127 14293642865979405738331691)
            ·
              refine ⟨21440464298969108607497537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14293642865979405738331691 21440464298969108607497537)
              ·
                refine ⟨16080348224226831455623153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21440464298969108607497537 16080348224226831455623153)
                ·
                  refine ⟨12060261168170123591717365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16080348224226831455623153 12060261168170123591717365)
                  ·
                    refine ⟨1130649484515949086723503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12060261168170123591717365 1130649484515949086723503)
                    ·
                      rfl

theorem cell22_3302898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 2, 2, 5].length) (baseStart_3302898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3302898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3302898 prefixEnd_3302898 := by exact prefixLift 3302898
  have htrace : WordTrace (prefixWord ++ tailWord_3302898) baseStart_3302898 baseEnd_3302898 := by
    simpa [prefixWord, tailWord_3302898, baseEnd_3302898] using wordTrace_append hprefix tailTrace_3302898
  have hstable : (prefixWord ++ tailWord_3302898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3302898).length < 2 ^ (prefixWord ++ tailWord_3302898).sum := by decide
  have hdescent : baseEnd_3302898 < baseStart_3302898 := by decide
  rcases family_descends (prefixWord ++ tailWord_3302898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3302943 : List Nat := [1, 1, 2, 4, 1, 1, 3, 2, 4, 3]
def baseStart_3302943 : Nat := 118140960795 + 3302943 * 2 ^ 59
def prefixEnd_3302943 : Nat := 4983230072969 + 3 ^ 40 * 3302943 * 2
def baseEnd_3302943 : Nat := 1130664888935583969348365

theorem tailTrace_3302943 : CollatzResearch.WordTrace tailWord_3302943 prefixEnd_3302943 1130664888935583969348365 := by
  unfold tailWord_3302943
  simp only [CollatzResearch.WordTrace]
  refine ⟨120468228073009083599393483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80312152048672722399595655 120468228073009083599393483)
  ·
    refine ⟨180702342109513625399090225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120468228073009083599393483 180702342109513625399090225)
    ·
      refine ⟨135526756582135219049317669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180702342109513625399090225 135526756582135219049317669)
      ·
        refine ⟨25411266859150353571747063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 135526756582135219049317669 25411266859150353571747063)
        ·
          refine ⟨38116900288725530357620595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25411266859150353571747063 38116900288725530357620595)
          ·
            refine ⟨57175350433088295536430893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38116900288725530357620595 57175350433088295536430893)
            ·
              refine ⟨21440756412408110826161585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57175350433088295536430893 21440756412408110826161585)
              ·
                refine ⟨16080567309306083119621189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21440756412408110826161585 16080567309306083119621189)
                ·
                  refine ⟨3015106370494890584928973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16080567309306083119621189 3015106370494890584928973)
                  ·
                    refine ⟨1130664888935583969348365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3015106370494890584928973 1130664888935583969348365)
                    ·
                      rfl

theorem cell22_3302943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 2, 4, 3].length) (baseStart_3302943 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3302943 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3302943 prefixEnd_3302943 := by exact prefixLift 3302943
  have htrace : WordTrace (prefixWord ++ tailWord_3302943) baseStart_3302943 baseEnd_3302943 := by
    simpa [prefixWord, tailWord_3302943, baseEnd_3302943] using wordTrace_append hprefix tailTrace_3302943
  have hstable : (prefixWord ++ tailWord_3302943).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3302943).length < 2 ^ (prefixWord ++ tailWord_3302943).sum := by decide
  have hdescent : baseEnd_3302943 < baseStart_3302943 := by decide
  rcases family_descends (prefixWord ++ tailWord_3302943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3302945 : List Nat := [1, 2, 3, 2, 2, 2, 3, 3, 4]
def baseStart_3302945 : Nat := 118140960795 + 3302945 * 2 ^ 59
def prefixEnd_3302945 : Nat := 4983230072969 + 3 ^ 40 * 3302945 * 2
def baseEnd_3302945 : Nat := 376888524525485543599453

theorem tailTrace_3302945 : CollatzResearch.WordTrace tailWord_3302945 prefixEnd_3302945 376888524525485543599453 := by
  unfold tailWord_3302945
  simp only [CollatzResearch.WordTrace]
  refine ⟨120468301019001837940966289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80312200679334558627310859 120468301019001837940966289)
  ·
    refine ⟨90351225764251378455724717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120468301019001837940966289 90351225764251378455724717)
    ·
      refine ⟨33881709661594266920896769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90351225764251378455724717 33881709661594266920896769)
      ·
        refine ⟨25411282246195700190672577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33881709661594266920896769 25411282246195700190672577)
        ·
          refine ⟨19058461684646775143004433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25411282246195700190672577 19058461684646775143004433)
          ·
            refine ⟨14293846263485081357253325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19058461684646775143004433 14293846263485081357253325)
            ·
              refine ⟨5360192348806905508969997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14293846263485081357253325 5360192348806905508969997)
              ·
                refine ⟨2010072130802589565863749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5360192348806905508969997 2010072130802589565863749)
                ·
                  refine ⟨376888524525485543599453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2010072130802589565863749 376888524525485543599453)
                  ·
                    rfl

theorem cell22_3302945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 3, 3, 4].length) (baseStart_3302945 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3302945 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3302945 prefixEnd_3302945 := by exact prefixLift 3302945
  have htrace : WordTrace (prefixWord ++ tailWord_3302945) baseStart_3302945 baseEnd_3302945 := by
    simpa [prefixWord, tailWord_3302945, baseEnd_3302945] using wordTrace_append hprefix tailTrace_3302945
  have hstable : (prefixWord ++ tailWord_3302945).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3302945).length < 2 ^ (prefixWord ++ tailWord_3302945).sum := by decide
  have hdescent : baseEnd_3302945 < baseStart_3302945 := by decide
  rcases family_descends (prefixWord ++ tailWord_3302945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3303001 : List Nat := [1, 2, 1, 2, 2, 1, 1, 3, 9]
def baseStart_3303001 : Nat := 118140960795 + 3303001 * 2 ^ 59
def prefixEnd_3303001 : Nat := 4983230072969 + 3 ^ 40 * 3303001 * 2
def baseEnd_3303001 : Nat := 376894914506963717132729

theorem tailTrace_3303001 : CollatzResearch.WordTrace tailWord_3303001 prefixEnd_3303001 376894914506963717132729 := by
  unfold tailWord_3303001
  simp only [CollatzResearch.WordTrace]
  refine ⟨120470343506798959505004857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80313562337865973003336571 120470343506798959505004857)
  ·
    refine ⟨90352757630099219628753643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120470343506798959505004857 90352757630099219628753643)
    ·
      refine ⟨135529136445148829443130465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90352757630099219628753643 135529136445148829443130465)
      ·
        refine ⟨101646852333861622082347849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135529136445148829443130465 101646852333861622082347849)
        ·
          refine ⟨76235139250396216561760887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101646852333861622082347849 76235139250396216561760887)
          ·
            refine ⟨114352708875594324842641331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76235139250396216561760887 114352708875594324842641331)
            ·
              refine ⟨171529063313391487263961997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114352708875594324842641331 171529063313391487263961997)
              ·
                refine ⟨64323398742521807723985749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 171529063313391487263961997 64323398742521807723985749)
                ·
                  refine ⟨376894914506963717132729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 64323398742521807723985749 376894914506963717132729)
                  ·
                    rfl

theorem cell22_3303001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 3, 9].length) (baseStart_3303001 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3303001 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3303001 prefixEnd_3303001 := by exact prefixLift 3303001
  have htrace : WordTrace (prefixWord ++ tailWord_3303001) baseStart_3303001 baseEnd_3303001 := by
    simpa [prefixWord, tailWord_3303001, baseEnd_3303001] using wordTrace_append hprefix tailTrace_3303001
  have hstable : (prefixWord ++ tailWord_3303001).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3303001).length < 2 ^ (prefixWord ++ tailWord_3303001).sum := by decide
  have hdescent : baseEnd_3303001 < baseStart_3303001 := by decide
  rcases family_descends (prefixWord ++ tailWord_3303001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3303033 : List Nat := [1, 2, 1, 3, 3, 1, 3, 1, 2, 5]
def baseStart_3303033 : Nat := 118140960795 + 3303033 * 2 ^ 59
def prefixEnd_3303033 : Nat := 4983230072969 + 3 ^ 40 * 3303033 * 2
def baseEnd_3303033 : Nat := 1130695697774853734598089

theorem tailTrace_3303033 : CollatzResearch.WordTrace tailWord_3303033 prefixEnd_3303033 1130695697774853734598089 := by
  unfold tailWord_3303033
  simp only [CollatzResearch.WordTrace]
  refine ⟨120471510642683028970169753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80314340428455352646779835 120471510642683028970169753)
  ·
    refine ⟨90353632982012271727627315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120471510642683028970169753 90353632982012271727627315)
    ·
      refine ⟨135530449473018407591440973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90353632982012271727627315 135530449473018407591440973)
      ·
        refine ⟨50823918552381902846790365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135530449473018407591440973 50823918552381902846790365)
        ·
          refine ⟨19058969457143213567546387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50823918552381902846790365 19058969457143213567546387)
          ·
            refine ⟨28588454185714820351319581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19058969457143213567546387 28588454185714820351319581)
            ·
              refine ⟨10720670319643057631744843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28588454185714820351319581 10720670319643057631744843)
              ·
                refine ⟨16081005479464586447617265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10720670319643057631744843 16081005479464586447617265)
                ·
                  refine ⟨12060754109598439835712949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16081005479464586447617265 12060754109598439835712949)
                  ·
                    refine ⟨1130695697774853734598089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12060754109598439835712949 1130695697774853734598089)
                    ·
                      rfl

theorem cell22_3303033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 3, 1, 2, 5].length) (baseStart_3303033 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3303033 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3303033 prefixEnd_3303033 := by exact prefixLift 3303033
  have htrace : WordTrace (prefixWord ++ tailWord_3303033) baseStart_3303033 baseEnd_3303033 := by
    simpa [prefixWord, tailWord_3303033, baseEnd_3303033] using wordTrace_append hprefix tailTrace_3303033
  have hstable : (prefixWord ++ tailWord_3303033).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3303033).length < 2 ^ (prefixWord ++ tailWord_3303033).sum := by decide
  have hdescent : baseEnd_3303033 < baseStart_3303033 := by decide
  rcases family_descends (prefixWord ++ tailWord_3303033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3303095 : List Nat := [1, 1, 3, 1, 5, 1, 3, 1, 1, 5]
def baseStart_3303095 : Nat := 118140960795 + 3303095 * 2 ^ 59
def prefixEnd_3303095 : Nat := 4983230072969 + 3 ^ 40 * 3303095 * 2
def baseEnd_3303095 : Nat := 1130716921641906239547899

theorem tailTrace_3303095 : CollatzResearch.WordTrace tailWord_3303095 prefixEnd_3303095 1130716921641906239547899 := by
  unfold tailWord_3303095
  simp only [CollatzResearch.WordTrace]
  refine ⟨120473771968458413558926739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80315847978972275705951159 120473771968458413558926739)
  ·
    refine ⟨180710657952687620338390109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120473771968458413558926739 180710657952687620338390109)
    ·
      refine ⟨67766496732257857626896291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 180710657952687620338390109 67766496732257857626896291)
      ·
        refine ⟨101649745098386786440344437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67766496732257857626896291 101649745098386786440344437)
        ·
          refine ⟨9529663602973761228782291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 101649745098386786440344437 9529663602973761228782291)
          ·
            refine ⟨14294495404460641843173437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9529663602973761228782291 14294495404460641843173437)
            ·
              refine ⟨5360435776672740691190039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14294495404460641843173437 5360435776672740691190039)
              ·
                refine ⟨8040653665009111036785059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5360435776672740691190039 8040653665009111036785059)
                ·
                  refine ⟨12060980497513666555177589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8040653665009111036785059 12060980497513666555177589)
                  ·
                    refine ⟨1130716921641906239547899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12060980497513666555177589 1130716921641906239547899)
                    ·
                      rfl

theorem cell22_3303095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 3, 1, 1, 5].length) (baseStart_3303095 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3303095 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3303095 prefixEnd_3303095 := by exact prefixLift 3303095
  have htrace : WordTrace (prefixWord ++ tailWord_3303095) baseStart_3303095 baseEnd_3303095 := by
    simpa [prefixWord, tailWord_3303095, baseEnd_3303095] using wordTrace_append hprefix tailTrace_3303095
  have hstable : (prefixWord ++ tailWord_3303095).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3303095).length < 2 ^ (prefixWord ++ tailWord_3303095).sum := by decide
  have hdescent : baseEnd_3303095 < baseStart_3303095 := by decide
  rcases family_descends (prefixWord ++ tailWord_3303095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3303114 : List Nat := [3, 1, 2, 1, 5, 2, 1, 3, 4]
def baseStart_3303114 : Nat := 118140960795 + 3303114 * 2 ^ 59
def prefixEnd_3303114 : Nat := 4983230072969 + 3 ^ 40 * 3303114 * 2
def baseEnd_3303114 : Nat := 376907808576732174440947

theorem tailTrace_3303114 : CollatzResearch.WordTrace tailWord_3303114 prefixEnd_3303114 376907808576732174440947 := by
  unfold tailWord_3303114
  simp only [CollatzResearch.WordTrace]
  refine ⟨30118616238847394950967099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80316309970259719869245597 30118616238847394950967099)
  ·
    refine ⟨45177924358271092426450649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30118616238847394950967099 45177924358271092426450649)
    ·
      refine ⟨33883443268703319319837987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45177924358271092426450649 33883443268703319319837987)
      ·
        refine ⟨50825164903054978979756981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33883443268703319319837987 50825164903054978979756981)
        ·
          refine ⟨4764859209661404279352217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 50825164903054978979756981 4764859209661404279352217)
          ·
            refine ⟨3573644407246053209514163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4764859209661404279352217 3573644407246053209514163)
            ·
              refine ⟨5360466610869079814271245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3573644407246053209514163 5360466610869079814271245)
              ·
                refine ⟨2010174979075904930351717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5360466610869079814271245 2010174979075904930351717)
                ·
                  refine ⟨376907808576732174440947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2010174979075904930351717 376907808576732174440947)
                  ·
                    rfl

theorem cell22_3303114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 1, 3, 4].length) (baseStart_3303114 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3303114 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3303114 prefixEnd_3303114 := by exact prefixLift 3303114
  have htrace : WordTrace (prefixWord ++ tailWord_3303114) baseStart_3303114 baseEnd_3303114 := by
    simpa [prefixWord, tailWord_3303114, baseEnd_3303114] using wordTrace_append hprefix tailTrace_3303114
  have hstable : (prefixWord ++ tailWord_3303114).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3303114).length < 2 ^ (prefixWord ++ tailWord_3303114).sum := by decide
  have hdescent : baseEnd_3303114 < baseStart_3303114 := by decide
  rcases family_descends (prefixWord ++ tailWord_3303114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3303168 : List Nat := [2, 1, 1, 2, 1, 1, 2, 4, 1, 7]
def baseStart_3303168 : Nat := 118140960795 + 3303168 * 2 ^ 59
def prefixEnd_3303168 : Nat := 4983230072969 + 3 ^ 40 * 3303168 * 2
def baseEnd_3303168 : Nat := 1130741911033758382472675

theorem tailTrace_3303168 : CollatzResearch.WordTrace tailWord_3303168 prefixEnd_3303168 1130741911033758382472675 := by
  unfold tailWord_3303168
  simp only [CollatzResearch.WordTrace]
  refine ⟨60238217248596973513167079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80317622998129298017556105 60238217248596973513167079)
  ·
    refine ⟨90357325872895460269750619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60238217248596973513167079 90357325872895460269750619)
    ·
      refine ⟨135535988809343190404625929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90357325872895460269750619 135535988809343190404625929)
      ·
        refine ⟨101651991607007392803469447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135535988809343190404625929 101651991607007392803469447)
        ·
          refine ⟨152477987410511089205204171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101651991607007392803469447 152477987410511089205204171)
          ·
            refine ⟨228716981115766633807806257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152477987410511089205204171 228716981115766633807806257)
            ·
              refine ⟨171537735836824975355854693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 228716981115766633807806257 171537735836824975355854693)
              ·
                refine ⟨32163325469404682879222755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 171537735836824975355854693 32163325469404682879222755)
                ·
                  refine ⟨48244988204107024318834133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32163325469404682879222755 48244988204107024318834133)
                  ·
                    refine ⟨1130741911033758382472675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48244988204107024318834133 1130741911033758382472675)
                    ·
                      rfl

theorem cell22_3303168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 4, 1, 7].length) (baseStart_3303168 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3303168 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3303168 prefixEnd_3303168 := by exact prefixLift 3303168
  have htrace : WordTrace (prefixWord ++ tailWord_3303168) baseStart_3303168 baseEnd_3303168 := by
    simpa [prefixWord, tailWord_3303168, baseEnd_3303168] using wordTrace_append hprefix tailTrace_3303168
  have hstable : (prefixWord ++ tailWord_3303168).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3303168).length < 2 ^ (prefixWord ++ tailWord_3303168).sum := by decide
  have hdescent : baseEnd_3303168 < baseStart_3303168 := by decide
  rcases family_descends (prefixWord ++ tailWord_3303168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3303191 : List Nat := [1, 1, 3, 4, 2, 1, 4, 2, 1, 3]
def baseStart_3303191 : Nat := 118140960795 + 3303191 * 2 ^ 59
def prefixEnd_3303191 : Nat := 4983230072969 + 3 ^ 40 * 3303191 * 2
def baseEnd_3303191 : Nat := 1130749784403793989147605

theorem tailTrace_3303191 : CollatzResearch.WordTrace tailWord_3303191 prefixEnd_3303191 1130749784403793989147605 := by
  unfold tailWord_3303191
  simp only [CollatzResearch.WordTrace]
  refine ⟨120477273376110621954421427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80318182250740414636280951 120477273376110621954421427)
  ·
    refine ⟨180715910064165932931632141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120477273376110621954421427 180715910064165932931632141)
    ·
      refine ⟨67768466274062224849362053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 180715910064165932931632141 67768466274062224849362053)
      ·
        refine ⟨12706587426386667159255385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67768466274062224849362053 12706587426386667159255385)
        ·
          refine ⟨9529940569790000369441539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12706587426386667159255385 9529940569790000369441539)
          ·
            refine ⟨14294910854685000554162309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9529940569790000369441539 14294910854685000554162309)
            ·
              refine ⟨2680295785253437603905433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14294910854685000554162309 2680295785253437603905433)
              ·
                refine ⟨2010221838940078202929075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2680295785253437603905433 2010221838940078202929075)
                ·
                  refine ⟨3015332758410117304393613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2010221838940078202929075 3015332758410117304393613)
                  ·
                    refine ⟨1130749784403793989147605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3015332758410117304393613 1130749784403793989147605)
                    ·
                      rfl

theorem cell22_3303191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 4, 2, 1, 3].length) (baseStart_3303191 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3303191 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3303191 prefixEnd_3303191 := by exact prefixLift 3303191
  have htrace : WordTrace (prefixWord ++ tailWord_3303191) baseStart_3303191 baseEnd_3303191 := by
    simpa [prefixWord, tailWord_3303191, baseEnd_3303191] using wordTrace_append hprefix tailTrace_3303191
  have hstable : (prefixWord ++ tailWord_3303191).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3303191).length < 2 ^ (prefixWord ++ tailWord_3303191).sum := by decide
  have hdescent : baseEnd_3303191 < baseStart_3303191 := by decide
  rcases family_descends (prefixWord ++ tailWord_3303191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3303200 : List Nat := [2, 1, 1, 5, 1, 1, 1, 1, 5, 4]
def baseStart_3303200 : Nat := 118140960795 + 3303200 * 2 ^ 59
def prefixEnd_3303200 : Nat := 4983230072969 + 3 ^ 40 * 3303200 * 2
def baseEnd_3303200 : Nat := 1130752865287720965672577

theorem tailTrace_3303200 : CollatzResearch.WordTrace tailWord_3303200 prefixEnd_3303200 1130752865287720965672577 := by
  unfold tailWord_3303200
  simp only [CollatzResearch.WordTrace]
  refine ⟨60238800816539008245749527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80318401088718677660999369 60238800816539008245749527)
  ·
    refine ⟨90358201224808512368624291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60238800816539008245749527 90358201224808512368624291)
    ·
      refine ⟨135537301837212768552936437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90358201224808512368624291 135537301837212768552936437)
      ·
        refine ⟨12706622047238697051837791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 135537301837212768552936437 12706622047238697051837791)
        ·
          refine ⟨19059933070858045577756687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12706622047238697051837791 19059933070858045577756687)
          ·
            refine ⟨28589899606287068366635031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19059933070858045577756687 28589899606287068366635031)
            ·
              refine ⟨42884849409430602549952547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28589899606287068366635031 42884849409430602549952547)
              ·
                refine ⟨64327274114145903824928821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42884849409430602549952547 64327274114145903824928821)
                ·
                  refine ⟨6030681948201178483587077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 64327274114145903824928821 6030681948201178483587077)
                  ·
                    refine ⟨1130752865287720965672577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6030681948201178483587077 1130752865287720965672577)
                    ·
                      rfl

theorem cell22_3303200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 1, 5, 4].length) (baseStart_3303200 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3303200 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3303200 prefixEnd_3303200 := by exact prefixLift 3303200
  have htrace : WordTrace (prefixWord ++ tailWord_3303200) baseStart_3303200 baseEnd_3303200 := by
    simpa [prefixWord, tailWord_3303200, baseEnd_3303200] using wordTrace_append hprefix tailTrace_3303200
  have hstable : (prefixWord ++ tailWord_3303200).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3303200).length < 2 ^ (prefixWord ++ tailWord_3303200).sum := by decide
  have hdescent : baseEnd_3303200 < baseStart_3303200 := by decide
  rcases family_descends (prefixWord ++ tailWord_3303200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3303277 : List Nat := [1, 5, 1, 1, 1, 1, 6, 6]
def baseStart_3303277 : Nat := 118140960795 + 3303277 * 2 ^ 59
def prefixEnd_3303277 : Nat := 4983230072969 + 3 ^ 40 * 3303277 * 2
def baseEnd_3303277 : Nat := 125642135995702047944149

theorem tailTrace_3303277 : CollatzResearch.WordTrace tailWord_3303277 prefixEnd_3303277 125642135995702047944149 := by
  unfold tailWord_3303277
  simp only [CollatzResearch.WordTrace]
  refine ⟨120480410053799058642052085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80320273369199372428034723 120480410053799058642052085)
  ·
    refine ⟨11295038442543661747692383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 120480410053799058642052085 11295038442543661747692383)
    ·
      refine ⟨16942557663815492621538575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11295038442543661747692383 16942557663815492621538575)
      ·
        refine ⟨25413836495723238932307863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16942557663815492621538575 25413836495723238932307863)
        ·
          refine ⟨38120754743584858398461795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25413836495723238932307863 38120754743584858398461795)
          ·
            refine ⟨57181132115377287597692693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38120754743584858398461795 57181132115377287597692693)
            ·
              refine ⟨2680365567908310356141845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 57181132115377287597692693 2680365567908310356141845)
              ·
                refine ⟨125642135995702047944149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2680365567908310356141845 125642135995702047944149)
                ·
                  rfl

theorem cell22_3303277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 6, 6].length) (baseStart_3303277 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3303277 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3303277 prefixEnd_3303277 := by exact prefixLift 3303277
  have htrace : WordTrace (prefixWord ++ tailWord_3303277) baseStart_3303277 baseEnd_3303277 := by
    simpa [prefixWord, tailWord_3303277, baseEnd_3303277] using wordTrace_append hprefix tailTrace_3303277
  have hstable : (prefixWord ++ tailWord_3303277).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3303277).length < 2 ^ (prefixWord ++ tailWord_3303277).sum := by decide
  have hdescent : baseEnd_3303277 < baseStart_3303277 := by decide
  rcases family_descends (prefixWord ++ tailWord_3303277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3303294 : List Nat := [4, 2, 3, 1, 1, 3, 8]
def baseStart_3303294 : Nat := 118140960795 + 3303294 * 2 ^ 59
def prefixEnd_3303294 : Nat := 4983230072969 + 3 ^ 40 * 3303294 * 2
def baseEnd_3303294 : Nat := 41880927533656890882307

theorem tailTrace_3303294 : CollatzResearch.WordTrace tailWord_3303294 prefixEnd_3303294 41880927533656890882307 := by
  unfold tailWord_3303294
  simp only [CollatzResearch.WordTrace]
  refine ⟨15060128761842183818177617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80320686729824980363613957 15060128761842183818177617)
  ·
    refine ⟨11295096571381637863633213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15060128761842183818177617 11295096571381637863633213)
    ·
      refine ⟨4235661214268114198862455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11295096571381637863633213 4235661214268114198862455)
      ·
        refine ⟨6353491821402171298293683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4235661214268114198862455 6353491821402171298293683)
        ·
          refine ⟨9530237732103256947440525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6353491821402171298293683 9530237732103256947440525)
          ·
            refine ⟨3573839149538721355290197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9530237732103256947440525 3573839149538721355290197)
            ·
              refine ⟨41880927533656890882307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3573839149538721355290197 41880927533656890882307)
              ·
                rfl

theorem cell22_3303294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 8].length) (baseStart_3303294 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3303294 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3303294 prefixEnd_3303294 := by exact prefixLift 3303294
  have htrace : WordTrace (prefixWord ++ tailWord_3303294) baseStart_3303294 baseEnd_3303294 := by
    simpa [prefixWord, tailWord_3303294, baseEnd_3303294] using wordTrace_append hprefix tailTrace_3303294
  have hstable : (prefixWord ++ tailWord_3303294).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3303294).length < 2 ^ (prefixWord ++ tailWord_3303294).sum := by decide
  have hdescent : baseEnd_3303294 < baseStart_3303294 := by decide
  rcases family_descends (prefixWord ++ tailWord_3303294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3303305 : List Nat := [1, 2, 1, 1, 5, 1, 1, 3, 7]
def baseStart_3303305 : Nat := 118140960795 + 3303305 * 2 ^ 59
def prefixEnd_3303305 : Nat := 4983230072969 + 3 ^ 40 * 3303305 * 2
def baseEnd_3303305 : Nat := 376929602977845230599085

theorem tailTrace_3303305 : CollatzResearch.WordTrace tailWord_3303305 prefixEnd_3303305 376929602977845230599085 := by
  unfold tailWord_3303305
  simp only [CollatzResearch.WordTrace]
  refine ⟨120481431297697619424071369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80320954198465079616047579 120481431297697619424071369)
  ·
    refine ⟨90361073473273214568053527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120481431297697619424071369 90361073473273214568053527)
    ·
      refine ⟨135541610209909821852080291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90361073473273214568053527 135541610209909821852080291)
      ·
        refine ⟨203312415314864732778120437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135541610209909821852080291 203312415314864732778120437)
        ·
          refine ⟨19060538935768568697948791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 203312415314864732778120437 19060538935768568697948791)
          ·
            refine ⟨28590808403652853046923187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19060538935768568697948791 28590808403652853046923187)
            ·
              refine ⟨42886212605479279570384781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28590808403652853046923187 42886212605479279570384781)
              ·
                refine ⟨16082329727054729838894293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42886212605479279570384781 16082329727054729838894293)
                ·
                  refine ⟨376929602977845230599085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16082329727054729838894293 376929602977845230599085)
                  ·
                    rfl

theorem cell22_3303305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 3, 7].length) (baseStart_3303305 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3303305 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3303305 prefixEnd_3303305 := by exact prefixLift 3303305
  have htrace : WordTrace (prefixWord ++ tailWord_3303305) baseStart_3303305 baseEnd_3303305 := by
    simpa [prefixWord, tailWord_3303305, baseEnd_3303305] using wordTrace_append hprefix tailTrace_3303305
  have hstable : (prefixWord ++ tailWord_3303305).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3303305).length < 2 ^ (prefixWord ++ tailWord_3303305).sum := by decide
  have hdescent : baseEnd_3303305 < baseStart_3303305 := by decide
  rcases family_descends (prefixWord ++ tailWord_3303305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3303356 : List Nat := [2, 2, 2, 5, 1, 1, 2, 2, 5]
def baseStart_3303356 : Nat := 118140960795 + 3303356 * 2 ^ 59
def prefixEnd_3303356 : Nat := 4983230072969 + 3 ^ 40 * 3303356 * 2
def baseEnd_3303356 : Nat := 376935422425262852924033

theorem tailTrace_3303356 : CollatzResearch.WordTrace tailWord_3303356 prefixEnd_3303356 376935422425262852924033 := by
  unfold tailWord_3303356
  simp only [CollatzResearch.WordTrace]
  refine ⟨60241645710256427567088961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80322194280341903422785281 60241645710256427567088961)
  ·
    refine ⟨45181234282692320675316721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60241645710256427567088961 45181234282692320675316721)
    ·
      refine ⟨33885925712019240506487541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45181234282692320675316721 33885925712019240506487541)
      ·
        refine ⟨3176805535501803797483207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 33885925712019240506487541 3176805535501803797483207)
        ·
          refine ⟨4765208303252705696224811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3176805535501803797483207 4765208303252705696224811)
          ·
            refine ⟨7147812454879058544337217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4765208303252705696224811 7147812454879058544337217)
            ·
              refine ⟨5360859341159293908252913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7147812454879058544337217 5360859341159293908252913)
              ·
                refine ⟨4020644505869470431189685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5360859341159293908252913 4020644505869470431189685)
                ·
                  refine ⟨376935422425262852924033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4020644505869470431189685 376935422425262852924033)
                  ·
                    rfl

theorem cell22_3303356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 2, 2, 5].length) (baseStart_3303356 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3303356 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3303356 prefixEnd_3303356 := by exact prefixLift 3303356
  have htrace : WordTrace (prefixWord ++ tailWord_3303356) baseStart_3303356 baseEnd_3303356 := by
    simpa [prefixWord, tailWord_3303356, baseEnd_3303356] using wordTrace_append hprefix tailTrace_3303356
  have hstable : (prefixWord ++ tailWord_3303356).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3303356).length < 2 ^ (prefixWord ++ tailWord_3303356).sum := by decide
  have hdescent : baseEnd_3303356 < baseStart_3303356 := by decide
  rcases family_descends (prefixWord ++ tailWord_3303356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3303534 : List Nat := [4, 1, 2, 2, 1, 1, 1, 2, 3, 5]
def baseStart_3303534 : Nat := 118140960795 + 3303534 * 2 ^ 59
def prefixEnd_3303534 : Nat := 4983230072969 + 3 ^ 40 * 3303534 * 2
def baseEnd_3303534 : Nat := 1130867200313455427821553

theorem tailTrace_3303534 : CollatzResearch.WordTrace tailWord_3303534 prefixEnd_3303534 1130867200313455427821553 := by
  unfold tailWord_3303534
  simp only [CollatzResearch.WordTrace]
  refine ⟨15061222951733498941769707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80326522409245327689438437 15061222951733498941769707)
  ·
    refine ⟨22591834427600248412654561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15061222951733498941769707 22591834427600248412654561)
    ·
      refine ⟨16943875820700186309490921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22591834427600248412654561 16943875820700186309490921)
      ·
        refine ⟨12707906865525139732118191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16943875820700186309490921 12707906865525139732118191)
        ·
          refine ⟨19061860298287709598177287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12707906865525139732118191 19061860298287709598177287)
          ·
            refine ⟨28592790447431564397265931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19061860298287709598177287 28592790447431564397265931)
            ·
              refine ⟨42889185671147346595898897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28592790447431564397265931 42889185671147346595898897)
              ·
                refine ⟨32166889253360509946924173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42889185671147346595898897 32166889253360509946924173)
                ·
                  refine ⟨12062583470010191230096565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32166889253360509946924173 12062583470010191230096565)
                  ·
                    refine ⟨1130867200313455427821553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12062583470010191230096565 1130867200313455427821553)
                    ·
                      rfl

theorem cell22_3303534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 2, 3, 5].length) (baseStart_3303534 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3303534 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3303534 prefixEnd_3303534 := by exact prefixLift 3303534
  have htrace : WordTrace (prefixWord ++ tailWord_3303534) baseStart_3303534 baseEnd_3303534 := by
    simpa [prefixWord, tailWord_3303534, baseEnd_3303534] using wordTrace_append hprefix tailTrace_3303534
  have hstable : (prefixWord ++ tailWord_3303534).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3303534).length < 2 ^ (prefixWord ++ tailWord_3303534).sum := by decide
  have hdescent : baseEnd_3303534 < baseStart_3303534 := by decide
  rcases family_descends (prefixWord ++ tailWord_3303534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3303536 : List Nat := [2, 1, 1, 1, 5, 3, 1, 4, 4]
def baseStart_3303536 : Nat := 118140960795 + 3303536 * 2 ^ 59
def prefixEnd_3303536 : Nat := 4983230072969 + 3 ^ 40 * 3303536 * 2
def baseEnd_3303536 : Nat := 376955961651442696423849

theorem tailTrace_3303536 : CollatzResearch.WordTrace tailWord_3303536 prefixEnd_3303536 376955961651442696423849 := by
  unfold tailWord_3303536
  simp only [CollatzResearch.WordTrace]
  refine ⟨60244928279930372937865231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80326571039907163917153641 60244928279930372937865231)
  ·
    refine ⟨90367392419895559406797847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60244928279930372937865231 90367392419895559406797847)
    ·
      refine ⟨135551088629843339110196771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90367392419895559406797847 135551088629843339110196771)
      ·
        refine ⟨203326632944765008665295157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135551088629843339110196771 203326632944765008665295157)
        ·
          refine ⟨19061871838571719562371421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 203326632944765008665295157 19061871838571719562371421)
          ·
            refine ⟨7148201939464394835889283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19061871838571719562371421 7148201939464394835889283)
            ·
              refine ⟨10722302909196592253833925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7148201939464394835889283 10722302909196592253833925)
              ·
                refine ⟨2010431795474361047593861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10722302909196592253833925 2010431795474361047593861)
                ·
                  refine ⟨376955961651442696423849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2010431795474361047593861 376955961651442696423849)
                  ·
                    rfl

theorem cell22_3303536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 1, 4, 4].length) (baseStart_3303536 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3303536 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3303536 prefixEnd_3303536 := by exact prefixLift 3303536
  have htrace : WordTrace (prefixWord ++ tailWord_3303536) baseStart_3303536 baseEnd_3303536 := by
    simpa [prefixWord, tailWord_3303536, baseEnd_3303536] using wordTrace_append hprefix tailTrace_3303536
  have hstable : (prefixWord ++ tailWord_3303536).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3303536).length < 2 ^ (prefixWord ++ tailWord_3303536).sum := by decide
  have hdescent : baseEnd_3303536 < baseStart_3303536 := by decide
  rcases family_descends (prefixWord ++ tailWord_3303536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3303566 : List Nat := [4, 1, 1, 3, 3, 1, 1, 1, 1, 6]
def baseStart_3303566 : Nat := 118140960795 + 3303566 * 2 ^ 59
def prefixEnd_3303566 : Nat := 4983230072969 + 3 ^ 40 * 3303566 * 2
def baseEnd_3303566 : Nat := 1130878154567418011021455

theorem tailTrace_3303566 : CollatzResearch.WordTrace tailWord_3303566 prefixEnd_3303566 1130878154567418011021455 := by
  unfold tailWord_3303566
  simp only [CollatzResearch.WordTrace]
  refine ⟨15061368843719007624915319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80327300499834707332881701 15061368843719007624915319)
  ·
    refine ⟨22592053265578511437372979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15061368843719007624915319 22592053265578511437372979)
    ·
      refine ⟨33888079898367767156059469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22592053265578511437372979 33888079898367767156059469)
      ·
        refine ⟨12708029961887912683522301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33888079898367767156059469 12708029961887912683522301)
        ·
          refine ⟨4765511235707967256320863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12708029961887912683522301 4765511235707967256320863)
          ·
            refine ⟨7148266853561950884481295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4765511235707967256320863 7148266853561950884481295)
            ·
              refine ⟨10722400280342926326721943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7148266853561950884481295 10722400280342926326721943)
              ·
                refine ⟨16083600420514389490082915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10722400280342926326721943 16083600420514389490082915)
                ·
                  refine ⟨24125400630771584235124373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16083600420514389490082915 24125400630771584235124373)
                  ·
                    refine ⟨1130878154567418011021455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24125400630771584235124373 1130878154567418011021455)
                    ·
                      rfl

theorem cell22_3303566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 1, 1, 1, 6].length) (baseStart_3303566 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3303566 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3303566 prefixEnd_3303566 := by exact prefixLift 3303566
  have htrace : WordTrace (prefixWord ++ tailWord_3303566) baseStart_3303566 baseEnd_3303566 := by
    simpa [prefixWord, tailWord_3303566, baseEnd_3303566] using wordTrace_append hprefix tailTrace_3303566
  have hstable : (prefixWord ++ tailWord_3303566).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3303566).length < 2 ^ (prefixWord ++ tailWord_3303566).sum := by decide
  have hdescent : baseEnd_3303566 < baseStart_3303566 := by decide
  rcases family_descends (prefixWord ++ tailWord_3303566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3303572 : List Nat := [2, 4, 2, 3, 1, 2, 2, 1, 1, 4]
def baseStart_3303572 : Nat := 118140960795 + 3303572 * 2 ^ 59
def prefixEnd_3303572 : Nat := 4983230072969 + 3 ^ 40 * 3303572 * 2
def baseEnd_3303572 : Nat := 1130880208490035995371437

theorem tailTrace_3303572 : CollatzResearch.WordTrace tailWord_3303572 prefixEnd_3303572 1130880208490035995371437 := by
  unfold tailWord_3303572
  simp only [CollatzResearch.WordTrace]
  refine ⟨60245584793865162012020485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80327446391820216016027313 60245584793865162012020485)
  ·
    refine ⟨11296047148849717877253841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60245584793865162012020485 11296047148849717877253841)
    ·
      refine ⟨8472035361637288407940381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11296047148849717877253841 8472035361637288407940381)
      ·
        refine ⟨3177013260613983152977643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8472035361637288407940381 3177013260613983152977643)
        ·
          refine ⟨4765519890920974729466465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3177013260613983152977643 4765519890920974729466465)
          ·
            refine ⟨3574139918190731047099849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4765519890920974729466465 3574139918190731047099849)
            ·
              refine ⟨2680604938643048285324887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3574139918190731047099849 2680604938643048285324887)
              ·
                refine ⟨4020907407964572427987331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2680604938643048285324887 4020907407964572427987331)
                ·
                  refine ⟨6031361111946858641980997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4020907407964572427987331 6031361111946858641980997)
                  ·
                    refine ⟨1130880208490035995371437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6031361111946858641980997 1130880208490035995371437)
                    ·
                      rfl

theorem cell22_3303572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 2, 1, 1, 4].length) (baseStart_3303572 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3303572 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3303572 prefixEnd_3303572 := by exact prefixLift 3303572
  have htrace : WordTrace (prefixWord ++ tailWord_3303572) baseStart_3303572 baseEnd_3303572 := by
    simpa [prefixWord, tailWord_3303572, baseEnd_3303572] using wordTrace_append hprefix tailTrace_3303572
  have hstable : (prefixWord ++ tailWord_3303572).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3303572).length < 2 ^ (prefixWord ++ tailWord_3303572).sum := by decide
  have hdescent : baseEnd_3303572 < baseStart_3303572 := by decide
  rcases family_descends (prefixWord ++ tailWord_3303572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3303579 : List Nat := [1, 1, 1, 1, 1, 1, 2, 6, 5, 3]
def baseStart_3303579 : Nat := 118140960795 + 3303579 * 2 ^ 59
def prefixEnd_3303579 : Nat := 4983230072969 + 3 ^ 40 * 3303579 * 2
def baseEnd_3303579 : Nat := 1130882604733090310446415

theorem tailTrace_3303579 : CollatzResearch.WordTrace tailWord_3303579 prefixEnd_3303579 1130882604733090310446415 := by
  unfold tailWord_3303579
  simp only [CollatzResearch.WordTrace]
  refine ⟨120491424898704964219545791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80327616599136642813030527 120491424898704964219545791)
  ·
    refine ⟨180737137348057446329318687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120491424898704964219545791 180737137348057446329318687)
    ·
      refine ⟨271105706022086169493978031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180737137348057446329318687 271105706022086169493978031)
      ·
        refine ⟨406658559033129254240967047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 271105706022086169493978031 406658559033129254240967047)
        ·
          refine ⟨609987838549693881361450571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 406658559033129254240967047 609987838549693881361450571)
          ·
            refine ⟨914981757824540822042175857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 609987838549693881361450571 914981757824540822042175857)
            ·
              refine ⟨686236318368405616531631893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 914981757824540822042175857 686236318368405616531631893)
              ·
                refine ⟨32167327423519013274920245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 686236318368405616531631893 32167327423519013274920245)
                ·
                  refine ⟨3015686945954907494523773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32167327423519013274920245 3015686945954907494523773)
                  ·
                    refine ⟨1130882604733090310446415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3015686945954907494523773 1130882604733090310446415)
                    ·
                      rfl

theorem cell22_3303579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 6, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 6, 5, 3].length) (baseStart_3303579 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3303579 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3303579 prefixEnd_3303579 := by exact prefixLift 3303579
  have htrace : WordTrace (prefixWord ++ tailWord_3303579) baseStart_3303579 baseEnd_3303579 := by
    simpa [prefixWord, tailWord_3303579, baseEnd_3303579] using wordTrace_append hprefix tailTrace_3303579
  have hstable : (prefixWord ++ tailWord_3303579).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3303579).length < 2 ^ (prefixWord ++ tailWord_3303579).sum := by decide
  have hdescent : baseEnd_3303579 < baseStart_3303579 := by decide
  rcases family_descends (prefixWord ++ tailWord_3303579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3303630 : List Nat := [4, 1, 1, 1, 4, 1, 3, 3, 1, 3]
def baseStart_3303630 : Nat := 118140960795 + 3303630 * 2 ^ 59
def prefixEnd_3303630 : Nat := 4983230072969 + 3 ^ 40 * 3303630 * 2
def baseEnd_3303630 : Nat := 1130900063075343177421259

theorem tailTrace_3303630 : CollatzResearch.WordTrace tailWord_3303630 prefixEnd_3303630 1130900063075343177421259 := by
  unfold tailWord_3303630
  simp only [CollatzResearch.WordTrace]
  refine ⟨15061660627690024991206543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80328856681013466619768229 15061660627690024991206543)
  ·
    refine ⟨22592490941535037486809815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15061660627690024991206543 22592490941535037486809815)
    ·
      refine ⟨33888736412302556230214723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22592490941535037486809815 33888736412302556230214723)
      ·
        refine ⟨50833104618453834345322085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33888736412302556230214723 50833104618453834345322085)
        ·
          refine ⟨9531207115960093939747891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50833104618453834345322085 9531207115960093939747891)
          ·
            refine ⟨14296810673940140909621837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9531207115960093939747891 14296810673940140909621837)
            ·
              refine ⟨5361304002727552841108189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14296810673940140909621837 5361304002727552841108189)
              ·
                refine ⟨2010489001022832315415571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5361304002727552841108189 2010489001022832315415571)
                ·
                  refine ⟨3015733501534248473123357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2010489001022832315415571 3015733501534248473123357)
                  ·
                    refine ⟨1130900063075343177421259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3015733501534248473123357 1130900063075343177421259)
                    ·
                      rfl

theorem cell22_3303630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 3, 3, 1, 3].length) (baseStart_3303630 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3303630 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3303630 prefixEnd_3303630 := by exact prefixLift 3303630
  have htrace : WordTrace (prefixWord ++ tailWord_3303630) baseStart_3303630 baseEnd_3303630 := by
    simpa [prefixWord, tailWord_3303630, baseEnd_3303630] using wordTrace_append hprefix tailTrace_3303630
  have hstable : (prefixWord ++ tailWord_3303630).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3303630).length < 2 ^ (prefixWord ++ tailWord_3303630).sum := by decide
  have hdescent : baseEnd_3303630 < baseStart_3303630 := by decide
  rcases family_descends (prefixWord ++ tailWord_3303630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3303639 : List Nat := [1, 1, 3, 2, 1, 2, 1, 2, 5, 4]
def baseStart_3303639 : Nat := 118140960795 + 3303639 * 2 ^ 59
def prefixEnd_3303639 : Nat := 4983230072969 + 3 ^ 40 * 3303639 * 2
def baseEnd_3303639 : Nat := 1130903143959270153946231

theorem tailTrace_3303639 : CollatzResearch.WordTrace tailWord_3303639 prefixEnd_3303639 1130903143959270153946231 := by
  unfold tailWord_3303639
  simp only [CollatzResearch.WordTrace]
  refine ⟨120493613278487594466729971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80329075518991729644486647 120493613278487594466729971)
  ·
    refine ⟨180740419917731391700094957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120493613278487594466729971 180740419917731391700094957)
    ·
      refine ⟨67777657469149271887535609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 180740419917731391700094957 67777657469149271887535609)
      ·
        refine ⟨50833243101861953915651707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67777657469149271887535609 50833243101861953915651707)
        ·
          refine ⟨76249864652792930873477561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50833243101861953915651707 76249864652792930873477561)
          ·
            refine ⟨57187398489594698155108171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76249864652792930873477561 57187398489594698155108171)
            ·
              refine ⟨85781097734392047232662257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57187398489594698155108171 85781097734392047232662257)
              ·
                refine ⟨64335823300794035424496693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85781097734392047232662257 64335823300794035424496693)
                ·
                  refine ⟨6031483434449440821046565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 64335823300794035424496693 6031483434449440821046565)
                  ·
                    refine ⟨1130903143959270153946231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6031483434449440821046565 1130903143959270153946231)
                    ·
                      rfl

theorem cell22_3303639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 2, 5, 4].length) (baseStart_3303639 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3303639 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3303639 prefixEnd_3303639 := by exact prefixLift 3303639
  have htrace : WordTrace (prefixWord ++ tailWord_3303639) baseStart_3303639 baseEnd_3303639 := by
    simpa [prefixWord, tailWord_3303639, baseEnd_3303639] using wordTrace_append hprefix tailTrace_3303639
  have hstable : (prefixWord ++ tailWord_3303639).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3303639).length < 2 ^ (prefixWord ++ tailWord_3303639).sum := by decide
  have hdescent : baseEnd_3303639 < baseStart_3303639 := by decide
  rcases family_descends (prefixWord ++ tailWord_3303639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3303701 : List Nat := [1, 3, 2, 1, 2, 1, 4, 2, 2, 4]
def baseStart_3303701 : Nat := 118140960795 + 3303701 * 2 ^ 59
def prefixEnd_3303701 : Nat := 4983230072969 + 3 ^ 40 * 3303701 * 2
def baseEnd_3303701 : Nat := 1130924367826322658896041

theorem tailTrace_3303701 : CollatzResearch.WordTrace tailWord_3303701 prefixEnd_3303701 1130924367826322658896041 := by
  unfold tailWord_3303701
  simp only [CollatzResearch.WordTrace]
  refine ⟨120495874604262979055486957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80330583069508652703657971 120495874604262979055486957)
  ·
    refine ⟨45185952976598617145807609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120495874604262979055486957 45185952976598617145807609)
    ·
      refine ⟨33889464732448962859355707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45185952976598617145807609 33889464732448962859355707)
      ·
        refine ⟨50834197098673444289033561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33889464732448962859355707 50834197098673444289033561)
        ·
          refine ⟨38125647824005083216775171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50834197098673444289033561 38125647824005083216775171)
          ·
            refine ⟨57188471736007624825162757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38125647824005083216775171 57188471736007624825162757)
            ·
              refine ⟨10722838450501429654718017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57188471736007624825162757 10722838450501429654718017)
              ·
                refine ⟨8042128837876072241038513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10722838450501429654718017 8042128837876072241038513)
                ·
                  refine ⟨6031596628407054180778885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8042128837876072241038513 6031596628407054180778885)
                  ·
                    refine ⟨1130924367826322658896041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6031596628407054180778885 1130924367826322658896041)
                    ·
                      rfl

theorem cell22_3303701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4, 2, 2, 4].length) (baseStart_3303701 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3303701 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3303701 prefixEnd_3303701 := by exact prefixLift 3303701
  have htrace : WordTrace (prefixWord ++ tailWord_3303701) baseStart_3303701 baseEnd_3303701 := by
    simpa [prefixWord, tailWord_3303701, baseEnd_3303701] using wordTrace_append hprefix tailTrace_3303701
  have hstable : (prefixWord ++ tailWord_3303701).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3303701).length < 2 ^ (prefixWord ++ tailWord_3303701).sum := by decide
  have hdescent : baseEnd_3303701 < baseStart_3303701 := by decide
  rcases family_descends (prefixWord ++ tailWord_3303701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3303703 : List Nat := [1, 1, 3, 4, 1, 2, 1, 4, 2, 3]
def baseStart_3303703 : Nat := 118140960795 + 3303703 * 2 ^ 59
def prefixEnd_3303703 : Nat := 4983230072969 + 3 ^ 40 * 3303703 * 2
def baseEnd_3303703 : Nat := 1130925052467195320346035

theorem tailTrace_3303703 : CollatzResearch.WordTrace tailWord_3303703 prefixEnd_3303703 1130925052467195320346035 := by
  unfold tailWord_3303703
  simp only [CollatzResearch.WordTrace]
  refine ⟨120495947550255733397059763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80330631700170488931373175 120495947550255733397059763)
  ·
    refine ⟨180743921325383600095589645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120495947550255733397059763 180743921325383600095589645)
    ·
      refine ⟨67778970497018850035846117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 180743921325383600095589645 67778970497018850035846117)
      ·
        refine ⟨12708556968191034381721147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67778970497018850035846117 12708556968191034381721147)
        ·
          refine ⟨19062835452286551572581721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12708556968191034381721147 19062835452286551572581721)
          ·
            refine ⟨14297126589214913679436291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19062835452286551572581721 14297126589214913679436291)
            ·
              refine ⟨21445689883822370519154437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14297126589214913679436291 21445689883822370519154437)
              ·
                refine ⟨4021066853216694472341457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21445689883822370519154437 4021066853216694472341457)
                ·
                  refine ⟨3015800139912520854256093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4021066853216694472341457 3015800139912520854256093)
                  ·
                    refine ⟨1130925052467195320346035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3015800139912520854256093 1130925052467195320346035)
                    ·
                      rfl

theorem cell22_3303703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 4, 2, 3].length) (baseStart_3303703 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3303703 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3303703 prefixEnd_3303703 := by exact prefixLift 3303703
  have htrace : WordTrace (prefixWord ++ tailWord_3303703) baseStart_3303703 baseEnd_3303703 := by
    simpa [prefixWord, tailWord_3303703, baseEnd_3303703] using wordTrace_append hprefix tailTrace_3303703
  have hstable : (prefixWord ++ tailWord_3303703).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3303703).length < 2 ^ (prefixWord ++ tailWord_3303703).sum := by decide
  have hdescent : baseEnd_3303703 < baseStart_3303703 := by decide
  rcases family_descends (prefixWord ++ tailWord_3303703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3303716 : List Nat := [2, 3, 1, 3, 1, 2, 3, 7]
def baseStart_3303716 : Nat := 118140960795 + 3303716 * 2 ^ 59
def prefixEnd_3303716 : Nat := 4983230072969 + 3 ^ 40 * 3303716 * 2
def baseEnd_3303716 : Nat := 125658833625874179974555

theorem tailTrace_3303716 : CollatzResearch.WordTrace tailWord_3303716 prefixEnd_3303716 125658833625874179974555 := by
  unfold tailWord_3303716
  simp only [CollatzResearch.WordTrace]
  refine ⟨60248210849604318308641501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80330947799472424411522001 60248210849604318308641501)
  ·
    refine ⟨22593079068601619365740563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60248210849604318308641501 22593079068601619365740563)
    ·
      refine ⟨33889618602902429048610845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22593079068601619365740563 33889618602902429048610845)
      ·
        refine ⟨12708606976088410893229067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33889618602902429048610845 12708606976088410893229067)
        ·
          refine ⟨19062910464132616339843601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12708606976088410893229067 19062910464132616339843601)
          ·
            refine ⟨14297182848099462254882701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19062910464132616339843601 14297182848099462254882701)
            ·
              refine ⟨5361443568037298345581013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14297182848099462254882701 5361443568037298345581013)
              ·
                refine ⟨125658833625874179974555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5361443568037298345581013 125658833625874179974555)
                ·
                  rfl

theorem cell22_3303716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 3, 7].length) (baseStart_3303716 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3303716 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3303716 prefixEnd_3303716 := by exact prefixLift 3303716
  have htrace : WordTrace (prefixWord ++ tailWord_3303716) baseStart_3303716 baseEnd_3303716 := by
    simpa [prefixWord, tailWord_3303716, baseEnd_3303716] using wordTrace_append hprefix tailTrace_3303716
  have hstable : (prefixWord ++ tailWord_3303716).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3303716).length < 2 ^ (prefixWord ++ tailWord_3303716).sum := by decide
  have hdescent : baseEnd_3303716 < baseStart_3303716 := by decide
  rcases family_descends (prefixWord ++ tailWord_3303716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3303761 : List Nat := [1, 2, 2, 1, 4, 3, 1, 1, 7]
def baseStart_3303761 : Nat := 118140960795 + 3303761 * 2 ^ 59
def prefixEnd_3303761 : Nat := 4983230072969 + 3 ^ 40 * 3303761 * 2
def baseEnd_3303761 : Nat := 376981635684167500798619

theorem tailTrace_3303761 : CollatzResearch.WordTrace tailWord_3303761 prefixEnd_3303761 376981635684167500798619 := by
  unfold tailWord_3303761
  simp only [CollatzResearch.WordTrace]
  refine ⟨120498062984045609302671137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80332041989363739535114091 120498062984045609302671137)
  ·
    refine ⟨90373547238034206977003353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120498062984045609302671137 90373547238034206977003353)
    ·
      refine ⟨67780160428525655232752515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90373547238034206977003353 67780160428525655232752515)
      ·
        refine ⟨101670240642788482849128773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67780160428525655232752515 101670240642788482849128773)
        ·
          refine ⟨19063170120522840534211645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 101670240642788482849128773 19063170120522840534211645)
          ·
            refine ⟨7148688795196065200329367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19063170120522840534211645 7148688795196065200329367)
            ·
              refine ⟨10723033192794097800494051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7148688795196065200329367 10723033192794097800494051)
              ·
                refine ⟨16084549789191146700741077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10723033192794097800494051 16084549789191146700741077)
                ·
                  refine ⟨376981635684167500798619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16084549789191146700741077 376981635684167500798619)
                  ·
                    rfl

theorem cell22_3303761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 1, 1, 7].length) (baseStart_3303761 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3303761 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3303761 prefixEnd_3303761 := by exact prefixLift 3303761
  have htrace : WordTrace (prefixWord ++ tailWord_3303761) baseStart_3303761 baseEnd_3303761 := by
    simpa [prefixWord, tailWord_3303761, baseEnd_3303761] using wordTrace_append hprefix tailTrace_3303761
  have hstable : (prefixWord ++ tailWord_3303761).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3303761).length < 2 ^ (prefixWord ++ tailWord_3303761).sum := by decide
  have hdescent : baseEnd_3303761 < baseStart_3303761 := by decide
  rcases family_descends (prefixWord ++ tailWord_3303761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3303765 : List Nat := [1, 3, 2, 2, 4, 1, 2, 1, 3, 3]
def baseStart_3303765 : Nat := 118140960795 + 3303765 * 2 ^ 59
def prefixEnd_3303765 : Nat := 4983230072969 + 3 ^ 40 * 3303765 * 2
def baseEnd_3303765 : Nat := 1130946276334247825295845

theorem tailTrace_3303765 : CollatzResearch.WordTrace tailWord_3303765 prefixEnd_3303765 1130946276334247825295845 := by
  unfold tailWord_3303765
  simp only [CollatzResearch.WordTrace]
  refine ⟨120498208876031117985816749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80332139250687411990544499 120498208876031117985816749)
  ·
    refine ⟨45186828328511669244681281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120498208876031117985816749 45186828328511669244681281)
    ·
      refine ⟨33890121246383751933510961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45186828328511669244681281 33890121246383751933510961)
      ·
        refine ⟨25417590934787813950133221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33890121246383751933510961 25417590934787813950133221)
        ·
          refine ⟨4765798300272715115649979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25417590934787813950133221 4765798300272715115649979)
          ·
            refine ⟨7148697450409072673474969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4765798300272715115649979 7148697450409072673474969)
            ·
              refine ⟨5361523087806804505106227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7148697450409072673474969 5361523087806804505106227)
              ·
                refine ⟨8042284631710206757659341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5361523087806804505106227 8042284631710206757659341)
                ·
                  refine ⟨3015856736891327534122253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8042284631710206757659341 3015856736891327534122253)
                  ·
                    refine ⟨1130946276334247825295845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3015856736891327534122253 1130946276334247825295845)
                    ·
                      rfl

theorem cell22_3303765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 2, 1, 3, 3].length) (baseStart_3303765 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3303765 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3303765 prefixEnd_3303765 := by exact prefixLift 3303765
  have htrace : WordTrace (prefixWord ++ tailWord_3303765) baseStart_3303765 baseEnd_3303765 := by
    simpa [prefixWord, tailWord_3303765, baseEnd_3303765] using wordTrace_append hprefix tailTrace_3303765
  have hstable : (prefixWord ++ tailWord_3303765).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3303765).length < 2 ^ (prefixWord ++ tailWord_3303765).sum := by decide
  have hdescent : baseEnd_3303765 < baseStart_3303765 := by decide
  rcases family_descends (prefixWord ++ tailWord_3303765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3303881 : List Nat := [1, 2, 1, 1, 2, 1, 5, 1, 2, 6]
def baseStart_3303881 : Nat := 118140960795 + 3303881 * 2 ^ 59
def prefixEnd_3303881 : Nat := 4983230072969 + 3 ^ 40 * 3303881 * 2
def baseEnd_3303881 : Nat := 1130985985504862189395489

theorem tailTrace_3303881 : CollatzResearch.WordTrace tailWord_3303881 prefixEnd_3303881 1130985985504862189395489 := by
  unfold tailWord_3303881
  simp only [CollatzResearch.WordTrace]
  refine ⟨120502439743610869797039497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80334959829073913198026331 120502439743610869797039497)
  ·
    refine ⟨90376829807708152347779623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120502439743610869797039497 90376829807708152347779623)
    ·
      refine ⟨135565244711562228521669435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90376829807708152347779623 135565244711562228521669435)
      ·
        refine ⟨203347867067343342782504153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135565244711562228521669435 203347867067343342782504153)
        ·
          refine ⟨152510900300507507086878115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 203347867067343342782504153 152510900300507507086878115)
          ·
            refine ⟨228766350450761260630317173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152510900300507507086878115 228766350450761260630317173)
            ·
              refine ⟨21446845354758868184092235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 228766350450761260630317173 21446845354758868184092235)
              ·
                refine ⟨32170268032138302276138353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21446845354758868184092235 32170268032138302276138353)
                ·
                  refine ⟨24127701024103726707103765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32170268032138302276138353 24127701024103726707103765)
                  ·
                    refine ⟨1130985985504862189395489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24127701024103726707103765 1130985985504862189395489)
                    ·
                      rfl

theorem cell22_3303881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 1, 2, 6].length) (baseStart_3303881 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3303881 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3303881 prefixEnd_3303881 := by exact prefixLift 3303881
  have htrace : WordTrace (prefixWord ++ tailWord_3303881) baseStart_3303881 baseEnd_3303881 := by
    simpa [prefixWord, tailWord_3303881, baseEnd_3303881] using wordTrace_append hprefix tailTrace_3303881
  have hstable : (prefixWord ++ tailWord_3303881).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3303881).length < 2 ^ (prefixWord ++ tailWord_3303881).sum := by decide
  have hdescent : baseEnd_3303881 < baseStart_3303881 := by decide
  rcases family_descends (prefixWord ++ tailWord_3303881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3303883 : List Nat := [1, 1, 1, 1, 3, 3, 1, 5, 3, 3]
def baseStart_3303883 : Nat := 118140960795 + 3303883 * 2 ^ 59
def prefixEnd_3303883 : Nat := 4983230072969 + 3 ^ 40 * 3303883 * 2
def baseEnd_3303883 : Nat := 1130986670145734850845483

theorem tailTrace_3303883 : CollatzResearch.WordTrace tailWord_3303883 prefixEnd_3303883 1130986670145734850845483 := by
  unfold tailWord_3303883
  simp only [CollatzResearch.WordTrace]
  refine ⟨120502512689603624138612303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80335008459735749425741535 120502512689603624138612303)
  ·
    refine ⟨180753769034405436207918455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120502512689603624138612303 180753769034405436207918455)
    ·
      refine ⟨271130653551608154311877683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180753769034405436207918455 271130653551608154311877683)
      ·
        refine ⟨406695980327412231467816525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 271130653551608154311877683 406695980327412231467816525)
        ·
          refine ⟨152510992622779586800431197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 406695980327412231467816525 152510992622779586800431197)
          ·
            refine ⟨57191622233542345050161699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 152510992622779586800431197 57191622233542345050161699)
            ·
              refine ⟨85787433350313517575242549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57191622233542345050161699 85787433350313517575242549)
              ·
                refine ⟨8042571876591892272678989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 85787433350313517575242549 8042571876591892272678989)
                ·
                  refine ⟨3015964453721959602254621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8042571876591892272678989 3015964453721959602254621)
                  ·
                    refine ⟨1130986670145734850845483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3015964453721959602254621 1130986670145734850845483)
                    ·
                      rfl

theorem cell22_3303883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 5, 3, 3].length) (baseStart_3303883 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3303883 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3303883 prefixEnd_3303883 := by exact prefixLift 3303883
  have htrace : WordTrace (prefixWord ++ tailWord_3303883) baseStart_3303883 baseEnd_3303883 := by
    simpa [prefixWord, tailWord_3303883, baseEnd_3303883] using wordTrace_append hprefix tailTrace_3303883
  have hstable : (prefixWord ++ tailWord_3303883).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3303883).length < 2 ^ (prefixWord ++ tailWord_3303883).sum := by decide
  have hdescent : baseEnd_3303883 < baseStart_3303883 := by decide
  rcases family_descends (prefixWord ++ tailWord_3303883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3303896 : List Nat := [2, 1, 2, 2, 2, 1, 1, 2, 9]
def baseStart_3303896 : Nat := 118140960795 + 3303896 * 2 ^ 59
def prefixEnd_3303896 : Nat := 4983230072969 + 3 ^ 40 * 3303896 * 2
def baseEnd_3303896 : Nat := 376997040103802383423481

theorem tailTrace_3303896 : CollatzResearch.WordTrace tailWord_3303896 prefixEnd_3303896 376997040103802383423481 := by
  unfold tailWord_3303896
  simp only [CollatzResearch.WordTrace]
  refine ⟨60251493419278263679417771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80335324559037684905890361 60251493419278263679417771)
  ·
    refine ⟨90377240128917395519126657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60251493419278263679417771 90377240128917395519126657)
    ·
      refine ⟨67782930096688046639344993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90377240128917395519126657 67782930096688046639344993)
      ·
        refine ⟨50837197572516034979508745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67782930096688046639344993 50837197572516034979508745)
        ·
          refine ⟨38127898179387026234631559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50837197572516034979508745 38127898179387026234631559)
          ·
            refine ⟨57191847269080539351947339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38127898179387026234631559 57191847269080539351947339)
            ·
              refine ⟨85787770903620809027921009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57191847269080539351947339 85787770903620809027921009)
              ·
                refine ⟨64340828177715606770940757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85787770903620809027921009 64340828177715606770940757)
                ·
                  refine ⟨376997040103802383423481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 64340828177715606770940757 376997040103802383423481)
                  ·
                    rfl

theorem cell22_3303896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 2, 9].length) (baseStart_3303896 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3303896 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3303896 prefixEnd_3303896 := by exact prefixLift 3303896
  have htrace : WordTrace (prefixWord ++ tailWord_3303896) baseStart_3303896 baseEnd_3303896 := by
    simpa [prefixWord, tailWord_3303896, baseEnd_3303896] using wordTrace_append hprefix tailTrace_3303896
  have hstable : (prefixWord ++ tailWord_3303896).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3303896).length < 2 ^ (prefixWord ++ tailWord_3303896).sum := by decide
  have hdescent : baseEnd_3303896 < baseStart_3303896 := by decide
  rcases family_descends (prefixWord ++ tailWord_3303896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3303960 : List Nat := [2, 1, 2, 3, 3, 1, 1, 4, 1, 4]
def baseStart_3303960 : Nat := 118140960795 + 3303960 * 2 ^ 59
def prefixEnd_3303960 : Nat := 4983230072969 + 3 ^ 40 * 3303960 * 2
def baseEnd_3303960 : Nat := 1131013028819332316670247

theorem tailTrace_3303960 : CollatzResearch.WordTrace tailWord_3303960 prefixEnd_3303960 1131013028819332316670247 := by
  unfold tailWord_3303960
  simp only [CollatzResearch.WordTrace]
  refine ⟨60252660555162333144582667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80336880740216444192776889 60252660555162333144582667)
  ·
    refine ⟨90378990832743499716874001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60252660555162333144582667 90378990832743499716874001)
    ·
      refine ⟨67784243124557624787655501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90378990832743499716874001 67784243124557624787655501)
      ·
        refine ⟨25419091171709109295370813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67784243124557624787655501 25419091171709109295370813)
        ·
          refine ⟨9532159189390915985764055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25419091171709109295370813 9532159189390915985764055)
          ·
            refine ⟨14298238784086373978646083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9532159189390915985764055 14298238784086373978646083)
            ·
              refine ⟨21447358176129560967969125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14298238784086373978646083 21447358176129560967969125)
              ·
                refine ⟨4021379658024292681494211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21447358176129560967969125 4021379658024292681494211)
                ·
                  refine ⟨6032069487036439022241317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4021379658024292681494211 6032069487036439022241317)
                  ·
                    refine ⟨1131013028819332316670247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6032069487036439022241317 1131013028819332316670247)
                    ·
                      rfl

theorem cell22_3303960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 4, 1, 4].length) (baseStart_3303960 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3303960 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3303960 prefixEnd_3303960 := by exact prefixLift 3303960
  have htrace : WordTrace (prefixWord ++ tailWord_3303960) baseStart_3303960 baseEnd_3303960 := by
    simpa [prefixWord, tailWord_3303960, baseEnd_3303960] using wordTrace_append hprefix tailTrace_3303960
  have hstable : (prefixWord ++ tailWord_3303960).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3303960).length < 2 ^ (prefixWord ++ tailWord_3303960).sum := by decide
  have hdescent : baseEnd_3303960 < baseStart_3303960 := by decide
  rcases family_descends (prefixWord ++ tailWord_3303960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3303973 : List Nat := [1, 3, 1, 2, 2, 1, 2, 4, 1, 5]
def baseStart_3303973 : Nat := 118140960795 + 3303973 * 2 ^ 59
def prefixEnd_3303973 : Nat := 4983230072969 + 3 ^ 40 * 3303973 * 2
def baseEnd_3303973 : Nat := 1131017478985004616095207

theorem tailTrace_3303973 : CollatzResearch.WordTrace tailWord_3303973 prefixEnd_3303973 1131017478985004616095207 := by
  unfold tailWord_3303973
  simp only [CollatzResearch.WordTrace]
  refine ⟨120505795259277569509388573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80337196839518379672925715 120505795259277569509388573)
  ·
    refine ⟨45189673222229088566020715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120505795259277569509388573 45189673222229088566020715)
    ·
      refine ⟨67784509833343632849031073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45189673222229088566020715 67784509833343632849031073)
      ·
        refine ⟨50838382375007724636773305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67784509833343632849031073 50838382375007724636773305)
        ·
          refine ⟨38128786781255793477579979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50838382375007724636773305 38128786781255793477579979)
          ·
            refine ⟨57193180171883690216369969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38128786781255793477579979 57193180171883690216369969)
            ·
              refine ⟨42894885128912767662277477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57193180171883690216369969 42894885128912767662277477)
              ·
                refine ⟨8042790961671143936677027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42894885128912767662277477 8042790961671143936677027)
                ·
                  refine ⟨12064186442506715905015541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8042790961671143936677027 12064186442506715905015541)
                  ·
                    refine ⟨1131017478985004616095207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12064186442506715905015541 1131017478985004616095207)
                    ·
                      rfl

theorem cell22_3303973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 4, 1, 5].length) (baseStart_3303973 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3303973 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3303973 prefixEnd_3303973 := by exact prefixLift 3303973
  have htrace : WordTrace (prefixWord ++ tailWord_3303973) baseStart_3303973 baseEnd_3303973 := by
    simpa [prefixWord, tailWord_3303973, baseEnd_3303973] using wordTrace_append hprefix tailTrace_3303973
  have hstable : (prefixWord ++ tailWord_3303973).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3303973).length < 2 ^ (prefixWord ++ tailWord_3303973).sum := by decide
  have hdescent : baseEnd_3303973 < baseStart_3303973 := by decide
  rcases family_descends (prefixWord ++ tailWord_3303973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3303992 : List Nat := [2, 1, 2, 1, 4, 1, 5, 2, 4]
def baseStart_3303992 : Nat := 118140960795 + 3303992 * 2 ^ 59
def prefixEnd_3303992 : Nat := 4983230072969 + 3 ^ 40 * 3303992 * 2
def baseEnd_3303992 : Nat := 377007994357764966623383

theorem tailTrace_3303992 : CollatzResearch.WordTrace tailWord_3303992 prefixEnd_3303992 377007994357764966623383 := by
  unfold tailWord_3303992
  simp only [CollatzResearch.WordTrace]
  refine ⟨60253244123104367877165115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80337658830805823836220153 60253244123104367877165115)
  ·
    refine ⟨90379866184656551815747673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60253244123104367877165115 90379866184656551815747673)
    ·
      refine ⟨67784899638492413861810755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90379866184656551815747673 67784899638492413861810755)
      ·
        refine ⟨101677349457738620792716133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67784899638492413861810755 101677349457738620792716133)
        ·
          refine ⟨19064503023325991398634275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 101677349457738620792716133 19064503023325991398634275)
          ·
            refine ⟨28596754534988987097951413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19064503023325991398634275 28596754534988987097951413)
            ·
              refine ⟨2680945737655217540432945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28596754534988987097951413 2680945737655217540432945)
              ·
                refine ⟨2010709303241413155324709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2680945737655217540432945 2010709303241413155324709)
                ·
                  refine ⟨377007994357764966623383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2010709303241413155324709 377007994357764966623383)
                  ·
                    rfl

theorem cell22_3303992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 5, 2, 4].length) (baseStart_3303992 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3303992 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3303992 prefixEnd_3303992 := by exact prefixLift 3303992
  have htrace : WordTrace (prefixWord ++ tailWord_3303992) baseStart_3303992 baseEnd_3303992 := by
    simpa [prefixWord, tailWord_3303992, baseEnd_3303992] using wordTrace_append hprefix tailTrace_3303992
  have hstable : (prefixWord ++ tailWord_3303992).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3303992).length < 2 ^ (prefixWord ++ tailWord_3303992).sum := by decide
  have hdescent : baseEnd_3303992 < baseStart_3303992 := by decide
  rcases family_descends (prefixWord ++ tailWord_3303992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3304007 : List Nat := [1, 1, 4, 1, 4, 2, 1, 3, 2, 3]
def baseStart_3304007 : Nat := 118140960795 + 3304007 * 2 ^ 59
def prefixEnd_3304007 : Nat := 4983230072969 + 3 ^ 40 * 3304007 * 2
def baseEnd_3304007 : Nat := 1131029117879839860745103

theorem tailTrace_3304007 : CollatzResearch.WordTrace tailWord_3304007 prefixEnd_3304007 1131029117879839860745103 := by
  unfold tailWord_3304007
  simp only [CollatzResearch.WordTrace]
  refine ⟨120507035341154393316126275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80338023560769595544084183 120507035341154393316126275)
  ·
    refine ⟨180760553011731589974189413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120507035341154393316126275 180760553011731589974189413)
    ·
      refine ⟨33892603689699673120160515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 180760553011731589974189413 33892603689699673120160515)
      ·
        refine ⟨50838905534549509680240773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33892603689699673120160515 50838905534549509680240773)
        ·
          refine ⟨9532294787728033065045145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50838905534549509680240773 9532294787728033065045145)
          ·
            refine ⟨7149221090796024798783859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9532294787728033065045145 7149221090796024798783859)
            ·
              refine ⟨10723831636194037198175789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7149221090796024798783859 10723831636194037198175789)
              ·
                refine ⟨4021436863572763949315921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10723831636194037198175789 4021436863572763949315921)
                ·
                  refine ⟨3016077647679572961986941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4021436863572763949315921 3016077647679572961986941)
                  ·
                    refine ⟨1131029117879839860745103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3016077647679572961986941 1131029117879839860745103)
                    ·
                      rfl

theorem cell22_3304007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 1, 3, 2, 3].length) (baseStart_3304007 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3304007 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3304007 prefixEnd_3304007 := by exact prefixLift 3304007
  have htrace : WordTrace (prefixWord ++ tailWord_3304007) baseStart_3304007 baseEnd_3304007 := by
    simpa [prefixWord, tailWord_3304007, baseEnd_3304007] using wordTrace_append hprefix tailTrace_3304007
  have hstable : (prefixWord ++ tailWord_3304007).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3304007).length < 2 ^ (prefixWord ++ tailWord_3304007).sum := by decide
  have hdescent : baseEnd_3304007 < baseStart_3304007 := by decide
  rcases family_descends (prefixWord ++ tailWord_3304007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3304054 : List Nat := [5, 1, 1, 2, 4, 1, 1, 7]
def baseStart_3304054 : Nat := 118140960795 + 3304054 * 2 ^ 59
def prefixEnd_3304054 : Nat := 4983230072969 + 3 ^ 40 * 3304054 * 2
def baseEnd_3304054 : Nat := 125671689660038600535551

theorem tailTrace_3304054 : CollatzResearch.WordTrace tailWord_3304054 prefixEnd_3304054 125671689660038600535551 := by
  unfold tailWord_3304054
  simp only [CollatzResearch.WordTrace]
  refine ⟨7531796848249007521442951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 80339166381322746895391477 7531796848249007521442951)
  ·
    refine ⟨11297695272373511282164427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7531796848249007521442951 11297695272373511282164427)
    ·
      refine ⟨16946542908560266923246641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11297695272373511282164427 16946542908560266923246641)
      ·
        refine ⟨12709907181420200192434981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16946542908560266923246641 12709907181420200192434981)
        ·
          refine ⟨2383107596516287536081559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12709907181420200192434981 2383107596516287536081559)
          ·
            refine ⟨3574661394774431304122339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2383107596516287536081559 3574661394774431304122339)
            ·
              refine ⟨5361992092161646956183509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3574661394774431304122339 5361992092161646956183509)
              ·
                refine ⟨125671689660038600535551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5361992092161646956183509 125671689660038600535551)
                ·
                  rfl

theorem cell22_3304054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 1, 7].length) (baseStart_3304054 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3304054 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3304054 prefixEnd_3304054 := by exact prefixLift 3304054
  have htrace : WordTrace (prefixWord ++ tailWord_3304054) baseStart_3304054 baseEnd_3304054 := by
    simpa [prefixWord, tailWord_3304054, baseEnd_3304054] using wordTrace_append hprefix tailTrace_3304054
  have hstable : (prefixWord ++ tailWord_3304054).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3304054).length < 2 ^ (prefixWord ++ tailWord_3304054).sum := by decide
  have hdescent : baseEnd_3304054 < baseStart_3304054 := by decide
  rcases family_descends (prefixWord ++ tailWord_3304054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3304065 : List Nat := [1, 2, 4, 2, 1, 1, 1, 5, 5]
def baseStart_3304065 : Nat := 118140960795 + 3304065 * 2 ^ 59
def prefixEnd_3304065 : Nat := 4983230072969 + 3 ^ 40 * 3304065 * 2
def baseEnd_3304065 : Nat := 377016324155049014264975

theorem tailTrace_3304065 : CollatzResearch.WordTrace tailWord_3304065 prefixEnd_3304065 377016324155049014264975 := by
  unfold tailWord_3304065
  simp only [CollatzResearch.WordTrace]
  refine ⟨120509150774944269221737649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80339433849962846147825099 120509150774944269221737649)
  ·
    refine ⟨90381863081208201916303237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120509150774944269221737649 90381863081208201916303237)
    ·
      refine ⟨16946599327726537859306857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 90381863081208201916303237 16946599327726537859306857)
      ·
        refine ⟨12709949495794903394480143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16946599327726537859306857 12709949495794903394480143)
        ·
          refine ⟨19064924243692355091720215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12709949495794903394480143 19064924243692355091720215)
          ·
            refine ⟨28597386365538532637580323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19064924243692355091720215 28597386365538532637580323)
            ·
              refine ⟨42896079548307798956370485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28597386365538532637580323 42896079548307798956370485)
              ·
                refine ⟨4021507457653856152159733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42896079548307798956370485 4021507457653856152159733)
                ·
                  refine ⟨377016324155049014264975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4021507457653856152159733 377016324155049014264975)
                  ·
                    rfl

theorem cell22_3304065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 5, 5].length) (baseStart_3304065 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3304065 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3304065 prefixEnd_3304065 := by exact prefixLift 3304065
  have htrace : WordTrace (prefixWord ++ tailWord_3304065) baseStart_3304065 baseEnd_3304065 := by
    simpa [prefixWord, tailWord_3304065, baseEnd_3304065] using wordTrace_append hprefix tailTrace_3304065
  have hstable : (prefixWord ++ tailWord_3304065).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3304065).length < 2 ^ (prefixWord ++ tailWord_3304065).sum := by decide
  have hdescent : baseEnd_3304065 < baseStart_3304065 := by decide
  rcases family_descends (prefixWord ++ tailWord_3304065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3304108 : List Nat := [2, 2, 1, 1, 1, 1, 1, 1, 1, 11]
def baseStart_3304108 : Nat := 118140960795 + 3304108 * 2 ^ 59
def prefixEnd_3304108 : Nat := 4983230072969 + 3 ^ 40 * 3304108 * 2
def baseEnd_3304108 : Nat := 1131063692243909263969793

theorem tailTrace_3304108 : CollatzResearch.WordTrace tailWord_3304108 prefixEnd_3304108 1131063692243909263969793 := by
  unfold tailWord_3304108
  simp only [CollatzResearch.WordTrace]
  refine ⟨60255359556894243782776489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80340479409192325043701985 60255359556894243782776489)
  ·
    refine ⟨45191519667670682837082367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60255359556894243782776489 45191519667670682837082367)
    ·
      refine ⟨67787279501506024255623551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45191519667670682837082367 67787279501506024255623551)
      ·
        refine ⟨101680919252259036383435327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67787279501506024255623551 101680919252259036383435327)
        ·
          refine ⟨152521378878388554575152991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101680919252259036383435327 152521378878388554575152991)
          ·
            refine ⟨228782068317582831862729487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152521378878388554575152991 228782068317582831862729487)
            ·
              refine ⟨343173102476374247794094231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 228782068317582831862729487 343173102476374247794094231)
              ·
                refine ⟨514759653714561371691141347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 343173102476374247794094231 514759653714561371691141347)
                ·
                  refine ⟨772139480571842057536712021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 514759653714561371691141347 772139480571842057536712021)
                  ·
                    refine ⟨1131063692243909263969793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 772139480571842057536712021 1131063692243909263969793)
                    ·
                      rfl

theorem cell22_3304108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 11].length) (baseStart_3304108 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3304108 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3304108 prefixEnd_3304108 := by exact prefixLift 3304108
  have htrace : WordTrace (prefixWord ++ tailWord_3304108) baseStart_3304108 baseEnd_3304108 := by
    simpa [prefixWord, tailWord_3304108, baseEnd_3304108] using wordTrace_append hprefix tailTrace_3304108
  have hstable : (prefixWord ++ tailWord_3304108).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3304108).length < 2 ^ (prefixWord ++ tailWord_3304108).sum := by decide
  have hdescent : baseEnd_3304108 < baseStart_3304108 := by decide
  rcases family_descends (prefixWord ++ tailWord_3304108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3304142 : List Nat := [4, 1, 1, 1, 3, 2, 1, 2, 4, 3]
def baseStart_3304142 : Nat := 118140960795 + 3304142 * 2 ^ 59
def prefixEnd_3304142 : Nat := 4983230072969 + 3 ^ 40 * 3304142 * 2
def baseEnd_3304142 : Nat := 1131075331138744508619689

theorem tailTrace_3304142 : CollatzResearch.WordTrace tailWord_3304142 prefixEnd_3304142 1131075331138744508619689 := by
  unfold tailWord_3304142
  simp only [CollatzResearch.WordTrace]
  refine ⟨15063994899458163921536335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80341306130443540914860453 15063994899458163921536335)
  ·
    refine ⟨22595992349187245882304503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15063994899458163921536335 22595992349187245882304503)
    ·
      refine ⟨33893988523780868823456755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22595992349187245882304503 33893988523780868823456755)
      ·
        refine ⟨50840982785671303235185133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33893988523780868823456755 50840982785671303235185133)
        ·
          refine ⟨19065368544626738713194425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50840982785671303235185133 19065368544626738713194425)
          ·
            refine ⟨14299026408470054034895819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19065368544626738713194425 14299026408470054034895819)
            ·
              refine ⟨21448539612705081052343729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14299026408470054034895819 21448539612705081052343729)
              ·
                refine ⟨16086404709528810789257797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21448539612705081052343729 16086404709528810789257797)
                ·
                  refine ⟨3016200883036652022985837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16086404709528810789257797 3016200883036652022985837)
                  ·
                    refine ⟨1131075331138744508619689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3016200883036652022985837 1131075331138744508619689)
                    ·
                      rfl

theorem cell22_3304142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 2, 4, 3].length) (baseStart_3304142 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3304142 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3304142 prefixEnd_3304142 := by exact prefixLift 3304142
  have htrace : WordTrace (prefixWord ++ tailWord_3304142) baseStart_3304142 baseEnd_3304142 := by
    simpa [prefixWord, tailWord_3304142, baseEnd_3304142] using wordTrace_append hprefix tailTrace_3304142
  have hstable : (prefixWord ++ tailWord_3304142).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3304142).length < 2 ^ (prefixWord ++ tailWord_3304142).sum := by decide
  have hdescent : baseEnd_3304142 < baseStart_3304142 := by decide
  rcases family_descends (prefixWord ++ tailWord_3304142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3304180 : List Nat := [2, 6, 1, 1, 3, 1, 1, 2, 1, 4]
def baseStart_3304180 : Nat := 118140960795 + 3304180 * 2 ^ 59
def prefixEnd_3304180 : Nat := 4983230072969 + 3 ^ 40 * 3304180 * 2
def baseEnd_3304180 : Nat := 1131088339315325076169573

theorem tailTrace_3304180 : CollatzResearch.WordTrace tailWord_3304180 prefixEnd_3304180 1131088339315325076169573 := by
  unfold tailWord_3304180
  simp only [CollatzResearch.WordTrace]
  refine ⟨60256672584763821931086997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80342230113018429241449329 60256672584763821931086997)
  ·
    refine ⟨2824531527410804153019703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 60256672584763821931086997 2824531527410804153019703)
    ·
      refine ⟨4236797291116206229529555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2824531527410804153019703 4236797291116206229529555)
      ·
        refine ⟨6355195936674309344294333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4236797291116206229529555 6355195936674309344294333)
        ·
          refine ⟨2383198476252866004110375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6355195936674309344294333 2383198476252866004110375)
          ·
            refine ⟨3574797714379299006165563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2383198476252866004110375 3574797714379299006165563)
            ·
              refine ⟨5362196571568948509248345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3574797714379299006165563 5362196571568948509248345)
              ·
                refine ⟨4021647428676711381936259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5362196571568948509248345 4021647428676711381936259)
                ·
                  refine ⟨6032471143015067072904389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4021647428676711381936259 6032471143015067072904389)
                  ·
                    refine ⟨1131088339315325076169573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6032471143015067072904389 1131088339315325076169573)
                    ·
                      rfl

theorem cell22_3304180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 1, 2, 1, 4].length) (baseStart_3304180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3304180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3304180 prefixEnd_3304180 := by exact prefixLift 3304180
  have htrace : WordTrace (prefixWord ++ tailWord_3304180) baseStart_3304180 baseEnd_3304180 := by
    simpa [prefixWord, tailWord_3304180, baseEnd_3304180] using wordTrace_append hprefix tailTrace_3304180
  have hstable : (prefixWord ++ tailWord_3304180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3304180).length < 2 ^ (prefixWord ++ tailWord_3304180).sum := by decide
  have hdescent : baseEnd_3304180 < baseStart_3304180 := by decide
  rcases family_descends (prefixWord ++ tailWord_3304180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3304204 : List Nat := [2, 2, 1, 2, 2, 1, 1, 7, 1, 3]
def baseStart_3304204 : Nat := 118140960795 + 3304204 * 2 ^ 59
def prefixEnd_3304204 : Nat := 4983230072969 + 3 ^ 40 * 3304204 * 2
def baseEnd_3304204 : Nat := 1131096555005797013569499

theorem tailTrace_3304204 : CollatzResearch.WordTrace tailWord_3304204 prefixEnd_3304204 1131096555005797013569499 := by
  unfold tailWord_3304204
  simp only [CollatzResearch.WordTrace]
  refine ⟨60257110260720347980523833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80342813680960463974031777 60257110260720347980523833)
  ·
    refine ⟨45192832695540260985392875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60257110260720347980523833 45192832695540260985392875)
    ·
      refine ⟨67789249043310391478089313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45192832695540260985392875 67789249043310391478089313)
      ·
        refine ⟨50841936782482793608566985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67789249043310391478089313 50841936782482793608566985)
        ·
          refine ⟨38131452586862095206425239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50841936782482793608566985 38131452586862095206425239)
          ·
            refine ⟨57197178880293142809637859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38131452586862095206425239 57197178880293142809637859)
            ·
              refine ⟨85795768320439714214456789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57197178880293142809637859 85795768320439714214456789)
              ·
                refine ⟨2010838320010305801901331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 85795768320439714214456789 2010838320010305801901331)
                ·
                  refine ⟨3016257480015458702851997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2010838320010305801901331 3016257480015458702851997)
                  ·
                    refine ⟨1131096555005797013569499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3016257480015458702851997 1131096555005797013569499)
                    ·
                      rfl

theorem cell22_3304204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 7, 1, 3].length) (baseStart_3304204 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3304204 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3304204 prefixEnd_3304204 := by exact prefixLift 3304204
  have htrace : WordTrace (prefixWord ++ tailWord_3304204) baseStart_3304204 baseEnd_3304204 := by
    simpa [prefixWord, tailWord_3304204, baseEnd_3304204] using wordTrace_append hprefix tailTrace_3304204
  have hstable : (prefixWord ++ tailWord_3304204).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3304204).length < 2 ^ (prefixWord ++ tailWord_3304204).sum := by decide
  have hdescent : baseEnd_3304204 < baseStart_3304204 := by decide
  rcases family_descends (prefixWord ++ tailWord_3304204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3304232 : List Nat := [2, 1, 5, 1, 1, 1, 3, 1, 2, 5]
def baseStart_3304232 : Nat := 118140960795 + 3304232 * 2 ^ 59
def prefixEnd_3304232 : Nat := 4983230072969 + 3 ^ 40 * 3304232 * 2
def baseEnd_3304232 : Nat := 1131106139978014273869413

theorem tailTrace_3304232 : CollatzResearch.WordTrace tailWord_3304232 prefixEnd_3304232 1131106139978014273869413 := by
  unfold tailWord_3304232
  simp only [CollatzResearch.WordTrace]
  refine ⟨60257620882669628371533475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80343494510226171162044633 60257620882669628371533475)
  ·
    refine ⟨90386431324004442557300213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60257620882669628371533475 90386431324004442557300213)
    ·
      refine ⟨8473727936625416489746895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 90386431324004442557300213 8473727936625416489746895)
      ·
        refine ⟨12710591904938124734620343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8473727936625416489746895 12710591904938124734620343)
        ·
          refine ⟨19065887857407187101930515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12710591904938124734620343 19065887857407187101930515)
          ·
            refine ⟨28598831786110780652895773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19065887857407187101930515 28598831786110780652895773)
            ·
              refine ⟨10724561919791542744835915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28598831786110780652895773 10724561919791542744835915)
              ·
                refine ⟨16086842879687314117253873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10724561919791542744835915 16086842879687314117253873)
                ·
                  refine ⟨12065132159765485587940405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16086842879687314117253873 12065132159765485587940405)
                  ·
                    refine ⟨1131106139978014273869413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12065132159765485587940405 1131106139978014273869413)
                    ·
                      rfl

theorem cell22_3304232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 3, 1, 2, 5].length) (baseStart_3304232 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3304232 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3304232 prefixEnd_3304232 := by exact prefixLift 3304232
  have htrace : WordTrace (prefixWord ++ tailWord_3304232) baseStart_3304232 baseEnd_3304232 := by
    simpa [prefixWord, tailWord_3304232, baseEnd_3304232] using wordTrace_append hprefix tailTrace_3304232
  have hstable : (prefixWord ++ tailWord_3304232).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3304232).length < 2 ^ (prefixWord ++ tailWord_3304232).sum := by decide
  have hdescent : baseEnd_3304232 < baseStart_3304232 := by decide
  rcases family_descends (prefixWord ++ tailWord_3304232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3304247 : List Nat := [1, 1, 3, 1, 2, 1, 4, 4, 1, 4]
def baseStart_3304247 : Nat := 118140960795 + 3304247 * 2 ^ 59
def prefixEnd_3304247 : Nat := 4983230072969 + 3 ^ 40 * 3304247 * 2
def baseEnd_3304247 : Nat := 1131111274784559234744367

theorem tailTrace_3304247 : CollatzResearch.WordTrace tailWord_3304247 prefixEnd_3304247 1131111274784559234744367 := by
  unfold tailWord_3304247
  simp only [CollatzResearch.WordTrace]
  refine ⟨120515788860284914304862995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80343859240189942869908663 120515788860284914304862995)
  ·
    refine ⟨180773683290427371457294493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120515788860284914304862995 180773683290427371457294493)
    ·
      refine ⟨67790131233910264296485435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 180773683290427371457294493 67790131233910264296485435)
      ·
        refine ⟨101685196850865396444728153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67790131233910264296485435 101685196850865396444728153)
        ·
          refine ⟨76263897638149047333546115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101685196850865396444728153 76263897638149047333546115)
          ·
            refine ⟨114395846457223571000319173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76263897638149047333546115 114395846457223571000319173)
            ·
              refine ⟨21449221210729419562559845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 114395846457223571000319173 21449221210729419562559845)
              ·
                refine ⟨4021728977011766167979971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21449221210729419562559845 4021728977011766167979971)
                ·
                  refine ⟨6032593465517649251969957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4021728977011766167979971 6032593465517649251969957)
                  ·
                    refine ⟨1131111274784559234744367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6032593465517649251969957 1131111274784559234744367)
                    ·
                      rfl

theorem cell22_3304247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 4, 1, 4].length) (baseStart_3304247 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3304247 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3304247 prefixEnd_3304247 := by exact prefixLift 3304247
  have htrace : WordTrace (prefixWord ++ tailWord_3304247) baseStart_3304247 baseEnd_3304247 := by
    simpa [prefixWord, tailWord_3304247, baseEnd_3304247] using wordTrace_append hprefix tailTrace_3304247
  have hstable : (prefixWord ++ tailWord_3304247).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3304247).length < 2 ^ (prefixWord ++ tailWord_3304247).sum := by decide
  have hdescent : baseEnd_3304247 < baseStart_3304247 := by decide
  rcases family_descends (prefixWord ++ tailWord_3304247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3304279 : List Nat := [1, 1, 3, 2, 4, 1, 2, 4, 4]
def baseStart_3304279 : Nat := 118140960795 + 3304279 * 2 ^ 59
def prefixEnd_3304279 : Nat := 4983230072969 + 3 ^ 40 * 3304279 * 2
def baseEnd_3304279 : Nat := 377040743012840605981423

theorem tailTrace_3304279 : CollatzResearch.WordTrace tailWord_3304279 prefixEnd_3304279 377040743012840605981423 := by
  unfold tailWord_3304279
  simp only [CollatzResearch.WordTrace]
  refine ⟨120516955996168983770027891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80344637330779322513351927 120516955996168983770027891)
  ·
    refine ⟨180775433994253475655041837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120516955996168983770027891 180775433994253475655041837)
    ·
      refine ⟨67790787747845053370640689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 180775433994253475655041837 67790787747845053370640689)
      ·
        refine ⟨50843090810883790027980517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67790787747845053370640689 50843090810883790027980517)
        ·
          refine ⟨9533079527040710630246347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50843090810883790027980517 9533079527040710630246347)
          ·
            refine ⟨14299619290561065945369521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9533079527040710630246347 14299619290561065945369521)
            ·
              refine ⟨10724714467920799459027141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14299619290561065945369521 10724714467920799459027141)
              ·
                refine ⟨2010883962735149898567589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10724714467920799459027141 2010883962735149898567589)
                ·
                  refine ⟨377040743012840605981423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2010883962735149898567589 377040743012840605981423)
                  ·
                    rfl

theorem cell22_3304279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 2, 4, 4].length) (baseStart_3304279 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3304279 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3304279 prefixEnd_3304279 := by exact prefixLift 3304279
  have htrace : WordTrace (prefixWord ++ tailWord_3304279) baseStart_3304279 baseEnd_3304279 := by
    simpa [prefixWord, tailWord_3304279, baseEnd_3304279] using wordTrace_append hprefix tailTrace_3304279
  have hstable : (prefixWord ++ tailWord_3304279).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3304279).length < 2 ^ (prefixWord ++ tailWord_3304279).sum := by decide
  have hdescent : baseEnd_3304279 < baseStart_3304279 := by decide
  rcases family_descends (prefixWord ++ tailWord_3304279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3304292 : List Nat := [2, 3, 1, 1, 4, 1, 1, 2, 1, 6]
def baseStart_3304292 : Nat := 118140960795 + 3304292 * 2 ^ 59
def prefixEnd_3304292 : Nat := 4983230072969 + 3 ^ 40 * 3304292 * 2
def baseEnd_3304292 : Nat := 1131126679204194117369229

theorem tailTrace_3304292 : CollatzResearch.WordTrace tailWord_3304292 prefixEnd_3304292 1131126679204194117369229 := by
  unfold tailWord_3304292
  simp only [CollatzResearch.WordTrace]
  refine ⟨60258715072560943495125565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80344953430081257993500753 60258715072560943495125565)
  ·
    refine ⟨22597018152210353810672087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60258715072560943495125565 22597018152210353810672087)
    ·
      refine ⟨33895527228315530716008131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22597018152210353810672087 33895527228315530716008131)
      ·
        refine ⟨50843290842473296074012197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33895527228315530716008131 50843290842473296074012197)
        ·
          refine ⟨9533117032963743013877287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50843290842473296074012197 9533117032963743013877287)
          ·
            refine ⟨14299675549445614520815931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9533117032963743013877287 14299675549445614520815931)
            ·
              refine ⟨21449513324168421781223897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14299675549445614520815931 21449513324168421781223897)
              ·
                refine ⟨16087134993126316335917923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21449513324168421781223897 16087134993126316335917923)
                ·
                  refine ⟨24130702489689474503876885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16087134993126316335917923 24130702489689474503876885)
                  ·
                    refine ⟨1131126679204194117369229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24130702489689474503876885 1131126679204194117369229)
                    ·
                      rfl

theorem cell22_3304292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 2, 1, 6].length) (baseStart_3304292 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3304292 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3304292 prefixEnd_3304292 := by exact prefixLift 3304292
  have htrace : WordTrace (prefixWord ++ tailWord_3304292) baseStart_3304292 baseEnd_3304292 := by
    simpa [prefixWord, tailWord_3304292, baseEnd_3304292] using wordTrace_append hprefix tailTrace_3304292
  have hstable : (prefixWord ++ tailWord_3304292).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3304292).length < 2 ^ (prefixWord ++ tailWord_3304292).sum := by decide
  have hdescent : baseEnd_3304292 < baseStart_3304292 := by decide
  rcases family_descends (prefixWord ++ tailWord_3304292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3304307 : List Nat := [1, 1, 1, 2, 2, 1, 8, 6]
def baseStart_3304307 : Nat := 118140960795 + 3304307 * 2 ^ 59
def prefixEnd_3304307 : Nat := 4983230072969 + 3 ^ 40 * 3304307 * 2
def baseEnd_3304307 : Nat := 125681312667859897582687

theorem tailTrace_3304307 : CollatzResearch.WordTrace tailWord_3304307 prefixEnd_3304307 125681312667859897582687 := by
  unfold tailWord_3304307
  simp only [CollatzResearch.WordTrace]
  refine ⟨120517977240067544552047175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80345318160045029701364783 120517977240067544552047175)
  ·
    refine ⟨180776965860101316828070763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120517977240067544552047175 180776965860101316828070763)
    ·
      refine ⟨271165448790151975242106145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180776965860101316828070763 271165448790151975242106145)
      ·
        refine ⟨203374086592613981431579609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 271165448790151975242106145 203374086592613981431579609)
        ·
          refine ⟨152530564944460486073684707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 203374086592613981431579609 152530564944460486073684707)
          ·
            refine ⟨228795847416690729110527061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152530564944460486073684707 228795847416690729110527061)
            ·
              refine ⟨2681201336914344481763989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 228795847416690729110527061 2681201336914344481763989)
              ·
                refine ⟨125681312667859897582687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2681201336914344481763989 125681312667859897582687)
                ·
                  rfl

theorem cell22_3304307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 8, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 8, 6].length) (baseStart_3304307 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3304307 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3304307 prefixEnd_3304307 := by exact prefixLift 3304307
  have htrace : WordTrace (prefixWord ++ tailWord_3304307) baseStart_3304307 baseEnd_3304307 := by
    simpa [prefixWord, tailWord_3304307, baseEnd_3304307] using wordTrace_append hprefix tailTrace_3304307
  have hstable : (prefixWord ++ tailWord_3304307).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3304307).length < 2 ^ (prefixWord ++ tailWord_3304307).sum := by decide
  have hdescent : baseEnd_3304307 < baseStart_3304307 := by decide
  rcases family_descends (prefixWord ++ tailWord_3304307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3304431 : List Nat := [1, 1, 2, 1, 4, 4, 2, 3, 4]
def baseStart_3304431 : Nat := 118140960795 + 3304431 * 2 ^ 59
def prefixEnd_3304431 : Nat := 4983230072969 + 3 ^ 40 * 3304431 * 2
def baseEnd_3304431 : Nat := 377058087248281362714601

theorem tailTrace_3304431 : CollatzResearch.WordTrace tailWord_3304431 prefixEnd_3304431 377058087248281362714601 := by
  unfold tailWord_3304431
  simp only [CollatzResearch.WordTrace]
  refine ⟨120522499891618313729561147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80348333261078875819707431 120522499891618313729561147)
  ·
    refine ⟨180783749837427470594341721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120522499891618313729561147 180783749837427470594341721)
    ·
      refine ⟨135587812378070602945756291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180783749837427470594341721 135587812378070602945756291)
      ·
        refine ⟨203381718567105904418634437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135587812378070602945756291 203381718567105904418634437)
        ·
          refine ⟨38134072231332357078493957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 203381718567105904418634437 38134072231332357078493957)
          ·
            refine ⟨7150138543374816952217617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38134072231332357078493957 7150138543374816952217617)
            ·
              refine ⟨5362603907531112714163213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7150138543374816952217617 5362603907531112714163213)
              ·
                refine ⟨2010976465324167267811205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5362603907531112714163213 2010976465324167267811205)
                ·
                  refine ⟨377058087248281362714601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2010976465324167267811205 377058087248281362714601)
                  ·
                    rfl

theorem cell22_3304431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 2, 3, 4].length) (baseStart_3304431 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3304431 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3304431 prefixEnd_3304431 := by exact prefixLift 3304431
  have htrace : WordTrace (prefixWord ++ tailWord_3304431) baseStart_3304431 baseEnd_3304431 := by
    simpa [prefixWord, tailWord_3304431, baseEnd_3304431] using wordTrace_append hprefix tailTrace_3304431
  have hstable : (prefixWord ++ tailWord_3304431).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3304431).length < 2 ^ (prefixWord ++ tailWord_3304431).sum := by decide
  have hdescent : baseEnd_3304431 < baseStart_3304431 := by decide
  rcases family_descends (prefixWord ++ tailWord_3304431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3304433 : List Nat := [1, 2, 2, 2, 4, 3, 2, 1, 1, 4]
def baseStart_3304433 : Nat := 118140960795 + 3304433 * 2 ^ 59
def prefixEnd_3304433 : Nat := 4983230072969 + 3 ^ 40 * 3304433 * 2
def baseEnd_3304433 : Nat := 1131174946385716749593797

theorem tailTrace_3304433 : CollatzResearch.WordTrace tailWord_3304433 prefixEnd_3304433 1131174946385716749593797 := by
  unfold tailWord_3304433
  simp only [CollatzResearch.WordTrace]
  refine ⟨120522572837611068071133953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80348381891740712047422635 120522572837611068071133953)
  ·
    refine ⟨90391929628208301053350465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120522572837611068071133953 90391929628208301053350465)
    ·
      refine ⟨67793947221156225790012849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90391929628208301053350465 67793947221156225790012849)
      ·
        refine ⟨50845460415867169342509637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67793947221156225790012849 50845460415867169342509637)
        ·
          refine ⟨9533523827975094251720557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50845460415867169342509637 9533523827975094251720557)
          ·
            refine ⟨3575071435490660344395209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9533523827975094251720557 3575071435490660344395209)
            ·
              refine ⟨2681303576617995258296407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3575071435490660344395209 2681303576617995258296407)
              ·
                refine ⟨4021955364926992887444611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2681303576617995258296407 4021955364926992887444611)
                ·
                  refine ⟨6032933047390489331166917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4021955364926992887444611 6032933047390489331166917)
                  ·
                    refine ⟨1131174946385716749593797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6032933047390489331166917 1131174946385716749593797)
                    ·
                      rfl

theorem cell22_3304433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 2, 1, 1, 4].length) (baseStart_3304433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3304433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3304433 prefixEnd_3304433 := by exact prefixLift 3304433
  have htrace : WordTrace (prefixWord ++ tailWord_3304433) baseStart_3304433 baseEnd_3304433 := by
    simpa [prefixWord, tailWord_3304433, baseEnd_3304433] using wordTrace_append hprefix tailTrace_3304433
  have hstable : (prefixWord ++ tailWord_3304433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3304433).length < 2 ^ (prefixWord ++ tailWord_3304433).sum := by decide
  have hdescent : baseEnd_3304433 < baseStart_3304433 := by decide
  rcases family_descends (prefixWord ++ tailWord_3304433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3304504 : List Nat := [2, 1, 2, 1, 5, 1, 2, 1, 7]
def baseStart_3304504 : Nat := 118140960795 + 3304504 * 2 ^ 59
def prefixEnd_3304504 : Nat := 4983230072969 + 3 ^ 40 * 3304504 * 2
def baseEnd_3304504 : Nat := 377066417045565410356193

theorem tailTrace_3304504 : CollatzResearch.WordTrace tailWord_3304504 prefixEnd_3304504 377066417045565410356193 := by
  unfold tailWord_3304504
  simp only [CollatzResearch.WordTrace]
  refine ⟨60262581210176923598484283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80350108280235898131312377 60262581210176923598484283)
  ·
    refine ⟨90393871815265385397726425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60262581210176923598484283 90393871815265385397726425)
    ·
      refine ⟨67795403861449039048294819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90393871815265385397726425 67795403861449039048294819)
      ·
        refine ⟨101693105792173558572442229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67795403861449039048294819 101693105792173558572442229)
        ·
          refine ⟨9533728668016271116166459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 101693105792173558572442229 9533728668016271116166459)
          ·
            refine ⟨14300593002024406674249689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9533728668016271116166459 14300593002024406674249689)
            ·
              refine ⟨10725444751518305005687267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14300593002024406674249689 10725444751518305005687267)
              ·
                refine ⟨16088167127277457508530901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10725444751518305005687267 16088167127277457508530901)
                ·
                  refine ⟨377066417045565410356193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16088167127277457508530901 377066417045565410356193)
                  ·
                    rfl

theorem cell22_3304504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 2, 1, 7].length) (baseStart_3304504 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3304504 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3304504 prefixEnd_3304504 := by exact prefixLift 3304504
  have htrace : WordTrace (prefixWord ++ tailWord_3304504) baseStart_3304504 baseEnd_3304504 := by
    simpa [prefixWord, tailWord_3304504, baseEnd_3304504] using wordTrace_append hprefix tailTrace_3304504
  have hstable : (prefixWord ++ tailWord_3304504).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3304504).length < 2 ^ (prefixWord ++ tailWord_3304504).sum := by decide
  have hdescent : baseEnd_3304504 < baseStart_3304504 := by decide
  rcases family_descends (prefixWord ++ tailWord_3304504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3304508 : List Nat := [2, 2, 2, 2, 2, 4, 1, 1, 3, 3]
def baseStart_3304508 : Nat := 118140960795 + 3304508 * 2 ^ 59
def prefixEnd_3304508 : Nat := 4983230072969 + 3 ^ 40 * 3304508 * 2
def baseEnd_3304508 : Nat := 1131200620418441553968567

theorem tailTrace_3304508 : CollatzResearch.WordTrace tailWord_3304508 prefixEnd_3304508 1131200620418441553968567 := by
  unfold tailWord_3304508
  simp only [CollatzResearch.WordTrace]
  refine ⟨60262654156169677940057089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80350205541559570586742785 60262654156169677940057089)
  ·
    refine ⟨45196990617127258455042817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60262654156169677940057089 45196990617127258455042817)
    ·
      refine ⟨33897742962845443841282113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45196990617127258455042817 33897742962845443841282113)
      ·
        refine ⟨25423307222134082880961585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33897742962845443841282113 25423307222134082880961585)
        ·
          refine ⟨19067480416600562160721189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25423307222134082880961585 19067480416600562160721189)
          ·
            refine ⟨3575152578112605405135223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19067480416600562160721189 3575152578112605405135223)
            ·
              refine ⟨5362728867168908107702835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3575152578112605405135223 5362728867168908107702835)
              ·
                refine ⟨8044093300753362161554253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5362728867168908107702835 8044093300753362161554253)
                ·
                  refine ⟨3016534987782510810582845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8044093300753362161554253 3016534987782510810582845)
                  ·
                    refine ⟨1131200620418441553968567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3016534987782510810582845 1131200620418441553968567)
                    ·
                      rfl

theorem cell22_3304508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 1, 1, 3, 3].length) (baseStart_3304508 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3304508 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3304508 prefixEnd_3304508 := by exact prefixLift 3304508
  have htrace : WordTrace (prefixWord ++ tailWord_3304508) baseStart_3304508 baseEnd_3304508 := by
    simpa [prefixWord, tailWord_3304508, baseEnd_3304508] using wordTrace_append hprefix tailTrace_3304508
  have hstable : (prefixWord ++ tailWord_3304508).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3304508).length < 2 ^ (prefixWord ++ tailWord_3304508).sum := by decide
  have hdescent : baseEnd_3304508 < baseStart_3304508 := by decide
  rcases family_descends (prefixWord ++ tailWord_3304508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3304566 : List Nat := [5, 1, 1, 2, 1, 1, 2, 3, 6]
def baseStart_3304566 : Nat := 118140960795 + 3304566 * 2 ^ 59
def prefixEnd_3304566 : Nat := 4983230072969 + 3 ^ 40 * 3304566 * 2
def baseEnd_3304566 : Nat := 377073491667916245339463

theorem tailTrace_3304566 : CollatzResearch.WordTrace tailWord_3304566 prefixEnd_3304566 377073491667916245339463 := by
  unfold tailWord_3304566
  simp only [CollatzResearch.WordTrace]
  refine ⟨7532963984133076986607847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 80351615830752821190483701 7532963984133076986607847)
  ·
    refine ⟨11299445976199615479911771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7532963984133076986607847 11299445976199615479911771)
    ·
      refine ⟨16949168964299423219867657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11299445976199615479911771 16949168964299423219867657)
      ·
        refine ⟨12711876723224567414900743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16949168964299423219867657 12711876723224567414900743)
        ·
          refine ⟨19067815084836851122351115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12711876723224567414900743 19067815084836851122351115)
          ·
            refine ⟨28601722627255276683526673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19067815084836851122351115 28601722627255276683526673)
            ·
              refine ⟨21451291970441457512645005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28601722627255276683526673 21451291970441457512645005)
              ·
                refine ⟨8044234488915546567241877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21451291970441457512645005 8044234488915546567241877)
                ·
                  refine ⟨377073491667916245339463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8044234488915546567241877 377073491667916245339463)
                  ·
                    rfl

theorem cell22_3304566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 3, 6].length) (baseStart_3304566 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3304566 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3304566 prefixEnd_3304566 := by exact prefixLift 3304566
  have htrace : WordTrace (prefixWord ++ tailWord_3304566) baseStart_3304566 baseEnd_3304566 := by
    simpa [prefixWord, tailWord_3304566, baseEnd_3304566] using wordTrace_append hprefix tailTrace_3304566
  have hstable : (prefixWord ++ tailWord_3304566).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3304566).length < 2 ^ (prefixWord ++ tailWord_3304566).sum := by decide
  have hdescent : baseEnd_3304566 < baseStart_3304566 := by decide
  rcases family_descends (prefixWord ++ tailWord_3304566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3304579 : List Nat := [1, 1, 1, 3, 3, 2, 2, 2, 1, 6]
def baseStart_3304579 : Nat := 118140960795 + 3304579 * 2 ^ 59
def prefixEnd_3304579 : Nat := 4983230072969 + 3 ^ 40 * 3304579 * 2
def baseEnd_3304579 : Nat := 1131224925169421035443349

theorem tailTrace_3304579 : CollatzResearch.WordTrace tailWord_3304579 prefixEnd_3304579 1131224925169421035443349 := by
  unfold tailWord_3304579
  simp only [CollatzResearch.WordTrace]
  refine ⟨120527897895082135005948791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80351931930054756670632527 120527897895082135005948791)
  ·
    refine ⟨180791846842623202508923187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120527897895082135005948791 180791846842623202508923187)
    ·
      refine ⟨271187770263934803763384781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180791846842623202508923187 271187770263934803763384781)
      ·
        refine ⟨101695413848975551411269293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 271187770263934803763384781 101695413848975551411269293)
        ·
          refine ⟨38135780193365831779225985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101695413848975551411269293 38135780193365831779225985)
          ·
            refine ⟨28601835145024373834419489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38135780193365831779225985 28601835145024373834419489)
            ·
              refine ⟨21451376358768280375814617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28601835145024373834419489 21451376358768280375814617)
              ·
                refine ⟨16088532269076210281860963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21451376358768280375814617 16088532269076210281860963)
                ·
                  refine ⟨24132798403614315422791445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16088532269076210281860963 24132798403614315422791445)
                  ·
                    refine ⟨1131224925169421035443349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24132798403614315422791445 1131224925169421035443349)
                    ·
                      rfl

theorem cell22_3304579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 2, 1, 6].length) (baseStart_3304579 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3304579 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3304579 prefixEnd_3304579 := by exact prefixLift 3304579
  have htrace : WordTrace (prefixWord ++ tailWord_3304579) baseStart_3304579 baseEnd_3304579 := by
    simpa [prefixWord, tailWord_3304579, baseEnd_3304579] using wordTrace_append hprefix tailTrace_3304579
  have hstable : (prefixWord ++ tailWord_3304579).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3304579).length < 2 ^ (prefixWord ++ tailWord_3304579).sum := by decide
  have hdescent : baseEnd_3304579 < baseStart_3304579 := by decide
  rcases family_descends (prefixWord ++ tailWord_3304579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3304615 : List Nat := [1, 1, 6, 2, 1, 1, 3, 2, 2, 3]
def baseStart_3304615 : Nat := 118140960795 + 3304615 * 2 ^ 59
def prefixEnd_3304615 : Nat := 4983230072969 + 3 ^ 40 * 3304615 * 2
def baseEnd_3304615 : Nat := 1131237248705128941543239

theorem tailTrace_3304615 : CollatzResearch.WordTrace tailWord_3304615 prefixEnd_3304615 1131237248705128941543239 := by
  unfold tailWord_3304615
  simp only [CollatzResearch.WordTrace]
  refine ⟨120529210922951713154259299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80352807281967808769506199 120529210922951713154259299)
  ·
    refine ⟨180793816384427569731388949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120529210922951713154259299 180793816384427569731388949)
    ·
      refine ⟨8474710143020042331158857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 180793816384427569731388949 8474710143020042331158857)
      ·
        refine ⟨6356032607265031748369143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8474710143020042331158857 6356032607265031748369143)
        ·
          refine ⟨9534048910897547622553715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6356032607265031748369143 9534048910897547622553715)
          ·
            refine ⟨14301073366346321433830573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9534048910897547622553715 14301073366346321433830573)
            ·
              refine ⟨5362902512379870537686465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14301073366346321433830573 5362902512379870537686465)
              ·
                refine ⟨4022176884284902903264849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5362902512379870537686465 4022176884284902903264849)
                ·
                  refine ⟨3016632663213677177448637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4022176884284902903264849 3016632663213677177448637)
                  ·
                    refine ⟨1131237248705128941543239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3016632663213677177448637 1131237248705128941543239)
                    ·
                      rfl

theorem cell22_3304615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 3, 2, 2, 3].length) (baseStart_3304615 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3304615 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3304615 prefixEnd_3304615 := by exact prefixLift 3304615
  have htrace : WordTrace (prefixWord ++ tailWord_3304615) baseStart_3304615 baseEnd_3304615 := by
    simpa [prefixWord, tailWord_3304615, baseEnd_3304615] using wordTrace_append hprefix tailTrace_3304615
  have hstable : (prefixWord ++ tailWord_3304615).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3304615).length < 2 ^ (prefixWord ++ tailWord_3304615).sum := by decide
  have hdescent : baseEnd_3304615 < baseStart_3304615 := by decide
  rcases family_descends (prefixWord ++ tailWord_3304615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3304677 : List Nat := [1, 3, 1, 4, 4, 1, 1, 1, 3, 3]
def baseStart_3304677 : Nat := 118140960795 + 3304677 * 2 ^ 59
def prefixEnd_3304677 : Nat := 4983230072969 + 3 ^ 40 * 3304677 * 2
def baseEnd_3304677 : Nat := 1131258472572181446493049

theorem tailTrace_3304677 : CollatzResearch.WordTrace tailWord_3304677 prefixEnd_3304677 1131258472572181446493049 := by
  unfold tailWord_3304677
  simp only [CollatzResearch.WordTrace]
  refine ⟨120531472248727097743016285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80354314832484731828677523 120531472248727097743016285)
  ·
    refine ⟨45199302093272661653631107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120531472248727097743016285 45199302093272661653631107)
    ·
      refine ⟨67798953139908992480446661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45199302093272661653631107 67798953139908992480446661)
      ·
        refine ⟨12712303713732936090083749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67798953139908992480446661 12712303713732936090083749)
        ·
          refine ⟨2383556946324925516890703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12712303713732936090083749 2383556946324925516890703)
          ·
            refine ⟨3575335419487388275336055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2383556946324925516890703 3575335419487388275336055)
            ·
              refine ⟨5363003129231082413004083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3575335419487388275336055 5363003129231082413004083)
              ·
                refine ⟨8044504693846623619506125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5363003129231082413004083 8044504693846623619506125)
                ·
                  refine ⟨3016689260192483857314797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8044504693846623619506125 3016689260192483857314797)
                  ·
                    refine ⟨1131258472572181446493049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3016689260192483857314797 1131258472572181446493049)
                    ·
                      rfl

theorem cell22_3304677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 1, 1, 3, 3].length) (baseStart_3304677 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3304677 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3304677 prefixEnd_3304677 := by exact prefixLift 3304677
  have htrace : WordTrace (prefixWord ++ tailWord_3304677) baseStart_3304677 baseEnd_3304677 := by
    simpa [prefixWord, tailWord_3304677, baseEnd_3304677] using wordTrace_append hprefix tailTrace_3304677
  have hstable : (prefixWord ++ tailWord_3304677).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3304677).length < 2 ^ (prefixWord ++ tailWord_3304677).sum := by decide
  have hdescent : baseEnd_3304677 < baseStart_3304677 := by decide
  rcases family_descends (prefixWord ++ tailWord_3304677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3304703 : List Nat := [1, 1, 2, 2, 1, 5, 3, 2, 1, 4]
def baseStart_3304703 : Nat := 118140960795 + 3304703 * 2 ^ 59
def prefixEnd_3304703 : Nat := 4983230072969 + 3 ^ 40 * 3304703 * 2
def baseEnd_3304703 : Nat := 1131267372903526045342969

theorem tailTrace_3304703 : CollatzResearch.WordTrace tailWord_3304703 prefixEnd_3304703 1131267372903526045342969 := by
  unfold tailWord_3304703
  simp only [CollatzResearch.WordTrace]
  refine ⟨120532420546632904183462763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80354947031088602788975175 120532420546632904183462763)
  ·
    refine ⟨180798630819949356275194145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120532420546632904183462763 180798630819949356275194145)
    ·
      refine ⟨135598973114962017206395609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180798630819949356275194145 135598973114962017206395609)
      ·
        refine ⟨101699229836221512904796707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135598973114962017206395609 101699229836221512904796707)
        ·
          refine ⟨152548844754332269357195061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101699229836221512904796707 152548844754332269357195061)
          ·
            refine ⟨14301454195718650252237037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 152548844754332269357195061 14301454195718650252237037)
            ·
              refine ⟨5363045323394493844588889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14301454195718650252237037 5363045323394493844588889)
              ·
                refine ⟨4022283992545870383441667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5363045323394493844588889 4022283992545870383441667)
                ·
                  refine ⟨6033425988818805575162501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4022283992545870383441667 6033425988818805575162501)
                  ·
                    refine ⟨1131267372903526045342969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6033425988818805575162501 1131267372903526045342969)
                    ·
                      rfl

theorem cell22_3304703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 3, 2, 1, 4].length) (baseStart_3304703 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3304703 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3304703 prefixEnd_3304703 := by exact prefixLift 3304703
  have htrace : WordTrace (prefixWord ++ tailWord_3304703) baseStart_3304703 baseEnd_3304703 := by
    simpa [prefixWord, tailWord_3304703, baseEnd_3304703] using wordTrace_append hprefix tailTrace_3304703
  have hstable : (prefixWord ++ tailWord_3304703).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3304703).length < 2 ^ (prefixWord ++ tailWord_3304703).sum := by decide
  have hdescent : baseEnd_3304703 < baseStart_3304703 := by decide
  rcases family_descends (prefixWord ++ tailWord_3304703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3304716 : List Nat := [2, 2, 1, 2, 2, 3, 1, 1, 3, 5]
def baseStart_3304716 : Nat := 118140960795 + 3304716 * 2 ^ 59
def prefixEnd_3304716 : Nat := 4983230072969 + 3 ^ 40 * 3304716 * 2
def baseEnd_3304716 : Nat := 1131271823069198344767929

theorem tailTrace_3304716 : CollatzResearch.WordTrace tailWord_3304716 prefixEnd_3304716 1131271823069198344767929 := by
  unfold tailWord_3304716
  simp only [CollatzResearch.WordTrace]
  refine ⟨60266447347792903701843001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80355263130390538269124001 60266447347792903701843001)
  ·
    refine ⟨45199835510844677776382251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60266447347792903701843001 45199835510844677776382251)
    ·
      refine ⟨67799753266267016664573377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45199835510844677776382251 67799753266267016664573377)
      ·
        refine ⟨50849814949700262498430033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67799753266267016664573377 50849814949700262498430033)
        ·
          refine ⟨38137361212275196873822525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50849814949700262498430033 38137361212275196873822525)
          ·
            refine ⟨14301510454603198827683447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38137361212275196873822525 14301510454603198827683447)
            ·
              refine ⟨21452265681904798241525171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14301510454603198827683447 21452265681904798241525171)
              ·
                refine ⟨32178398522857197362287757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21452265681904798241525171 32178398522857197362287757)
                ·
                  refine ⟨12066899446071449010857909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32178398522857197362287757 12066899446071449010857909)
                  ·
                    refine ⟨1131271823069198344767929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12066899446071449010857909 1131271823069198344767929)
                    ·
                      rfl

theorem cell22_3304716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 1, 3, 5].length) (baseStart_3304716 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3304716 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3304716 prefixEnd_3304716 := by exact prefixLift 3304716
  have htrace : WordTrace (prefixWord ++ tailWord_3304716) baseStart_3304716 baseEnd_3304716 := by
    simpa [prefixWord, tailWord_3304716, baseEnd_3304716] using wordTrace_append hprefix tailTrace_3304716
  have hstable : (prefixWord ++ tailWord_3304716).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3304716).length < 2 ^ (prefixWord ++ tailWord_3304716).sum := by decide
  have hdescent : baseEnd_3304716 < baseStart_3304716 := by decide
  rcases family_descends (prefixWord ++ tailWord_3304716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3304735 : List Nat := [1, 1, 2, 4, 4, 1, 1, 4, 4]
def baseStart_3304735 : Nat := 118140960795 + 3304735 * 2 ^ 59
def prefixEnd_3304735 : Nat := 4983230072969 + 3 ^ 40 * 3304735 * 2
def baseEnd_3304735 : Nat := 377092775719162876180957

theorem tailTrace_3304735 : CollatzResearch.WordTrace tailWord_3304735 prefixEnd_3304735 377092775719162876180957 := by
  unfold tailWord_3304735
  simp only [CollatzResearch.WordTrace]
  refine ⟨120533587682516973648627659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80355725121677982432418439 120533587682516973648627659)
  ·
    refine ⟨180800381523775460472941489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120533587682516973648627659 180800381523775460472941489)
    ·
      refine ⟨135600286142831595354706117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180800381523775460472941489 135600286142831595354706117)
      ·
        refine ⟨25425053651780924129007397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 135600286142831595354706117 25425053651780924129007397)
        ·
          refine ⟨4767197559708923274188887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25425053651780924129007397 4767197559708923274188887)
          ·
            refine ⟨7150796339563384911283331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4767197559708923274188887 7150796339563384911283331)
            ·
              refine ⟨10726194509345077366924997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7150796339563384911283331 10726194509345077366924997)
              ·
                refine ⟨2011161470502202006298437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10726194509345077366924997 2011161470502202006298437)
                ·
                  refine ⟨377092775719162876180957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2011161470502202006298437 377092775719162876180957)
                  ·
                    rfl

theorem cell22_3304735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 1, 4, 4].length) (baseStart_3304735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3304735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3304735 prefixEnd_3304735 := by exact prefixLift 3304735
  have htrace : WordTrace (prefixWord ++ tailWord_3304735) baseStart_3304735 baseEnd_3304735 := by
    simpa [prefixWord, tailWord_3304735, baseEnd_3304735] using wordTrace_append hprefix tailTrace_3304735
  have hstable : (prefixWord ++ tailWord_3304735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3304735).length < 2 ^ (prefixWord ++ tailWord_3304735).sum := by decide
  have hdescent : baseEnd_3304735 < baseStart_3304735 := by decide
  rcases family_descends (prefixWord ++ tailWord_3304735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3304765 : List Nat := [1, 4, 1, 5, 1, 1, 1, 1, 1, 6]
def baseStart_3304765 : Nat := 118140960795 + 3304765 * 2 ^ 59
def prefixEnd_3304765 : Nat := 4983230072969 + 3 ^ 40 * 3304765 * 2
def baseEnd_3304765 : Nat := 1131288596770578550292779

theorem tailTrace_3304765 : CollatzResearch.WordTrace tailWord_3304765 prefixEnd_3304765 1131288596770578550292779 := by
  unfold tailWord_3304765
  simp only [CollatzResearch.WordTrace]
  refine ⟨120534681872408288772219749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80356454581605525848146499 120534681872408288772219749)
  ·
    refine ⟨22600252851076554144791203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 120534681872408288772219749 22600252851076554144791203)
    ·
      refine ⟨33900379276614831217186805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22600252851076554144791203 33900379276614831217186805)
      ·
        refine ⟨3178160557182640426611263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 33900379276614831217186805 3178160557182640426611263)
        ·
          refine ⟨4767240835773960639916895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3178160557182640426611263 4767240835773960639916895)
          ·
            refine ⟨7150861253660940959875343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4767240835773960639916895 7150861253660940959875343)
            ·
              refine ⟨10726291880491411439813015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7150861253660940959875343 10726291880491411439813015)
              ·
                refine ⟨16089437820737117159719523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10726291880491411439813015 16089437820737117159719523)
                ·
                  refine ⟨24134156731105675739579285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16089437820737117159719523 24134156731105675739579285)
                  ·
                    refine ⟨1131288596770578550292779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24134156731105675739579285 1131288596770578550292779)
                    ·
                      rfl

theorem cell22_3304765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 1, 1, 1, 6].length) (baseStart_3304765 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3304765 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3304765 prefixEnd_3304765 := by exact prefixLift 3304765
  have htrace : WordTrace (prefixWord ++ tailWord_3304765) baseStart_3304765 baseEnd_3304765 := by
    simpa [prefixWord, tailWord_3304765, baseEnd_3304765] using wordTrace_append hprefix tailTrace_3304765
  have hstable : (prefixWord ++ tailWord_3304765).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3304765).length < 2 ^ (prefixWord ++ tailWord_3304765).sum := by decide
  have hdescent : baseEnd_3304765 < baseStart_3304765 := by decide
  rcases family_descends (prefixWord ++ tailWord_3304765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3304814 : List Nat := [4, 1, 2, 4, 2, 1, 2, 6]
def baseStart_3304814 : Nat := 118140960795 + 3304814 * 2 ^ 59
def prefixEnd_3304814 : Nat := 4983230072969 + 3 ^ 40 * 3304814 * 2
def baseEnd_3304814 : Nat := 125700596719106528424181

theorem tailTrace_3304814 : CollatzResearch.WordTrace tailWord_3304814 prefixEnd_3304814 125700596719106528424181 := by
  unfold tailWord_3304814
  simp only [CollatzResearch.WordTrace]
  refine ⟨15067058631153846267594187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80357646032820513427168997 15067058631153846267594187)
  ·
    refine ⟨22600587946730769401391281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15067058631153846267594187 22600587946730769401391281)
    ·
      refine ⟨16950440960048077051043461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22600587946730769401391281 16950440960048077051043461)
      ·
        refine ⟨3178207680009014447070649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16950440960048077051043461 3178207680009014447070649)
        ·
          refine ⟨2383655760006760835302987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3178207680009014447070649 2383655760006760835302987)
          ·
            refine ⟨3575483640010141252954481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2383655760006760835302987 3575483640010141252954481)
            ·
              refine ⟨2681612730007605939715861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3575483640010141252954481 2681612730007605939715861)
              ·
                refine ⟨125700596719106528424181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2681612730007605939715861 125700596719106528424181)
                ·
                  rfl

theorem cell22_3304814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 2, 6].length) (baseStart_3304814 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3304814 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3304814 prefixEnd_3304814 := by exact prefixLift 3304814
  have htrace : WordTrace (prefixWord ++ tailWord_3304814) baseStart_3304814 baseEnd_3304814 := by
    simpa [prefixWord, tailWord_3304814, baseEnd_3304814] using wordTrace_append hprefix tailTrace_3304814
  have hstable : (prefixWord ++ tailWord_3304814).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3304814).length < 2 ^ (prefixWord ++ tailWord_3304814).sum := by decide
  have hdescent : baseEnd_3304814 < baseStart_3304814 := by decide
  rcases family_descends (prefixWord ++ tailWord_3304814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3304846 : List Nat := [4, 1, 1, 4, 2, 1, 3, 2, 1, 3]
def baseStart_3304846 : Nat := 118140960795 + 3304846 * 2 ^ 59
def prefixEnd_3304846 : Nat := 4983230072969 + 3 ^ 40 * 3304846 * 2
def baseEnd_3304846 : Nat := 1131316324725921339017531

theorem tailTrace_3304846 : CollatzResearch.WordTrace tailWord_3304846 prefixEnd_3304846 1131316324725921339017531 := by
  unfold tailWord_3304846
  simp only [CollatzResearch.WordTrace]
  refine ⟨15067204523139354950739799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80358424123409893070612261 15067204523139354950739799)
  ·
    refine ⟨22600806784709032426109699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15067204523139354950739799 22600806784709032426109699)
    ·
      refine ⟨33901210177063548639164549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22600806784709032426109699 33901210177063548639164549)
      ·
        refine ⟨6356476908199415369843353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33901210177063548639164549 6356476908199415369843353)
        ·
          refine ⟨4767357681149561527382515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6356476908199415369843353 4767357681149561527382515)
          ·
            refine ⟨7151036521724342291073773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4767357681149561527382515 7151036521724342291073773)
            ·
              refine ⟨2681638695646628359152665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7151036521724342291073773 2681638695646628359152665)
              ·
                refine ⟨2011229021734971269364499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2681638695646628359152665 2011229021734971269364499)
                ·
                  refine ⟨3016843532602456904046749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2011229021734971269364499 3016843532602456904046749)
                  ·
                    refine ⟨1131316324725921339017531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3016843532602456904046749 1131316324725921339017531)
                    ·
                      rfl

theorem cell22_3304846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 3, 2, 1, 3].length) (baseStart_3304846 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3304846 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3304846 prefixEnd_3304846 := by exact prefixLift 3304846
  have htrace : WordTrace (prefixWord ++ tailWord_3304846) baseStart_3304846 baseEnd_3304846 := by
    simpa [prefixWord, tailWord_3304846, baseEnd_3304846] using wordTrace_append hprefix tailTrace_3304846
  have hstable : (prefixWord ++ tailWord_3304846).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3304846).length < 2 ^ (prefixWord ++ tailWord_3304846).sum := by decide
  have hdescent : baseEnd_3304846 < baseStart_3304846 := by decide
  rcases family_descends (prefixWord ++ tailWord_3304846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3304853 : List Nat := [1, 3, 2, 1, 1, 2, 5, 1, 6]
def baseStart_3304853 : Nat := 118140960795 + 3304853 * 2 ^ 59
def prefixEnd_3304853 : Nat := 4983230072969 + 3 ^ 40 * 3304853 * 2
def baseEnd_3304853 : Nat := 377106240322991884697503

theorem tailTrace_3304853 : CollatzResearch.WordTrace tailWord_3304853 prefixEnd_3304853 377106240322991884697503 := by
  unfold tailWord_3304853
  simp only [CollatzResearch.WordTrace]
  refine ⟨120537891496089479801423213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80358594330726319867615475 120537891496089479801423213)
  ·
    refine ⟨45201709311033554925533705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120537891496089479801423213 45201709311033554925533705)
    ·
      refine ⟨33901281983275166194150279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45201709311033554925533705 33901281983275166194150279)
      ·
        refine ⟨50851922974912749291225419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33901281983275166194150279 50851922974912749291225419)
        ·
          refine ⟨76277884462369123936838129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50851922974912749291225419 76277884462369123936838129)
          ·
            refine ⟨57208413346776842952628597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76277884462369123936838129 57208413346776842952628597)
            ·
              refine ⟨5363288751260329026808931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 57208413346776842952628597 5363288751260329026808931)
              ·
                refine ⟨8044933126890493540213397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5363288751260329026808931 8044933126890493540213397)
                ·
                  refine ⟨377106240322991884697503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8044933126890493540213397 377106240322991884697503)
                  ·
                    rfl

theorem cell22_3304853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 5, 1, 6].length) (baseStart_3304853 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3304853 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3304853 prefixEnd_3304853 := by exact prefixLift 3304853
  have htrace : WordTrace (prefixWord ++ tailWord_3304853) baseStart_3304853 baseEnd_3304853 := by
    simpa [prefixWord, tailWord_3304853, baseEnd_3304853] using wordTrace_append hprefix tailTrace_3304853
  have hstable : (prefixWord ++ tailWord_3304853).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3304853).length < 2 ^ (prefixWord ++ tailWord_3304853).sum := by decide
  have hdescent : baseEnd_3304853 < baseStart_3304853 := by decide
  rcases family_descends (prefixWord ++ tailWord_3304853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3304868 : List Nat := [2, 3, 1, 2, 1, 1, 1, 5, 1, 5]
def baseStart_3304868 : Nat := 118140960795 + 3304868 * 2 ^ 59
def prefixEnd_3304868 : Nat := 4983230072969 + 3 ^ 40 * 3304868 * 2
def baseEnd_3304868 : Nat := 1131323855775520614967463

theorem tailTrace_3304868 : CollatzResearch.WordTrace tailWord_3304868 prefixEnd_3304868 1131323855775520614967463 := by
  unfold tailWord_3304868
  simp only [CollatzResearch.WordTrace]
  refine ⟨60269219295517568681609629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80358959060690091575479505 60269219295517568681609629)
  ·
    refine ⟨22600957235819088255603611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60269219295517568681609629 22600957235819088255603611)
    ·
      refine ⟨33901435853728632383405417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22600957235819088255603611 33901435853728632383405417)
      ·
        refine ⟨25426076890296474287554063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33901435853728632383405417 25426076890296474287554063)
        ·
          refine ⟨38139115335444711431331095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25426076890296474287554063 38139115335444711431331095)
          ·
            refine ⟨57208673003167067146996643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38139115335444711431331095 57208673003167067146996643)
            ·
              refine ⟨85813009504750600720494965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57208673003167067146996643 85813009504750600720494965)
              ·
                refine ⟨8044969641070368817546403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 85813009504750600720494965 8044969641070368817546403)
                ·
                  refine ⟨12067454461605553226319605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8044969641070368817546403 12067454461605553226319605)
                  ·
                    refine ⟨1131323855775520614967463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12067454461605553226319605 1131323855775520614967463)
                    ·
                      rfl

theorem cell22_3304868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 5, 1, 5].length) (baseStart_3304868 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3304868 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3304868 prefixEnd_3304868 := by exact prefixLift 3304868
  have htrace : WordTrace (prefixWord ++ tailWord_3304868) baseStart_3304868 baseEnd_3304868 := by
    simpa [prefixWord, tailWord_3304868, baseEnd_3304868] using wordTrace_append hprefix tailTrace_3304868
  have hstable : (prefixWord ++ tailWord_3304868).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3304868).length < 2 ^ (prefixWord ++ tailWord_3304868).sum := by decide
  have hdescent : baseEnd_3304868 < baseStart_3304868 := by decide
  rcases family_descends (prefixWord ++ tailWord_3304868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3304872 : List Nat := [2, 1, 6, 1, 2, 1, 1, 1, 3, 4]
def baseStart_3304872 : Nat := 118140960795 + 3304872 * 2 ^ 59
def prefixEnd_3304872 : Nat := 4983230072969 + 3 ^ 40 * 3304872 * 2
def baseEnd_3304872 : Nat := 1131325225057265937867451

theorem tailTrace_3304872 : CollatzResearch.WordTrace tailWord_3304872 prefixEnd_3304872 1131325225057265937867451 := by
  unfold tailWord_3304872
  simp only [CollatzResearch.WordTrace]
  refine ⟨60269292241510323023182435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80359056322013764030909913 60269292241510323023182435)
  ·
    refine ⟨90403938362265484534773653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60269292241510323023182435 90403938362265484534773653)
    ·
      refine ⟨4237684610731194587567515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 90403938362265484534773653 4237684610731194587567515)
      ·
        refine ⟨6356526916096791881351273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4237684610731194587567515 6356526916096791881351273)
        ·
          refine ⟨4767395187072593911013455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6356526916096791881351273 4767395187072593911013455)
          ·
            refine ⟨7151092780608890866520183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4767395187072593911013455 7151092780608890866520183)
            ·
              refine ⟨10726639170913336299780275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7151092780608890866520183 10726639170913336299780275)
              ·
                refine ⟨16089958756370004449670413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10726639170913336299780275 16089958756370004449670413)
                ·
                  refine ⟨6033734533638751668626405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16089958756370004449670413 6033734533638751668626405)
                  ·
                    refine ⟨1131325225057265937867451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6033734533638751668626405 1131325225057265937867451)
                    ·
                      rfl

theorem cell22_3304872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_3304872 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3304872 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3304872 prefixEnd_3304872 := by exact prefixLift 3304872
  have htrace : WordTrace (prefixWord ++ tailWord_3304872) baseStart_3304872 baseEnd_3304872 := by
    simpa [prefixWord, tailWord_3304872, baseEnd_3304872] using wordTrace_append hprefix tailTrace_3304872
  have hstable : (prefixWord ++ tailWord_3304872).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3304872).length < 2 ^ (prefixWord ++ tailWord_3304872).sum := by decide
  have hdescent : baseEnd_3304872 < baseStart_3304872 := by decide
  rcases family_descends (prefixWord ++ tailWord_3304872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3304885 : List Nat := [1, 3, 3, 2, 2, 2, 1, 2, 1, 5]
def baseStart_3304885 : Nat := 118140960795 + 3304885 * 2 ^ 59
def prefixEnd_3304885 : Nat := 4983230072969 + 3 ^ 40 * 3304885 * 2
def baseEnd_3304885 : Nat := 1131329675222938237292411

theorem tailTrace_3304885 : CollatzResearch.WordTrace tailWord_3304885 prefixEnd_3304885 1131329675222938237292411 := by
  unfold tailWord_3304885
  simp only [CollatzResearch.WordTrace]
  refine ⟨120539058631973549266588109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80359372421315699511058739 120539058631973549266588109)
  ·
    refine ⟨45202146986990080974970541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120539058631973549266588109 45202146986990080974970541)
    ·
      refine ⟨16950805120121280365613953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45202146986990080974970541 16950805120121280365613953)
      ·
        refine ⟨12713103840090960274210465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16950805120121280365613953 12713103840090960274210465)
        ·
          refine ⟨9534827880068220205657849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12713103840090960274210465 9534827880068220205657849)
          ·
            refine ⟨7151120910051165154243387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9534827880068220205657849 7151120910051165154243387)
            ·
              refine ⟨10726681365076747731365081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7151120910051165154243387 10726681365076747731365081)
              ·
                refine ⟨8045011023807560798523811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10726681365076747731365081 8045011023807560798523811)
                ·
                  refine ⟨12067516535711341197785717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8045011023807560798523811 12067516535711341197785717)
                  ·
                    refine ⟨1131329675222938237292411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12067516535711341197785717 1131329675222938237292411)
                    ·
                      rfl

theorem cell22_3304885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 2, 1, 5].length) (baseStart_3304885 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3304885 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3304885 prefixEnd_3304885 := by exact prefixLift 3304885
  have htrace : WordTrace (prefixWord ++ tailWord_3304885) baseStart_3304885 baseEnd_3304885 := by
    simpa [prefixWord, tailWord_3304885, baseEnd_3304885] using wordTrace_append hprefix tailTrace_3304885
  have hstable : (prefixWord ++ tailWord_3304885).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3304885).length < 2 ^ (prefixWord ++ tailWord_3304885).sum := by decide
  have hdescent : baseEnd_3304885 < baseStart_3304885 := by decide
  rcases family_descends (prefixWord ++ tailWord_3304885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3304964 : List Nat := [2, 3, 2, 3, 2, 1, 2, 1, 3, 3]
def baseStart_3304964 : Nat := 118140960795 + 3304964 * 2 ^ 59
def prefixEnd_3304964 : Nat := 4983230072969 + 3 ^ 40 * 3304964 * 2
def baseEnd_3304964 : Nat := 1131356718537408364567169

theorem tailTrace_3304964 : CollatzResearch.WordTrace tailWord_3304964 prefixEnd_3304964 1131356718537408364567169 := by
  unfold tailWord_3304964
  simp only [CollatzResearch.WordTrace]
  refine ⟨60270969999343672879356973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80361293332458230505809297 60270969999343672879356973)
  ·
    refine ⟨22601613749753877329758865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60270969999343672879356973 22601613749753877329758865)
    ·
      refine ⟨16951210312315407997319149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22601613749753877329758865 16951210312315407997319149)
      ·
        refine ⟨6356703867118277998994681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16951210312315407997319149 6356703867118277998994681)
        ·
          refine ⟨4767527900338708499246011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6356703867118277998994681 4767527900338708499246011)
          ·
            refine ⟨7151291850508062748869017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4767527900338708499246011 7151291850508062748869017)
            ·
              refine ⟨5363468887881047061651763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7151291850508062748869017 5363468887881047061651763)
              ·
                refine ⟨8045203331821570592477645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5363468887881047061651763 8045203331821570592477645)
                ·
                  refine ⟨3016951249433088972179117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8045203331821570592477645 3016951249433088972179117)
                  ·
                    refine ⟨1131356718537408364567169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3016951249433088972179117 1131356718537408364567169)
                    ·
                      rfl

theorem cell22_3304964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 2, 1, 3, 3].length) (baseStart_3304964 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3304964 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3304964 prefixEnd_3304964 := by exact prefixLift 3304964
  have htrace : WordTrace (prefixWord ++ tailWord_3304964) baseStart_3304964 baseEnd_3304964 := by
    simpa [prefixWord, tailWord_3304964, baseEnd_3304964] using wordTrace_append hprefix tailTrace_3304964
  have hstable : (prefixWord ++ tailWord_3304964).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3304964).length < 2 ^ (prefixWord ++ tailWord_3304964).sum := by decide
  have hdescent : baseEnd_3304964 < baseStart_3304964 := by decide
  rcases family_descends (prefixWord ++ tailWord_3304964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3305052 : List Nat := [2, 2, 4, 1, 2, 1, 1, 3, 2, 4]
def baseStart_3305052 : Nat := 118140960795 + 3305052 * 2 ^ 59
def prefixEnd_3305052 : Nat := 4983230072969 + 3 ^ 40 * 3305052 * 2
def baseEnd_3305052 : Nat := 1131386842735805468366899

theorem tailTrace_3305052 : CollatzResearch.WordTrace tailWord_3305052 prefixEnd_3305052 1131386842735805468366899 := by
  unfold tailWord_3305052
  simp only [CollatzResearch.WordTrace]
  refine ⟨60272574811184268393958705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80363433081579024525278273 60272574811184268393958705)
  ·
    refine ⟨45204431108388201295469029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60272574811184268393958705 45204431108388201295469029)
    ·
      refine ⟨8475830832822787742900443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45204431108388201295469029 8475830832822787742900443)
      ·
        refine ⟨12713746249234181614350665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8475830832822787742900443 12713746249234181614350665)
        ·
          refine ⟨9535309686925636210762999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12713746249234181614350665 9535309686925636210762999)
          ·
            refine ⟨14302964530388454316144499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9535309686925636210762999 14302964530388454316144499)
            ·
              refine ⟨21454446795582681474216749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14302964530388454316144499 21454446795582681474216749)
              ·
                refine ⟨8045417548343505552831281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21454446795582681474216749 8045417548343505552831281)
                ·
                  refine ⟨6034063161257629164623461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8045417548343505552831281 6034063161257629164623461)
                  ·
                    refine ⟨1131386842735805468366899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6034063161257629164623461 1131386842735805468366899)
                    ·
                      rfl

theorem cell22_3305052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 3, 2, 4].length) (baseStart_3305052 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3305052 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3305052 prefixEnd_3305052 := by exact prefixLift 3305052
  have htrace : WordTrace (prefixWord ++ tailWord_3305052) baseStart_3305052 baseEnd_3305052 := by
    simpa [prefixWord, tailWord_3305052, baseEnd_3305052] using wordTrace_append hprefix tailTrace_3305052
  have hstable : (prefixWord ++ tailWord_3305052).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3305052).length < 2 ^ (prefixWord ++ tailWord_3305052).sum := by decide
  have hdescent : baseEnd_3305052 < baseStart_3305052 := by decide
  rcases family_descends (prefixWord ++ tailWord_3305052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3305189 : List Nat := [1, 3, 1, 4, 1, 1, 2, 4, 2, 3]
def baseStart_3305189 : Nat := 118140960795 + 3305189 * 2 ^ 59
def prefixEnd_3305189 : Nat := 4983230072969 + 3 ^ 40 * 3305189 * 2
def baseEnd_3305189 : Nat := 1131433740635582777691479

theorem tailTrace_3305189 : CollatzResearch.WordTrace tailWord_3305189 prefixEnd_3305189 1131433740635582777691479 := by
  unfold tailWord_3305189
  simp only [CollatzResearch.WordTrace]
  refine ⟨120550146422872209185654621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80366764281914806123769747 120550146422872209185654621)
  ·
    refine ⟨45206304908577078444620483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120550146422872209185654621 45206304908577078444620483)
    ·
      refine ⟨67809457362865617666930725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45206304908577078444620483 67809457362865617666930725)
      ·
        refine ⟨12714273255537303312549511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67809457362865617666930725 12714273255537303312549511)
        ·
          refine ⟨19071409883305954968824267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12714273255537303312549511 19071409883305954968824267)
          ·
            refine ⟨28607114824958932453236401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19071409883305954968824267 28607114824958932453236401)
            ·
              refine ⟨21455336118719199339927301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28607114824958932453236401 21455336118719199339927301)
              ·
                refine ⟨4022875522259849876236369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21455336118719199339927301 4022875522259849876236369)
                ·
                  refine ⟨3017156641694887407177277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4022875522259849876236369 3017156641694887407177277)
                  ·
                    refine ⟨1131433740635582777691479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3017156641694887407177277 1131433740635582777691479)
                    ·
                      rfl

theorem cell22_3305189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 4, 2, 3].length) (baseStart_3305189 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3305189 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3305189 prefixEnd_3305189 := by exact prefixLift 3305189
  have htrace : WordTrace (prefixWord ++ tailWord_3305189) baseStart_3305189 baseEnd_3305189 := by
    simpa [prefixWord, tailWord_3305189, baseEnd_3305189] using wordTrace_append hprefix tailTrace_3305189
  have hstable : (prefixWord ++ tailWord_3305189).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3305189).length < 2 ^ (prefixWord ++ tailWord_3305189).sum := by decide
  have hdescent : baseEnd_3305189 < baseStart_3305189 := by decide
  rcases family_descends (prefixWord ++ tailWord_3305189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3305191 : List Nat := [1, 1, 5, 4, 1, 2, 1, 1, 6]
def baseStart_3305191 : Nat := 118140960795 + 3305191 * 2 ^ 59
def prefixEnd_3305191 : Nat := 4983230072969 + 3 ^ 40 * 3305191 * 2
def baseEnd_3305191 : Nat := 377144808425485146380491

theorem tailTrace_3305191 : CollatzResearch.WordTrace tailWord_3305191 prefixEnd_3305191 377144808425485146380491 := by
  unfold tailWord_3305191
  simp only [CollatzResearch.WordTrace]
  refine ⟨120550219368864963527227427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80366812912576642351484951 120550219368864963527227427)
  ·
    refine ⟨180825329053297445290841141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120550219368864963527227427 180825329053297445290841141)
    ·
      refine ⟨16952374598746635496016357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 180825329053297445290841141 16952374598746635496016357)
      ·
        refine ⟨3178570237264994155503067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16952374598746635496016357 3178570237264994155503067)
        ·
          refine ⟨4767855355897491233254601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3178570237264994155503067 4767855355897491233254601)
          ·
            refine ⟨3575891516923118424940951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4767855355897491233254601 3575891516923118424940951)
            ·
              refine ⟨5363837275384677637411427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3575891516923118424940951 5363837275384677637411427)
              ·
                refine ⟨8045755913077016456117141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5363837275384677637411427 8045755913077016456117141)
                ·
                  refine ⟨377144808425485146380491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8045755913077016456117141 377144808425485146380491)
                  ·
                    rfl

theorem cell22_3305191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 1, 1, 6].length) (baseStart_3305191 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3305191 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3305191 prefixEnd_3305191 := by exact prefixLift 3305191
  have htrace : WordTrace (prefixWord ++ tailWord_3305191) baseStart_3305191 baseEnd_3305191 := by
    simpa [prefixWord, tailWord_3305191, baseEnd_3305191] using wordTrace_append hprefix tailTrace_3305191
  have hstable : (prefixWord ++ tailWord_3305191).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3305191).length < 2 ^ (prefixWord ++ tailWord_3305191).sum := by decide
  have hdescent : baseEnd_3305191 < baseStart_3305191 := by decide
  rcases family_descends (prefixWord ++ tailWord_3305191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3305200 : List Nat := [2, 1, 1, 1, 3, 1, 2, 2, 2, 7]
def baseStart_3305200 : Nat := 118140960795 + 3305200 * 2 ^ 59
def prefixEnd_3305200 : Nat := 4983230072969 + 3 ^ 40 * 3305200 * 2
def baseEnd_3305200 : Nat := 1131437506160382415666445

theorem tailTrace_3305200 : CollatzResearch.WordTrace tailWord_3305200 prefixEnd_3305200 1131437506160382415666445 := by
  unfold tailWord_3305200
  simp only [CollatzResearch.WordTrace]
  refine ⟨60275273812916179032152527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80367031750554905376203369 60275273812916179032152527)
  ·
    refine ⟨90412910719374268548228791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60275273812916179032152527 90412910719374268548228791)
    ·
      refine ⟨135619366079061402822343187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90412910719374268548228791 135619366079061402822343187)
      ·
        refine ⟨203429049118592104233514781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135619366079061402822343187 203429049118592104233514781)
        ·
          refine ⟨76285893419472039087568043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 203429049118592104233514781 76285893419472039087568043)
          ·
            refine ⟨114428840129208058631352065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76285893419472039087568043 114428840129208058631352065)
            ·
              refine ⟨85821630096906043973514049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114428840129208058631352065 85821630096906043973514049)
              ·
                refine ⟨64366222572679532980135537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85821630096906043973514049 64366222572679532980135537)
                ·
                  refine ⟨48274666929509649735101653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64366222572679532980135537 48274666929509649735101653)
                  ·
                    refine ⟨1131437506160382415666445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48274666929509649735101653 1131437506160382415666445)
                    ·
                      rfl

theorem cell22_3305200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 2, 2, 7].length) (baseStart_3305200 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3305200 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3305200 prefixEnd_3305200 := by exact prefixLift 3305200
  have htrace : WordTrace (prefixWord ++ tailWord_3305200) baseStart_3305200 baseEnd_3305200 := by
    simpa [prefixWord, tailWord_3305200, baseEnd_3305200] using wordTrace_append hprefix tailTrace_3305200
  have hstable : (prefixWord ++ tailWord_3305200).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3305200).length < 2 ^ (prefixWord ++ tailWord_3305200).sum := by decide
  have hdescent : baseEnd_3305200 < baseStart_3305200 := by decide
  rcases family_descends (prefixWord ++ tailWord_3305200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3305202 : List Nat := [3, 2, 1, 3, 1, 1, 4, 7]
def baseStart_3305202 : Nat := 118140960795 + 3305202 * 2 ^ 59
def prefixEnd_3305202 : Nat := 4983230072969 + 3 ^ 40 * 3305202 * 2
def baseEnd_3305202 : Nat := 125715354533472786346271

theorem tailTrace_3305202 : CollatzResearch.WordTrace tailWord_3305202 prefixEnd_3305202 125715354533472786346271 := by
  unfold tailWord_3305202
  simp only [CollatzResearch.WordTrace]
  refine ⟨30137655142956278101469465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80367080381216741603918573 30137655142956278101469465)
  ·
    refine ⟨22603241357217208576102099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30137655142956278101469465 22603241357217208576102099)
    ·
      refine ⟨33904862035825812864153149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22603241357217208576102099 33904862035825812864153149)
      ·
        refine ⟨12714323263434679824057431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33904862035825812864153149 12714323263434679824057431)
        ·
          refine ⟨19071484895152019736086147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12714323263434679824057431 19071484895152019736086147)
          ·
            refine ⟨28607227342728029604129221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19071484895152019736086147 28607227342728029604129221)
            ·
              refine ⟨5363855126761505550774229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28607227342728029604129221 5363855126761505550774229)
              ·
                refine ⟨125715354533472786346271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5363855126761505550774229 125715354533472786346271)
                ·
                  rfl

theorem cell22_3305202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 4, 7].length) (baseStart_3305202 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3305202 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3305202 prefixEnd_3305202 := by exact prefixLift 3305202
  have htrace : WordTrace (prefixWord ++ tailWord_3305202) baseStart_3305202 baseEnd_3305202 := by
    simpa [prefixWord, tailWord_3305202, baseEnd_3305202] using wordTrace_append hprefix tailTrace_3305202
  have hstable : (prefixWord ++ tailWord_3305202).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3305202).length < 2 ^ (prefixWord ++ tailWord_3305202).sum := by decide
  have hdescent : baseEnd_3305202 < baseStart_3305202 := by decide
  rcases family_descends (prefixWord ++ tailWord_3305202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3305206 : List Nat := [5, 1, 1, 1, 1, 4, 1, 3, 2, 3]
def baseStart_3305206 : Nat := 118140960795 + 3305206 * 2 ^ 59
def prefixEnd_3305206 : Nat := 4983230072969 + 3 ^ 40 * 3305206 * 2
def baseEnd_3305206 : Nat := 1131439560083000400016427

theorem tailTrace_3305206 : CollatzResearch.WordTrace tailWord_3305206 prefixEnd_3305206 1131439560083000400016427 := by
  unfold tailWord_3305206
  simp only [CollatzResearch.WordTrace]
  refine ⟨7534422903988163818063967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 80367177642540414059348981 7534422903988163818063967)
  ·
    refine ⟨11301634355982245727095951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7534422903988163818063967 11301634355982245727095951)
    ·
      refine ⟨16952451533973368590643927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11301634355982245727095951 16952451533973368590643927)
      ·
        refine ⟨25428677300960052885965891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16952451533973368590643927 25428677300960052885965891)
        ·
          refine ⟨38143015951440079328948837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25428677300960052885965891 38143015951440079328948837)
          ·
            refine ⟨7151815490895014874177907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38143015951440079328948837 7151815490895014874177907)
            ·
              refine ⟨10727723236342522311266861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7151815490895014874177907 10727723236342522311266861)
              ·
                refine ⟨4022896213628445866725073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10727723236342522311266861 4022896213628445866725073)
                ·
                  refine ⟨3017172160221334400043805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4022896213628445866725073 3017172160221334400043805)
                  ·
                    refine ⟨1131439560083000400016427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3017172160221334400043805 1131439560083000400016427)
                    ·
                      rfl

theorem cell22_3305206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 1, 3, 2, 3].length) (baseStart_3305206 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3305206 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3305206 prefixEnd_3305206 := by exact prefixLift 3305206
  have htrace : WordTrace (prefixWord ++ tailWord_3305206) baseStart_3305206 baseEnd_3305206 := by
    simpa [prefixWord, tailWord_3305206, baseEnd_3305206] using wordTrace_append hprefix tailTrace_3305206
  have hstable : (prefixWord ++ tailWord_3305206).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3305206).length < 2 ^ (prefixWord ++ tailWord_3305206).sum := by decide
  have hdescent : baseEnd_3305206 < baseStart_3305206 := by decide
  rcases family_descends (prefixWord ++ tailWord_3305206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3305236 : List Nat := [2, 4, 4, 1, 1, 10]
def baseStart_3305236 : Nat := 118140960795 + 3305236 * 2 ^ 59
def prefixEnd_3305236 : Nat := 4983230072969 + 3 ^ 40 * 3305236 * 2
def baseEnd_3305236 : Nat := 13968516416001115083535

theorem tailTrace_3305236 : CollatzResearch.WordTrace tailWord_3305236 prefixEnd_3305236 13968516416001115083535 := by
  unfold tailWord_3305236
  simp only [CollatzResearch.WordTrace]
  refine ⟨60275930326850968106307781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80367907102467957475077041 60275930326850968106307781)
  ·
    refine ⟨11301736936284556519932709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60275930326850968106307781 11301736936284556519932709)
    ·
      refine ⟨2119075675553354347487383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11301736936284556519932709 2119075675553354347487383)
      ·
        refine ⟨3178613513330031521231075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2119075675553354347487383 3178613513330031521231075)
        ·
          refine ⟨4767920269995047281846613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3178613513330031521231075 4767920269995047281846613)
          ·
            refine ⟨13968516416001115083535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4767920269995047281846613 13968516416001115083535)
            ·
              rfl

theorem cell22_3305236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 10].length) (baseStart_3305236 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3305236 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3305236 prefixEnd_3305236 := by exact prefixLift 3305236
  have htrace : WordTrace (prefixWord ++ tailWord_3305236) baseStart_3305236 baseEnd_3305236 := by
    simpa [prefixWord, tailWord_3305236, baseEnd_3305236] using wordTrace_append hprefix tailTrace_3305236
  have hstable : (prefixWord ++ tailWord_3305236).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3305236).length < 2 ^ (prefixWord ++ tailWord_3305236).sum := by decide
  have hdescent : baseEnd_3305236 < baseStart_3305236 := by decide
  rcases family_descends (prefixWord ++ tailWord_3305236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3305324 : List Nat := [2, 2, 1, 1, 4, 2, 3, 1, 1, 5]
def baseStart_3305324 : Nat := 118140960795 + 3305324 * 2 ^ 59
def prefixEnd_3305324 : Nat := 4983230072969 + 3 ^ 40 * 3305324 * 2
def baseEnd_3305324 : Nat := 1131479953894487425566065

theorem tailTrace_3305324 : CollatzResearch.WordTrace tailWord_3305324 prefixEnd_3305324 1131479953894487425566065 := by
  unfold tailWord_3305324
  simp only [CollatzResearch.WordTrace]
  refine ⟨60277535138691563620909513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80370046851588751494546017 60277535138691563620909513)
  ·
    refine ⟨45208151354018672715682135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60277535138691563620909513 45208151354018672715682135)
    ·
      refine ⟨67812227031028009073523203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45208151354018672715682135 67812227031028009073523203)
      ·
        refine ⟨101718340546542013610284805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67812227031028009073523203 101718340546542013610284805)
        ·
          refine ⟨19072188852476627551928401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 101718340546542013610284805 19072188852476627551928401)
          ·
            refine ⟨14304141639357470663946301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19072188852476627551928401 14304141639357470663946301)
            ·
              refine ⟨5364053114759051498979863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14304141639357470663946301 5364053114759051498979863)
              ·
                refine ⟨8046079672138577248469795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5364053114759051498979863 8046079672138577248469795)
                ·
                  refine ⟨12069119508207865872704693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8046079672138577248469795 12069119508207865872704693)
                  ·
                    refine ⟨1131479953894487425566065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12069119508207865872704693 1131479953894487425566065)
                    ·
                      rfl

theorem cell22_3305324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 5].length) (baseStart_3305324 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3305324 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3305324 prefixEnd_3305324 := by exact prefixLift 3305324
  have htrace : WordTrace (prefixWord ++ tailWord_3305324) baseStart_3305324 baseEnd_3305324 := by
    simpa [prefixWord, tailWord_3305324, baseEnd_3305324] using wordTrace_append hprefix tailTrace_3305324
  have hstable : (prefixWord ++ tailWord_3305324).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3305324).length < 2 ^ (prefixWord ++ tailWord_3305324).sum := by decide
  have hdescent : baseEnd_3305324 < baseStart_3305324 := by decide
  rcases family_descends (prefixWord ++ tailWord_3305324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3305337 : List Nat := [1, 2, 1, 3, 2, 2, 3, 8]
def baseStart_3305337 : Nat := 118140960795 + 3305337 * 2 ^ 59
def prefixEnd_3305337 : Nat := 4983230072969 + 3 ^ 40 * 3305337 * 2
def baseEnd_3305337 : Nat := 125720489340017747221225

theorem tailTrace_3305337 : CollatzResearch.WordTrace tailWord_3305337 prefixEnd_3305337 125720489340017747221225 := by
  unfold tailWord_3305337
  simp only [CollatzResearch.WordTrace]
  refine ⟨120555544426336030462042265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80370362950890686974694843 120555544426336030462042265)
  ·
    refine ⟨90416658319752022846531699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120555544426336030462042265 90416658319752022846531699)
    ·
      refine ⟨135624987479628034269797549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90416658319752022846531699 135624987479628034269797549)
      ·
        refine ⟨50859370304860512851174081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135624987479628034269797549 50859370304860512851174081)
        ·
          refine ⟨38144527728645384638380561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50859370304860512851174081 38144527728645384638380561)
          ·
            refine ⟨28608395796484038478785421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38144527728645384638380561 28608395796484038478785421)
            ·
              refine ⟨10728148423681514429544533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28608395796484038478785421 10728148423681514429544533)
              ·
                refine ⟨125720489340017747221225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10728148423681514429544533 125720489340017747221225)
                ·
                  rfl

theorem cell22_3305337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3, 8].length) (baseStart_3305337 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3305337 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3305337 prefixEnd_3305337 := by exact prefixLift 3305337
  have htrace : WordTrace (prefixWord ++ tailWord_3305337) baseStart_3305337 baseEnd_3305337 := by
    simpa [prefixWord, tailWord_3305337, baseEnd_3305337] using wordTrace_append hprefix tailTrace_3305337
  have hstable : (prefixWord ++ tailWord_3305337).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3305337).length < 2 ^ (prefixWord ++ tailWord_3305337).sum := by decide
  have hdescent : baseEnd_3305337 < baseStart_3305337 := by decide
  rcases family_descends (prefixWord ++ tailWord_3305337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3305375 : List Nat := [1, 1, 2, 5, 3, 2, 2, 1, 2, 3]
def baseStart_3305375 : Nat := 118140960795 + 3305375 * 2 ^ 59
def prefixEnd_3305375 : Nat := 4983230072969 + 3 ^ 40 * 3305375 * 2
def baseEnd_3305375 : Nat := 1131497412236740292540909

theorem tailTrace_3305375 : CollatzResearch.WordTrace tailWord_3305375 prefixEnd_3305375 1131497412236740292540909 := by
  unfold tailWord_3305375
  simp only [CollatzResearch.WordTrace]
  refine ⟨120556930400198362951925579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80371286933465575301283719 120556930400198362951925579)
  ·
    refine ⟨180835395600297544427888369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120556930400198362951925579 180835395600297544427888369)
    ·
      refine ⟨135626546700223158320916277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180835395600297544427888369 135626546700223158320916277)
      ·
        refine ⟨12714988753145921092585901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 135626546700223158320916277 12714988753145921092585901)
        ·
          refine ⟨4768120782429720409719713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12714988753145921092585901 4768120782429720409719713)
          ·
            refine ⟨3576090586822290307289785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4768120782429720409719713 3576090586822290307289785)
            ·
              refine ⟨2682067940116717730467339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3576090586822290307289785 2682067940116717730467339)
              ·
                refine ⟨4023101910175076595701009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2682067940116717730467339 4023101910175076595701009)
                ·
                  refine ⟨3017326432631307446775757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4023101910175076595701009 3017326432631307446775757)
                  ·
                    refine ⟨1131497412236740292540909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3017326432631307446775757 1131497412236740292540909)
                    ·
                      rfl

theorem cell22_3305375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 2, 1, 2, 3].length) (baseStart_3305375 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3305375 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3305375 prefixEnd_3305375 := by exact prefixLift 3305375
  have htrace : WordTrace (prefixWord ++ tailWord_3305375) baseStart_3305375 baseEnd_3305375 := by
    simpa [prefixWord, tailWord_3305375, baseEnd_3305375] using wordTrace_append hprefix tailTrace_3305375
  have hstable : (prefixWord ++ tailWord_3305375).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3305375).length < 2 ^ (prefixWord ++ tailWord_3305375).sum := by decide
  have hdescent : baseEnd_3305375 < baseStart_3305375 := by decide
  rcases family_descends (prefixWord ++ tailWord_3305375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3305416 : List Nat := [2, 1, 3, 1, 4, 2, 2, 2, 5]
def baseStart_3305416 : Nat := 118140960795 + 3305416 * 2 ^ 59
def prefixEnd_3305416 : Nat := 4983230072969 + 3 ^ 40 * 3305416 * 2
def baseEnd_3305416 : Nat := 377170482458209950755261

theorem tailTrace_3305416 : CollatzResearch.WordTrace tailWord_3305416 prefixEnd_3305416 377170482458209950755261 := by
  unfold tailWord_3305416
  simp only [CollatzResearch.WordTrace]
  refine ⟨60279212896524913477084051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80372283862033217969445401 60279212896524913477084051)
  ·
    refine ⟨90418819344787370215626077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60279212896524913477084051 90418819344787370215626077)
    ·
      refine ⟨33907057254295263830859779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90418819344787370215626077 33907057254295263830859779)
      ·
        refine ⟨50860585881442895746289669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33907057254295263830859779 50860585881442895746289669)
        ·
          refine ⟨9536359852770542952429313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50860585881442895746289669 9536359852770542952429313)
          ·
            refine ⟨7152269889577907214321985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9536359852770542952429313 7152269889577907214321985)
            ·
              refine ⟨5364202417183430410741489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7152269889577907214321985 5364202417183430410741489)
              ·
                refine ⟨4023151812887572808056117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5364202417183430410741489 4023151812887572808056117)
                ·
                  refine ⟨377170482458209950755261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4023151812887572808056117 377170482458209950755261)
                  ·
                    rfl

theorem cell22_3305416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 2, 2, 5].length) (baseStart_3305416 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3305416 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3305416 prefixEnd_3305416 := by exact prefixLift 3305416
  have htrace : WordTrace (prefixWord ++ tailWord_3305416) baseStart_3305416 baseEnd_3305416 := by
    simpa [prefixWord, tailWord_3305416, baseEnd_3305416] using wordTrace_append hprefix tailTrace_3305416
  have hstable : (prefixWord ++ tailWord_3305416).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3305416).length < 2 ^ (prefixWord ++ tailWord_3305416).sum := by decide
  have hdescent : baseEnd_3305416 < baseStart_3305416 := by decide
  rcases family_descends (prefixWord ++ tailWord_3305416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3305420 : List Nat := [2, 2, 1, 4, 1, 2, 4, 2, 1, 3]
def baseStart_3305420 : Nat := 118140960795 + 3305420 * 2 ^ 59
def prefixEnd_3305420 : Nat := 4983230072969 + 3 ^ 40 * 3305420 * 2
def baseEnd_3305420 : Nat := 1131512816656375175165771

theorem tailTrace_3305420 : CollatzResearch.WordTrace tailWord_3305420 prefixEnd_3305420 1131512816656375175165771 := by
  unfold tailWord_3305420
  simp only [CollatzResearch.WordTrace]
  refine ⟨60279285842517667818656857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80372381123356890424875809 60279285842517667818656857)
  ·
    refine ⟨45209464381888250863992643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60279285842517667818656857 45209464381888250863992643)
    ·
      refine ⟨67814196572832376295988965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45209464381888250863992643 67814196572832376295988965)
      ·
        refine ⟨12715161857406070555497931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67814196572832376295988965 12715161857406070555497931)
        ·
          refine ⟨19072742786109105833246897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12715161857406070555497931 19072742786109105833246897)
          ·
            refine ⟨14304557089581829374935173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19072742786109105833246897 14304557089581829374935173)
            ·
              refine ⟨2682104454296593007800345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14304557089581829374935173 2682104454296593007800345)
              ·
                refine ⟨2011578340722444755850259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2682104454296593007800345 2011578340722444755850259)
                ·
                  refine ⟨3017367511083667133775389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2011578340722444755850259 3017367511083667133775389)
                  ·
                    refine ⟨1131512816656375175165771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3017367511083667133775389 1131512816656375175165771)
                    ·
                      rfl

theorem cell22_3305420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 4, 2, 1, 3].length) (baseStart_3305420 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3305420 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3305420 prefixEnd_3305420 := by exact prefixLift 3305420
  have htrace : WordTrace (prefixWord ++ tailWord_3305420) baseStart_3305420 baseEnd_3305420 := by
    simpa [prefixWord, tailWord_3305420, baseEnd_3305420] using wordTrace_append hprefix tailTrace_3305420
  have hstable : (prefixWord ++ tailWord_3305420).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3305420).length < 2 ^ (prefixWord ++ tailWord_3305420).sum := by decide
  have hdescent : baseEnd_3305420 < baseStart_3305420 := by decide
  rcases family_descends (prefixWord ++ tailWord_3305420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3305444 : List Nat := [2, 3, 1, 1, 1, 1, 5, 2, 6]
def baseStart_3305444 : Nat := 118140960795 + 3305444 * 2 ^ 59
def prefixEnd_3305444 : Nat := 4983230072969 + 3 ^ 40 * 3305444 * 2
def baseEnd_3305444 : Nat := 377173677448949037521899

theorem tailTrace_3305444 : CollatzResearch.WordTrace tailWord_3305444 prefixEnd_3305444 377173677448949037521899 := by
  unfold tailWord_3305444
  simp only [CollatzResearch.WordTrace]
  refine ⟨60279723518474193868093693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80372964691298925157458257 60279723518474193868093693)
  ·
    refine ⟨22604896319427822700535135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60279723518474193868093693 22604896319427822700535135)
    ·
      refine ⟨33907344479141734050802703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22604896319427822700535135 33907344479141734050802703)
      ·
        refine ⟨50861016718712601076204055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33907344479141734050802703 50861016718712601076204055)
        ·
          refine ⟨76291525078068901614306083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50861016718712601076204055 76291525078068901614306083)
          ·
            refine ⟨114437287617103352421459125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76291525078068901614306083 114437287617103352421459125)
            ·
              refine ⟨10728495714103439289511793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 114437287617103352421459125 10728495714103439289511793)
              ·
                refine ⟨8046371785577579467133845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10728495714103439289511793 8046371785577579467133845)
                ·
                  refine ⟨377173677448949037521899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8046371785577579467133845 377173677448949037521899)
                  ·
                    rfl

theorem cell22_3305444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5, 2, 6].length) (baseStart_3305444 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3305444 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3305444 prefixEnd_3305444 := by exact prefixLift 3305444
  have htrace : WordTrace (prefixWord ++ tailWord_3305444) baseStart_3305444 baseEnd_3305444 := by
    simpa [prefixWord, tailWord_3305444, baseEnd_3305444] using wordTrace_append hprefix tailTrace_3305444
  have hstable : (prefixWord ++ tailWord_3305444).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3305444).length < 2 ^ (prefixWord ++ tailWord_3305444).sum := by decide
  have hdescent : baseEnd_3305444 < baseStart_3305444 := by decide
  rcases family_descends (prefixWord ++ tailWord_3305444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3305493 : List Nat := [1, 3, 2, 1, 5, 2, 1, 1, 1, 5]
def baseStart_3305493 : Nat := 118140960795 + 3305493 * 2 ^ 59
def prefixEnd_3305493 : Nat := 4983230072969 + 3 ^ 40 * 3305493 * 2
def baseEnd_3305493 : Nat := 1131537806048227318090547

theorem tailTrace_3305493 : CollatzResearch.WordTrace tailWord_3305493 prefixEnd_3305493 1131537806048227318090547 := by
  unfold tailWord_3305493
  simp only [CollatzResearch.WordTrace]
  refine ⟨120561234213770869104721133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80374156142513912736480755 120561234213770869104721133)
  ·
    refine ⟨45210462830164075914270425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120561234213770869104721133 45210462830164075914270425)
    ·
      refine ⟨33907847122623056935702819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45210462830164075914270425 33907847122623056935702819)
      ·
        refine ⟨50861770683934585403554229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33907847122623056935702819 50861770683934585403554229)
        ·
          refine ⟨4768291001618867381583209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 50861770683934585403554229 4768291001618867381583209)
          ·
            refine ⟨3576218251214150536187407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4768291001618867381583209 3576218251214150536187407)
            ·
              refine ⟨5364327376821225804281111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3576218251214150536187407 5364327376821225804281111)
              ·
                refine ⟨8046491065231838706421667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5364327376821225804281111 8046491065231838706421667)
                ·
                  refine ⟨12069736597847758059632501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8046491065231838706421667 12069736597847758059632501)
                  ·
                    refine ⟨1131537806048227318090547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12069736597847758059632501 1131537806048227318090547)
                    ·
                      rfl

theorem cell22_3305493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 1, 1, 1, 5].length) (baseStart_3305493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3305493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3305493 prefixEnd_3305493 := by exact prefixLift 3305493
  have htrace : WordTrace (prefixWord ++ tailWord_3305493) baseStart_3305493 baseEnd_3305493 := by
    simpa [prefixWord, tailWord_3305493, baseEnd_3305493] using wordTrace_append hprefix tailTrace_3305493
  have hstable : (prefixWord ++ tailWord_3305493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3305493).length < 2 ^ (prefixWord ++ tailWord_3305493).sum := by decide
  have hdescent : baseEnd_3305493 < baseStart_3305493 := by decide
  rcases family_descends (prefixWord ++ tailWord_3305493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3305512 : List Nat := [2, 1, 5, 3, 1, 2, 1, 3, 4]
def baseStart_3305512 : Nat := 118140960795 + 3305512 * 2 ^ 59
def prefixEnd_3305512 : Nat := 4983230072969 + 3 ^ 40 * 3305512 * 2
def baseEnd_3305512 : Nat := 377181436712172533955163

theorem tailTrace_3305512 : CollatzResearch.WordTrace tailWord_3305512 prefixEnd_3305512 377181436712172533955163 := by
  unfold tailWord_3305512
  simp only [CollatzResearch.WordTrace]
  refine ⟨60280963600351017674831395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80374618133801356899775193 60280963600351017674831395)
  ·
    refine ⟨90421445400526526512247093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60280963600351017674831395 90421445400526526512247093)
    ·
      refine ⟨8477010506299361860523165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 90421445400526526512247093 8477010506299361860523165)
      ·
        refine ⟨3178878939862260697696187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8477010506299361860523165 3178878939862260697696187)
        ·
          refine ⟨4768318409793391046544281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3178878939862260697696187 4768318409793391046544281)
          ·
            refine ⟨3576238807345043284908211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4768318409793391046544281 3576238807345043284908211)
            ·
              refine ⟨5364358211017564927362317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3576238807345043284908211 5364358211017564927362317)
              ·
                refine ⟨2011634329131586847760869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5364358211017564927362317 2011634329131586847760869)
                ·
                  refine ⟨377181436712172533955163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2011634329131586847760869 377181436712172533955163)
                  ·
                    rfl

theorem cell22_3305512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 1, 3, 4].length) (baseStart_3305512 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3305512 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3305512 prefixEnd_3305512 := by exact prefixLift 3305512
  have htrace : WordTrace (prefixWord ++ tailWord_3305512) baseStart_3305512 baseEnd_3305512 := by
    simpa [prefixWord, tailWord_3305512, baseEnd_3305512] using wordTrace_append hprefix tailTrace_3305512
  have hstable : (prefixWord ++ tailWord_3305512).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3305512).length < 2 ^ (prefixWord ++ tailWord_3305512).sum := by decide
  have hdescent : baseEnd_3305512 < baseStart_3305512 := by decide
  rcases family_descends (prefixWord ++ tailWord_3305512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3305611 : List Nat := [1, 1, 1, 1, 4, 1, 1, 1, 8, 3]
def baseStart_3305611 : Nat := 118140960795 + 3305611 * 2 ^ 59
def prefixEnd_3305611 : Nat := 4983230072969 + 3 ^ 40 * 3305611 * 2
def baseEnd_3305611 : Nat := 1131578199859714343640185

theorem tailTrace_3305611 : CollatzResearch.WordTrace tailWord_3305611 prefixEnd_3305611 1131578199859714343640185 := by
  unfold tailWord_3305611
  simp only [CollatzResearch.WordTrace]
  refine ⟨120565538027343375257516687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80377025351562250171677791 120565538027343375257516687)
  ·
    refine ⟨180848307041015062886275031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120565538027343375257516687 180848307041015062886275031)
    ·
      refine ⟨271272460561522594329412547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180848307041015062886275031 271272460561522594329412547)
      ·
        refine ⟨406908690842283891494118821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 271272460561522594329412547 406908690842283891494118821)
        ·
          refine ⟨76295379532928229655147279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 406908690842283891494118821 76295379532928229655147279)
          ·
            refine ⟨114443069299392344482720919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76295379532928229655147279 114443069299392344482720919)
            ·
              refine ⟨171664603949088516724081379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114443069299392344482720919 171664603949088516724081379)
              ·
                refine ⟨257496905923632775086122069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 171664603949088516724081379 257496905923632775086122069)
                ·
                  refine ⟨3017541866292571583040493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 257496905923632775086122069 3017541866292571583040493)
                  ·
                    refine ⟨1131578199859714343640185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3017541866292571583040493 1131578199859714343640185)
                    ·
                      rfl

theorem cell22_3305611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 8, 3].length) (baseStart_3305611 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3305611 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3305611 prefixEnd_3305611 := by exact prefixLift 3305611
  have htrace : WordTrace (prefixWord ++ tailWord_3305611) baseStart_3305611 baseEnd_3305611 := by
    simpa [prefixWord, tailWord_3305611, baseEnd_3305611] using wordTrace_append hprefix tailTrace_3305611
  have hstable : (prefixWord ++ tailWord_3305611).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3305611).length < 2 ^ (prefixWord ++ tailWord_3305611).sum := by decide
  have hdescent : baseEnd_3305611 < baseStart_3305611 := by decide
  rcases family_descends (prefixWord ++ tailWord_3305611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3305628 : List Nat := [2, 2, 3, 2, 1, 1, 2, 2, 4, 3]
def baseStart_3305628 : Nat := 118140960795 + 3305628 * 2 ^ 59
def prefixEnd_3305628 : Nat := 4983230072969 + 3 ^ 40 * 3305628 * 2
def baseEnd_3305628 : Nat := 1131584019307131965965133

theorem tailTrace_3305628 : CollatzResearch.WordTrace tailWord_3305628 prefixEnd_3305628 1131584019307131965965133 := by
  unfold tailWord_3305628
  simp only [CollatzResearch.WordTrace]
  refine ⟨60283079034140893580442769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80377438712187858107257025 60283079034140893580442769)
  ·
    refine ⟨45212309275605670185332077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60283079034140893580442769 45212309275605670185332077)
    ·
      refine ⟨16954615978352126319499529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45212309275605670185332077 16954615978352126319499529)
      ·
        refine ⟨12715961983764094739624647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16954615978352126319499529 12715961983764094739624647)
        ·
          refine ⟨19073942975646142109436971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12715961983764094739624647 19073942975646142109436971)
          ·
            refine ⟨28610914463469213164155457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19073942975646142109436971 28610914463469213164155457)
            ·
              refine ⟨21458185847601909873116593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28610914463469213164155457 21458185847601909873116593)
              ·
                refine ⟨16093639385701432404837445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21458185847601909873116593 16093639385701432404837445)
                ·
                  refine ⟨3017557384819018575907021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16093639385701432404837445 3017557384819018575907021)
                  ·
                    refine ⟨1131584019307131965965133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3017557384819018575907021 1131584019307131965965133)
                    ·
                      rfl

theorem cell22_3305628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 2, 4, 3].length) (baseStart_3305628 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3305628 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3305628 prefixEnd_3305628 := by exact prefixLift 3305628
  have htrace : WordTrace (prefixWord ++ tailWord_3305628) baseStart_3305628 baseEnd_3305628 := by
    simpa [prefixWord, tailWord_3305628, baseEnd_3305628] using wordTrace_append hprefix tailTrace_3305628
  have hstable : (prefixWord ++ tailWord_3305628).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3305628).length < 2 ^ (prefixWord ++ tailWord_3305628).sum := by decide
  have hdescent : baseEnd_3305628 < baseStart_3305628 := by decide
  rcases family_descends (prefixWord ++ tailWord_3305628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3305645 : List Nat := [1, 5, 2, 1, 2, 2, 1, 1, 4, 3]
def baseStart_3305645 : Nat := 118140960795 + 3305645 * 2 ^ 59
def prefixEnd_3305645 : Nat := 4983230072969 + 3 ^ 40 * 3305645 * 2
def baseEnd_3305645 : Nat := 1131589838754549588290081

theorem tailTrace_3305645 : CollatzResearch.WordTrace tailWord_3305645 prefixEnd_3305645 1131589838754549588290081 := by
  unfold tailWord_3305645
  simp only [CollatzResearch.WordTrace]
  refine ⟨120566778109220199064254389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80377852072813466042836259 120566778109220199064254389)
  ·
    refine ⟨11303135447739393662273849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 120566778109220199064254389 11303135447739393662273849)
    ·
      refine ⟨8477351585804545246705387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11303135447739393662273849 8477351585804545246705387)
      ·
        refine ⟨12716027378706817870058081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8477351585804545246705387 12716027378706817870058081)
        ·
          refine ⟨9537020534030113402543561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12716027378706817870058081 9537020534030113402543561)
          ·
            refine ⟨7152765400522585051907671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9537020534030113402543561 7152765400522585051907671)
            ·
              refine ⟨10729148100783877577861507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7152765400522585051907671 10729148100783877577861507)
              ·
                refine ⟨16093722151175816366792261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10729148100783877577861507 16093722151175816366792261)
                ·
                  refine ⟨3017572903345465568773549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16093722151175816366792261 3017572903345465568773549)
                  ·
                    refine ⟨1131589838754549588290081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3017572903345465568773549 1131589838754549588290081)
                    ·
                      rfl

theorem cell22_3305645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 1, 1, 4, 3].length) (baseStart_3305645 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3305645 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3305645 prefixEnd_3305645 := by exact prefixLift 3305645
  have htrace : WordTrace (prefixWord ++ tailWord_3305645) baseStart_3305645 baseEnd_3305645 := by
    simpa [prefixWord, tailWord_3305645, baseEnd_3305645] using wordTrace_append hprefix tailTrace_3305645
  have hstable : (prefixWord ++ tailWord_3305645).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3305645).length < 2 ^ (prefixWord ++ tailWord_3305645).sum := by decide
  have hdescent : baseEnd_3305645 < baseStart_3305645 := by decide
  rcases family_descends (prefixWord ++ tailWord_3305645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3305662 : List Nat := [4, 2, 1, 1, 5, 1, 1, 1, 1, 5]
def baseStart_3305662 : Nat := 118140960795 + 3305662 * 2 ^ 59
def prefixEnd_3305662 : Nat := 4983230072969 + 3 ^ 40 * 3305662 * 2
def baseEnd_3305662 : Nat := 1131595658201967210615029

theorem tailTrace_3305662 : CollatzResearch.WordTrace tailWord_3305662 prefixEnd_3305662 1131595658201967210615029 := by
  unfold tailWord_3305662
  simp only [CollatzResearch.WordTrace]
  refine ⟨15070924768769826370952905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80378265433439073978415493 15070924768769826370952905)
  ·
    refine ⟨11303193576577369778214679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15070924768769826370952905 11303193576577369778214679)
    ·
      refine ⟨16954790364866054667322019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11303193576577369778214679 16954790364866054667322019)
      ·
        refine ⟨25432185547299082000983029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16954790364866054667322019 25432185547299082000983029)
        ·
          refine ⟨2384267395059288937592159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 25432185547299082000983029 2384267395059288937592159)
          ·
            refine ⟨3576401092588933406388239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2384267395059288937592159 3576401092588933406388239)
            ·
              refine ⟨5364601638883400109582359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3576401092588933406388239 5364601638883400109582359)
              ·
                refine ⟨8046902458325100164373539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5364601638883400109582359 8046902458325100164373539)
                ·
                  refine ⟨12070353687487650246560309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8046902458325100164373539 12070353687487650246560309)
                  ·
                    refine ⟨1131595658201967210615029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12070353687487650246560309 1131595658201967210615029)
                    ·
                      rfl

theorem cell22_3305662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 1, 1, 1, 5].length) (baseStart_3305662 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3305662 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3305662 prefixEnd_3305662 := by exact prefixLift 3305662
  have htrace : WordTrace (prefixWord ++ tailWord_3305662) baseStart_3305662 baseEnd_3305662 := by
    simpa [prefixWord, tailWord_3305662, baseEnd_3305662] using wordTrace_append hprefix tailTrace_3305662
  have hstable : (prefixWord ++ tailWord_3305662).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3305662).length < 2 ^ (prefixWord ++ tailWord_3305662).sum := by decide
  have hdescent : baseEnd_3305662 < baseStart_3305662 := by decide
  rcases family_descends (prefixWord ++ tailWord_3305662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3305692 : List Nat := [2, 2, 5, 2, 2, 1, 8]
def baseStart_3305692 : Nat := 118140960795 + 3305692 * 2 ^ 59
def prefixEnd_3305692 : Nat := 4983230072969 + 3 ^ 40 * 3305692 * 2
def baseEnd_3305692 : Nat := 41911330659816930828331

theorem tailTrace_3305692 : CollatzResearch.WordTrace tailWord_3305692 prefixEnd_3305692 41911330659816930828331 := by
  unfold tailWord_3305692
  simp only [CollatzResearch.WordTrace]
  refine ⟨60284246170024963045607665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80378994893366617394143553 60284246170024963045607665)
  ·
    refine ⟨45213184627518722284205749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60284246170024963045607665 45213184627518722284205749)
    ·
      refine ⟨4238736058829880214144289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 45213184627518722284205749 4238736058829880214144289)
      ·
        refine ⟨3179052044122410160608217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4238736058829880214144289 3179052044122410160608217)
        ·
          refine ⟨2384289033091807620456163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3179052044122410160608217 2384289033091807620456163)
          ·
            refine ⟨3576433549637711430684245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2384289033091807620456163 3576433549637711430684245)
            ·
              refine ⟨41911330659816930828331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3576433549637711430684245 41911330659816930828331)
              ·
                rfl

theorem cell22_3305692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 8].length) (baseStart_3305692 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3305692 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3305692 prefixEnd_3305692 := by exact prefixLift 3305692
  have htrace : WordTrace (prefixWord ++ tailWord_3305692) baseStart_3305692 baseEnd_3305692 := by
    simpa [prefixWord, tailWord_3305692, baseEnd_3305692] using wordTrace_append hprefix tailTrace_3305692
  have hstable : (prefixWord ++ tailWord_3305692).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3305692).length < 2 ^ (prefixWord ++ tailWord_3305692).sum := by decide
  have hdescent : baseEnd_3305692 < baseStart_3305692 := by decide
  rcases family_descends (prefixWord ++ tailWord_3305692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3305703 : List Nat := [1, 1, 5, 3, 1, 1, 2, 1, 7]
def baseStart_3305703 : Nat := 118140960795 + 3305703 * 2 ^ 59
def prefixEnd_3305703 : Nat := 4983230072969 + 3 ^ 40 * 3305703 * 2
def baseEnd_3305703 : Nat := 377203231113285590113301

theorem tailTrace_3305703 : CollatzResearch.WordTrace tailWord_3305703 prefixEnd_3305703 377203231113285590113301 := by
  unfold tailWord_3305703
  simp only [CollatzResearch.WordTrace]
  refine ⟨120568893543010074969865763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80379262362006716646577175 120568893543010074969865763)
  ·
    refine ⟨180853340314515112454798645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120568893543010074969865763 180853340314515112454798645)
    ·
      refine ⟨16955000654485791792637373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 180853340314515112454798645 16955000654485791792637373)
      ·
        refine ⟨6358125245432171922239015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16955000654485791792637373 6358125245432171922239015)
        ·
          refine ⟨9537187868148257883358523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6358125245432171922239015 9537187868148257883358523)
          ·
            refine ⟨14305781802222386825037785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9537187868148257883358523 14305781802222386825037785)
            ·
              refine ⟨10729336351666790118778339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14305781802222386825037785 10729336351666790118778339)
              ·
                refine ⟨16094004527500185178167509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10729336351666790118778339 16094004527500185178167509)
                ·
                  refine ⟨377203231113285590113301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16094004527500185178167509 377203231113285590113301)
                  ·
                    rfl

theorem cell22_3305703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 2, 1, 7].length) (baseStart_3305703 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3305703 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3305703 prefixEnd_3305703 := by exact prefixLift 3305703
  have htrace : WordTrace (prefixWord ++ tailWord_3305703) baseStart_3305703 baseEnd_3305703 := by
    simpa [prefixWord, tailWord_3305703, baseEnd_3305703] using wordTrace_append hprefix tailTrace_3305703
  have hstable : (prefixWord ++ tailWord_3305703).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3305703).length < 2 ^ (prefixWord ++ tailWord_3305703).sum := by decide
  have hdescent : baseEnd_3305703 < baseStart_3305703 := by decide
  rcases family_descends (prefixWord ++ tailWord_3305703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3305707 : List Nat := [1, 1, 1, 1, 2, 5, 5, 2, 1, 3]
def baseStart_3305707 : Nat := 118140960795 + 3305707 * 2 ^ 59
def prefixEnd_3305707 : Nat := 4983230072969 + 3 ^ 40 * 3305707 * 2
def baseEnd_3305707 : Nat := 1131611062621602093239891

theorem tailTrace_3305707 : CollatzResearch.WordTrace tailWord_3305707 prefixEnd_3305707 1131611062621602093239891 := by
  unfold tailWord_3305707
  simp only [CollatzResearch.WordTrace]
  refine ⟨120569039434995583653011375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80379359623330389102007583 120569039434995583653011375)
  ·
    refine ⟨180853559152493375479517063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120569039434995583653011375 180853559152493375479517063)
    ·
      refine ⟨271280338728740063219275595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180853559152493375479517063 271280338728740063219275595)
      ·
        refine ⟨406920508093110094828913393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 271280338728740063219275595 406920508093110094828913393)
        ·
          refine ⟨305190381069832571121685045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 406920508093110094828913393 305190381069832571121685045)
          ·
            refine ⟨28611598225296803542657973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 305190381069832571121685045 28611598225296803542657973)
            ·
              refine ⟨2682337333621575332124185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28611598225296803542657973 2682337333621575332124185)
              ·
                refine ⟨2011753000216181499093139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2682337333621575332124185 2011753000216181499093139)
                ·
                  refine ⟨3017629500324272248639709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2011753000216181499093139 3017629500324272248639709)
                  ·
                    refine ⟨1131611062621602093239891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3017629500324272248639709 1131611062621602093239891)
                    ·
                      rfl

theorem cell22_3305707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 5, 2, 1, 3].length) (baseStart_3305707 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3305707 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3305707 prefixEnd_3305707 := by exact prefixLift 3305707
  have htrace : WordTrace (prefixWord ++ tailWord_3305707) baseStart_3305707 baseEnd_3305707 := by
    simpa [prefixWord, tailWord_3305707, baseEnd_3305707] using wordTrace_append hprefix tailTrace_3305707
  have hstable : (prefixWord ++ tailWord_3305707).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3305707).length < 2 ^ (prefixWord ++ tailWord_3305707).sum := by decide
  have hdescent : baseEnd_3305707 < baseStart_3305707 := by decide
  rcases family_descends (prefixWord ++ tailWord_3305707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3305718 : List Nat := [5, 1, 1, 1, 1, 1, 2, 3, 2, 5]
def baseStart_3305718 : Nat := 118140960795 + 3305718 * 2 ^ 59
def prefixEnd_3305718 : Nat := 4983230072969 + 3 ^ 40 * 3305718 * 2
def baseEnd_3305718 : Nat := 1131614828146401731214857

theorem tailTrace_3305718 : CollatzResearch.WordTrace tailWord_3305718 prefixEnd_3305718 1131614828146401731214857 := by
  unfold tailWord_3305718
  simp only [CollatzResearch.WordTrace]
  refine ⟨7535590039872233283228863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 80379627091970488354441205 7535590039872233283228863)
  ·
    refine ⟨11303385059808349924843295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7535590039872233283228863 11303385059808349924843295)
    ·
      refine ⟨16955077589712524887264943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11303385059808349924843295 16955077589712524887264943)
      ·
        refine ⟨25432616384568787330897415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16955077589712524887264943 25432616384568787330897415)
        ·
          refine ⟨38148924576853180996346123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25432616384568787330897415 38148924576853180996346123)
          ·
            refine ⟨57223386865279771494519185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38148924576853180996346123 57223386865279771494519185)
            ·
              refine ⟨42917540148959828620889389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57223386865279771494519185 42917540148959828620889389)
              ·
                refine ⟨16094077555859935732833521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42917540148959828620889389 16094077555859935732833521)
                ·
                  refine ⟨12070558166894951799625141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16094077555859935732833521 12070558166894951799625141)
                  ·
                    refine ⟨1131614828146401731214857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12070558166894951799625141 1131614828146401731214857)
                    ·
                      rfl

theorem cell22_3305718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 3, 2, 5].length) (baseStart_3305718 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3305718 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3305718 prefixEnd_3305718 := by exact prefixLift 3305718
  have htrace : WordTrace (prefixWord ++ tailWord_3305718) baseStart_3305718 baseEnd_3305718 := by
    simpa [prefixWord, tailWord_3305718, baseEnd_3305718] using wordTrace_append hprefix tailTrace_3305718
  have hstable : (prefixWord ++ tailWord_3305718).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3305718).length < 2 ^ (prefixWord ++ tailWord_3305718).sum := by decide
  have hdescent : baseEnd_3305718 < baseStart_3305718 := by decide
  rcases family_descends (prefixWord ++ tailWord_3305718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3305731 : List Nat := [1, 1, 1, 3, 2, 3, 2, 1, 8]
def baseStart_3305731 : Nat := 118140960795 + 3305731 * 2 ^ 59
def prefixEnd_3305731 : Nat := 4983230072969 + 3 ^ 40 * 3305731 * 2
def baseEnd_3305731 : Nat := 377206426104024676879939

theorem tailTrace_3305731 : CollatzResearch.WordTrace tailWord_3305731 prefixEnd_3305731 377206426104024676879939 := by
  unfold tailWord_3305731
  simp only [CollatzResearch.WordTrace]
  refine ⟨120569914786908635751885047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80379943191272423834590031 120569914786908635751885047)
  ·
    refine ⟨180854872180362953627827571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120569914786908635751885047 180854872180362953627827571)
    ·
      refine ⟨271282308270544430441741357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180854872180362953627827571 271282308270544430441741357)
      ·
        refine ⟨101730865601454161415653009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 271282308270544430441741357 101730865601454161415653009)
        ·
          refine ⟨76298149201090621061739757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101730865601454161415653009 76298149201090621061739757)
          ·
            refine ⟨28611805950408982898152409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76298149201090621061739757 28611805950408982898152409)
            ·
              refine ⟨21458854462806737173614307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28611805950408982898152409 21458854462806737173614307)
              ·
                refine ⟨32188281694210105760421461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21458854462806737173614307 32188281694210105760421461)
                ·
                  refine ⟨377206426104024676879939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 32188281694210105760421461 377206426104024676879939)
                  ·
                    rfl

theorem cell22_3305731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 1, 8].length) (baseStart_3305731 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3305731 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3305731 prefixEnd_3305731 := by exact prefixLift 3305731
  have htrace : WordTrace (prefixWord ++ tailWord_3305731) baseStart_3305731 baseEnd_3305731 := by
    simpa [prefixWord, tailWord_3305731, baseEnd_3305731] using wordTrace_append hprefix tailTrace_3305731
  have hstable : (prefixWord ++ tailWord_3305731).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3305731).length < 2 ^ (prefixWord ++ tailWord_3305731).sum := by decide
  have hdescent : baseEnd_3305731 < baseStart_3305731 := by decide
  rcases family_descends (prefixWord ++ tailWord_3305731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3305733 : List Nat := [1, 3, 1, 1, 2, 1, 2, 6, 1, 4]
def baseStart_3305733 : Nat := 118140960795 + 3305733 * 2 ^ 59
def prefixEnd_3305733 : Nat := 4983230072969 + 3 ^ 40 * 3305733 * 2
def baseEnd_3305733 : Nat := 1131619962952946692089811

theorem tailTrace_3305733 : CollatzResearch.WordTrace tailWord_3305733 prefixEnd_3305733 1131619962952946692089811 := by
  unfold tailWord_3305733
  simp only [CollatzResearch.WordTrace]
  refine ⟨120569987732901390093457853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80379991821934260062305235 120569987732901390093457853)
  ·
    refine ⟨45213745399838021285046695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120569987732901390093457853 45213745399838021285046695)
    ·
      refine ⟨67820618099757031927570043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45213745399838021285046695 67820618099757031927570043)
      ·
        refine ⟨101730927149635547891355065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67820618099757031927570043 101730927149635547891355065)
        ·
          refine ⟨76298195362226660918516299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101730927149635547891355065 76298195362226660918516299)
          ·
            refine ⟨114447293043339991377774449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76298195362226660918516299 114447293043339991377774449)
            ·
              refine ⟨85835469782504993533330837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114447293043339991377774449 85835469782504993533330837)
              ·
                refine ⟨4023537646054921571874883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 85835469782504993533330837 4023537646054921571874883)
                ·
                  refine ⟨6035306469082382357812325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4023537646054921571874883 6035306469082382357812325)
                  ·
                    refine ⟨1131619962952946692089811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6035306469082382357812325 1131619962952946692089811)
                    ·
                      rfl

theorem cell22_3305733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 6, 1, 4].length) (baseStart_3305733 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3305733 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3305733 prefixEnd_3305733 := by exact prefixLift 3305733
  have htrace : WordTrace (prefixWord ++ tailWord_3305733) baseStart_3305733 baseEnd_3305733 := by
    simpa [prefixWord, tailWord_3305733, baseEnd_3305733] using wordTrace_append hprefix tailTrace_3305733
  have hstable : (prefixWord ++ tailWord_3305733).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3305733).length < 2 ^ (prefixWord ++ tailWord_3305733).sum := by decide
  have hdescent : baseEnd_3305733 < baseStart_3305733 := by decide
  rcases family_descends (prefixWord ++ tailWord_3305733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3305758 : List Nat := [4, 3, 2, 1, 1, 3, 2, 2, 1, 3]
def baseStart_3305758 : Nat := 118140960795 + 3305758 * 2 ^ 59
def prefixEnd_3305758 : Nat := 4983230072969 + 3 ^ 40 * 3305758 * 2
def baseEnd_3305758 : Nat := 1131628520963854960214735

theorem tailTrace_3305758 : CollatzResearch.WordTrace tailWord_3305758 prefixEnd_3305758 1131628520963854960214735 := by
  unfold tailWord_3305758
  simp only [CollatzResearch.WordTrace]
  refine ⟨15071362444726352420389741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80380599705207212908745285 15071362444726352420389741)
  ·
    refine ⟨5651760916772382157646153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15071362444726352420389741 5651760916772382157646153)
    ·
      refine ⟨4238820687579286618234615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5651760916772382157646153 4238820687579286618234615)
      ·
        refine ⟨6358231031368929927351923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4238820687579286618234615 6358231031368929927351923)
        ·
          refine ⟨9537346547053394891027885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6358231031368929927351923 9537346547053394891027885)
          ·
            refine ⟨3576504955145023084135457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9537346547053394891027885 3576504955145023084135457)
            ·
              refine ⟨2682378716358767313101593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3576504955145023084135457 2682378716358767313101593)
              ·
                refine ⟨2011784037269075484826195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2682378716358767313101593 2011784037269075484826195)
                ·
                  refine ⟨3017676055903613227239293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2011784037269075484826195 3017676055903613227239293)
                  ·
                    refine ⟨1131628520963854960214735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3017676055903613227239293 1131628520963854960214735)
                    ·
                      rfl

theorem cell22_3305758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 2, 2, 1, 3].length) (baseStart_3305758 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3305758 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3305758 prefixEnd_3305758 := by exact prefixLift 3305758
  have htrace : WordTrace (prefixWord ++ tailWord_3305758) baseStart_3305758 baseEnd_3305758 := by
    simpa [prefixWord, tailWord_3305758, baseEnd_3305758] using wordTrace_append hprefix tailTrace_3305758
  have hstable : (prefixWord ++ tailWord_3305758).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3305758).length < 2 ^ (prefixWord ++ tailWord_3305758).sum := by decide
  have hdescent : baseEnd_3305758 < baseStart_3305758 := by decide
  rcases family_descends (prefixWord ++ tailWord_3305758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3305776 : List Nat := [2, 1, 1, 1, 2, 2, 2, 11]
def baseStart_3305776 : Nat := 118140960795 + 3305776 * 2 ^ 59
def prefixEnd_3305776 : Nat := 4983230072969 + 3 ^ 40 * 3305776 * 2
def baseEnd_3305776 : Nat := 125737186970189879251631

theorem tailTrace_3305776 : CollatzResearch.WordTrace tailWord_3305776 prefixEnd_3305776 125737186970189879251631 := by
  unfold tailWord_3305776
  simp only [CollatzResearch.WordTrace]
  refine ⟨60285778035872804218636591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80381037381163738958182121 60285778035872804218636591)
  ·
    refine ⟨90428667053809206327954887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60285778035872804218636591 90428667053809206327954887)
    ·
      refine ⟨135643000580713809491932331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90428667053809206327954887 135643000580713809491932331)
      ·
        refine ⟨203464500871070714237898497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135643000580713809491932331 203464500871070714237898497)
        ·
          refine ⟨152598375653303035678423873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 203464500871070714237898497 152598375653303035678423873)
          ·
            refine ⟨114448781739977276758817905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 152598375653303035678423873 114448781739977276758817905)
            ·
              refine ⟨85836586304982957569113429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114448781739977276758817905 85836586304982957569113429)
              ·
                refine ⟨125737186970189879251631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 85836586304982957569113429 125737186970189879251631)
                ·
                  rfl

theorem cell22_3305776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 11].length) (baseStart_3305776 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3305776 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3305776 prefixEnd_3305776 := by exact prefixLift 3305776
  have htrace : WordTrace (prefixWord ++ tailWord_3305776) baseStart_3305776 baseEnd_3305776 := by
    simpa [prefixWord, tailWord_3305776, baseEnd_3305776] using wordTrace_append hprefix tailTrace_3305776
  have hstable : (prefixWord ++ tailWord_3305776).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3305776).length < 2 ^ (prefixWord ++ tailWord_3305776).sum := by decide
  have hdescent : baseEnd_3305776 < baseStart_3305776 := by decide
  rcases family_descends (prefixWord ++ tailWord_3305776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3305780 : List Nat := [2, 5, 1, 1, 1, 2, 1, 3, 1, 5]
def baseStart_3305780 : Nat := 118140960795 + 3305780 * 2 ^ 59
def prefixEnd_3305780 : Nat := 4983230072969 + 3 ^ 40 * 3305780 * 2
def baseEnd_3305780 : Nat := 1131636052013454236164667

theorem tailTrace_3305780 : CollatzResearch.WordTrace tailWord_3305780 prefixEnd_3305780 1131636052013454236164667 := by
  unfold tailWord_3305780
  simp only [CollatzResearch.WordTrace]
  refine ⟨60285850981865558560209397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80381134642487411413612529 60285850981865558560209397)
  ·
    refine ⟨5651798529549896115019631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 60285850981865558560209397 5651798529549896115019631)
    ·
      refine ⟨8477697794324844172529447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5651798529549896115019631 8477697794324844172529447)
      ·
        refine ⟨12716546691487266258794171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8477697794324844172529447 12716546691487266258794171)
        ·
          refine ⟨19074820037230899388191257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12716546691487266258794171 19074820037230899388191257)
          ·
            refine ⟨14306115027923174541143443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19074820037230899388191257 14306115027923174541143443)
            ·
              refine ⟨21459172541884761811715165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14306115027923174541143443 21459172541884761811715165)
              ·
                refine ⟨8047189703206785679393187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21459172541884761811715165 8047189703206785679393187)
                ·
                  refine ⟨12070784554810178519089781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8047189703206785679393187 12070784554810178519089781)
                  ·
                    refine ⟨1131636052013454236164667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12070784554810178519089781 1131636052013454236164667)
                    ·
                      rfl

theorem cell22_3305780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 3, 1, 5].length) (baseStart_3305780 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3305780 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3305780 prefixEnd_3305780 := by exact prefixLift 3305780
  have htrace : WordTrace (prefixWord ++ tailWord_3305780) baseStart_3305780 baseEnd_3305780 := by
    simpa [prefixWord, tailWord_3305780, baseEnd_3305780] using wordTrace_append hprefix tailTrace_3305780
  have hstable : (prefixWord ++ tailWord_3305780).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3305780).length < 2 ^ (prefixWord ++ tailWord_3305780).sum := by decide
  have hdescent : baseEnd_3305780 < baseStart_3305780 := by decide
  rcases family_descends (prefixWord ++ tailWord_3305780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3305876 : List Nat := [2, 4, 2, 1, 4, 1, 1, 1, 3, 3]
def baseStart_3305876 : Nat := 118140960795 + 3305876 * 2 ^ 59
def prefixEnd_3305876 : Nat := 4983230072969 + 3 ^ 40 * 3305876 * 2
def baseEnd_3305876 : Nat := 1131668914775341985764373

theorem tailTrace_3305876 : CollatzResearch.WordTrace tailWord_3305876 prefixEnd_3305876 1131668914775341985764373 := by
  unfold tailWord_3305876
  simp only [CollatzResearch.WordTrace]
  refine ⟨60287601685691662757956741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80383468914255550343942321 60287601685691662757956741)
  ·
    refine ⟨11303925316067186767116889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60287601685691662757956741 11303925316067186767116889)
    ·
      refine ⟨8477943987050390075337667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11303925316067186767116889 8477943987050390075337667)
      ·
        refine ⟨12716915980575585113006501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8477943987050390075337667 12716915980575585113006501)
        ·
          refine ⟨2384421746357922208688719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12716915980575585113006501 2384421746357922208688719)
          ·
            refine ⟨3576632619536883313033079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2384421746357922208688719 3576632619536883313033079)
            ·
              refine ⟨5364948929305324969549619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3576632619536883313033079 5364948929305324969549619)
              ·
                refine ⟨8047423393957987454324429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5364948929305324969549619 8047423393957987454324429)
                ·
                  refine ⟨3017783772734245295371661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8047423393957987454324429 3017783772734245295371661)
                  ·
                    refine ⟨1131668914775341985764373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3017783772734245295371661 1131668914775341985764373)
                    ·
                      rfl

theorem cell22_3305876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 1, 1, 3, 3].length) (baseStart_3305876 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3305876 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3305876 prefixEnd_3305876 := by exact prefixLift 3305876
  have htrace : WordTrace (prefixWord ++ tailWord_3305876) baseStart_3305876 baseEnd_3305876 := by
    simpa [prefixWord, tailWord_3305876, baseEnd_3305876] using wordTrace_append hprefix tailTrace_3305876
  have hstable : (prefixWord ++ tailWord_3305876).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3305876).length < 2 ^ (prefixWord ++ tailWord_3305876).sum := by decide
  have hdescent : baseEnd_3305876 < baseStart_3305876 := by decide
  rcases family_descends (prefixWord ++ tailWord_3305876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3305928 : List Nat := [2, 1, 3, 1, 3, 12]
def baseStart_3305928 : Nat := 118140960795 + 3305928 * 2 ^ 59
def prefixEnd_3305928 : Nat := 4983230072969 + 3 ^ 40 * 3305928 * 2
def baseEnd_3305928 : Nat := 13971440931333718314373

theorem tailTrace_3305928 : CollatzResearch.WordTrace tailWord_3305928 prefixEnd_3305928 13971440931333718314373 := by
  unfold tailWord_3305928
  simp only [CollatzResearch.WordTrace]
  refine ⟨60288549983597469198403219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80384733311463292264537625 60288549983597469198403219)
  ·
    refine ⟨90432824975396203797604829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60288549983597469198403219 90432824975396203797604829)
    ·
      refine ⟨33912309365773576424101811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90432824975396203797604829 33912309365773576424101811)
      ·
        refine ⟨50868464048660364636152717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33912309365773576424101811 50868464048660364636152717)
        ·
          refine ⟨19075674018247636738557269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50868464048660364636152717 19075674018247636738557269)
          ·
            refine ⟨13971440931333718314373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 19075674018247636738557269 13971440931333718314373)
            ·
              rfl

theorem cell22_3305928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 12].length) (baseStart_3305928 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3305928 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3305928 prefixEnd_3305928 := by exact prefixLift 3305928
  have htrace : WordTrace (prefixWord ++ tailWord_3305928) baseStart_3305928 baseEnd_3305928 := by
    simpa [prefixWord, tailWord_3305928, baseEnd_3305928] using wordTrace_append hprefix tailTrace_3305928
  have hstable : (prefixWord ++ tailWord_3305928).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3305928).length < 2 ^ (prefixWord ++ tailWord_3305928).sum := by decide
  have hdescent : baseEnd_3305928 < baseStart_3305928 := by decide
  rcases family_descends (prefixWord ++ tailWord_3305928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3305930 : List Nat := [3, 1, 2, 1, 2, 2, 1, 4, 2, 4]
def baseStart_3305930 : Nat := 118140960795 + 3305930 * 2 ^ 59
def prefixEnd_3305930 : Nat := 4983230072969 + 3 ^ 40 * 3305930 * 2
def baseEnd_3305930 : Nat := 1131687400078903844914207

theorem tailTrace_3305930 : CollatzResearch.WordTrace tailWord_3305930 prefixEnd_3305930 1131687400078903844914207 := by
  unfold tailWord_3305930
  simp only [CollatzResearch.WordTrace]
  refine ⟨30144293228296923184594811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80384781942125128492252829 30144293228296923184594811)
  ·
    refine ⟨45216439842445384776892217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30144293228296923184594811 45216439842445384776892217)
    ·
      refine ⟨33912329881834038582669163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45216439842445384776892217 33912329881834038582669163)
      ·
        refine ⟨50868494822751057874003745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33912329881834038582669163 50868494822751057874003745)
        ·
          refine ⟨38151371117063293405502809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50868494822751057874003745 38151371117063293405502809)
          ·
            refine ⟨28613528337797470054127107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38151371117063293405502809 28613528337797470054127107)
            ·
              refine ⟨42920292506696205081190661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28613528337797470054127107 42920292506696205081190661)
              ·
                refine ⟨8047554845005538452723249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42920292506696205081190661 8047554845005538452723249)
                ·
                  refine ⟨6035666133754153839542437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8047554845005538452723249 6035666133754153839542437)
                  ·
                    refine ⟨1131687400078903844914207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6035666133754153839542437 1131687400078903844914207)
                    ·
                      rfl

theorem cell22_3305930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 4, 2, 4].length) (baseStart_3305930 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3305930 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3305930 prefixEnd_3305930 := by exact prefixLift 3305930
  have htrace : WordTrace (prefixWord ++ tailWord_3305930) baseStart_3305930 baseEnd_3305930 := by
    simpa [prefixWord, tailWord_3305930, baseEnd_3305930] using wordTrace_append hprefix tailTrace_3305930
  have hstable : (prefixWord ++ tailWord_3305930).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3305930).length < 2 ^ (prefixWord ++ tailWord_3305930).sum := by decide
  have hdescent : baseEnd_3305930 < baseStart_3305930 := by decide
  rcases family_descends (prefixWord ++ tailWord_3305930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3305943 : List Nat := [1, 1, 3, 2, 1, 1, 1, 1, 4, 7]
def baseStart_3305943 : Nat := 118140960795 + 3305943 * 2 ^ 59
def prefixEnd_3305943 : Nat := 4983230072969 + 3 ^ 40 * 3305943 * 2
def baseEnd_3305943 : Nat := 1131691850244576144339167

theorem tailTrace_3305943 : CollatzResearch.WordTrace tailWord_3305943 prefixEnd_3305943 1131691850244576144339167 := by
  unfold tailWord_3305943
  simp only [CollatzResearch.WordTrace]
  refine ⟨120577647062140595958602483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80385098041427063972401655 120577647062140595958602483)
  ·
    refine ⟨180866470593210893937903725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120577647062140595958602483 180866470593210893937903725)
    ·
      refine ⟨67824926472454085226713897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 180866470593210893937903725 67824926472454085226713897)
      ·
        refine ⟨50868694854340563920035423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67824926472454085226713897 50868694854340563920035423)
        ·
          refine ⟨76303042281510845880053135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50868694854340563920035423 76303042281510845880053135)
          ·
            refine ⟨114454563422266268820079703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76303042281510845880053135 114454563422266268820079703)
            ·
              refine ⟨171681845133399403230119555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114454563422266268820079703 171681845133399403230119555)
              ·
                refine ⟨257522767700099104845179333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 171681845133399403230119555 257522767700099104845179333)
                ·
                  refine ⟨48285518943768582158471125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 257522767700099104845179333 48285518943768582158471125)
                  ·
                    refine ⟨1131691850244576144339167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48285518943768582158471125 1131691850244576144339167)
                    ·
                      rfl

theorem cell22_3305943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 4, 7].length) (baseStart_3305943 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3305943 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3305943 prefixEnd_3305943 := by exact prefixLift 3305943
  have htrace : WordTrace (prefixWord ++ tailWord_3305943) baseStart_3305943 baseEnd_3305943 := by
    simpa [prefixWord, tailWord_3305943, baseEnd_3305943] using wordTrace_append hprefix tailTrace_3305943
  have hstable : (prefixWord ++ tailWord_3305943).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3305943).length < 2 ^ (prefixWord ++ tailWord_3305943).sum := by decide
  have hdescent : baseEnd_3305943 < baseStart_3305943 := by decide
  rcases family_descends (prefixWord ++ tailWord_3305943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3305962 : List Nat := [3, 1, 3, 1, 3, 2, 3, 6]
def baseStart_3305962 : Nat := 118140960795 + 3305962 * 2 ^ 59
def prefixEnd_3305962 : Nat := 4983230072969 + 3 ^ 40 * 3305962 * 2
def baseEnd_3305962 : Nat := 125744261592540714234901

theorem tailTrace_3305962 : CollatzResearch.WordTrace tailWord_3305962 prefixEnd_3305962 125744261592540714234901 := by
  unfold tailWord_3305962
  simp only [CollatzResearch.WordTrace]
  refine ⟨30144585012267940550886035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80385560032714508135696093 30144585012267940550886035)
  ·
    refine ⟨45216877518401910826329053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30144585012267940550886035 45216877518401910826329053)
    ·
      refine ⟨16956329069400716559873395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45216877518401910826329053 16956329069400716559873395)
      ·
        refine ⟨25434493604101074839810093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16956329069400716559873395 25434493604101074839810093)
        ·
          refine ⟨9537935101537903064928785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25434493604101074839810093 9537935101537903064928785)
          ·
            refine ⟨7153451326153427298696589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9537935101537903064928785 7153451326153427298696589)
            ·
              refine ⟨2682544247307535237011221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7153451326153427298696589 2682544247307535237011221)
              ·
                refine ⟨125744261592540714234901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2682544247307535237011221 125744261592540714234901)
                ·
                  rfl

theorem cell22_3305962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 3, 6].length) (baseStart_3305962 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3305962 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3305962 prefixEnd_3305962 := by exact prefixLift 3305962
  have htrace : WordTrace (prefixWord ++ tailWord_3305962) baseStart_3305962 baseEnd_3305962 := by
    simpa [prefixWord, tailWord_3305962, baseEnd_3305962] using wordTrace_append hprefix tailTrace_3305962
  have hstable : (prefixWord ++ tailWord_3305962).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3305962).length < 2 ^ (prefixWord ++ tailWord_3305962).sum := by decide
  have hdescent : baseEnd_3305962 < baseStart_3305962 := by decide
  rcases family_descends (prefixWord ++ tailWord_3305962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3305994 : List Nat := [3, 1, 2, 2, 2, 1, 1, 6, 1, 3]
def baseStart_3305994 : Nat := 118140960795 + 3305994 * 2 ^ 59
def prefixEnd_3305994 : Nat := 4983230072969 + 3 ^ 40 * 3305994 * 2
def baseEnd_3305994 : Nat := 1131709308586829011314011

theorem tailTrace_3305994 : CollatzResearch.WordTrace tailWord_3305994 prefixEnd_3305994 1131709308586829011314011 := by
  unfold tailWord_3305994
  simp only [CollatzResearch.WordTrace]
  refine ⟨30144876796238957917177259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80386338123303887779139357 30144876796238957917177259)
  ·
    refine ⟨45217315194358436875765889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30144876796238957917177259 45217315194358436875765889)
    ·
      refine ⟨33912986395768827656824417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45217315194358436875765889 33912986395768827656824417)
      ·
        refine ⟨25434739796826620742618313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33912986395768827656824417 25434739796826620742618313)
        ·
          refine ⟨19076054847619965556963735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25434739796826620742618313 19076054847619965556963735)
          ·
            refine ⟨28614082271429948335445603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19076054847619965556963735 28614082271429948335445603)
            ·
              refine ⟨42921123407144922503168405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28614082271429948335445603 42921123407144922503168405)
              ·
                refine ⟨2011927659709918242336019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 42921123407144922503168405 2011927659709918242336019)
                ·
                  refine ⟨3017891489564877363504029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2011927659709918242336019 3017891489564877363504029)
                  ·
                    refine ⟨1131709308586829011314011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3017891489564877363504029 1131709308586829011314011)
                    ·
                      rfl

theorem cell22_3305994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 6, 1, 3].length) (baseStart_3305994 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3305994 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3305994 prefixEnd_3305994 := by exact prefixLift 3305994
  have htrace : WordTrace (prefixWord ++ tailWord_3305994) baseStart_3305994 baseEnd_3305994 := by
    simpa [prefixWord, tailWord_3305994, baseEnd_3305994] using wordTrace_append hprefix tailTrace_3305994
  have hstable : (prefixWord ++ tailWord_3305994).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3305994).length < 2 ^ (prefixWord ++ tailWord_3305994).sum := by decide
  have hdescent : baseEnd_3305994 < baseStart_3305994 := by decide
  rcases family_descends (prefixWord ++ tailWord_3305994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3306005 : List Nat := [1, 3, 2, 1, 3, 1, 1, 3, 2, 5]
def baseStart_3306005 : Nat := 118140960795 + 3306005 * 2 ^ 59
def prefixEnd_3306005 : Nat := 4983230072969 + 3 ^ 40 * 3306005 * 2
def baseEnd_3306005 : Nat := 1131713074111628649288977

theorem tailTrace_3306005 : CollatzResearch.WordTrace tailWord_3306005 prefixEnd_3306005 1131713074111628649288977 := by
  unfold tailWord_3306005
  simp only [CollatzResearch.WordTrace]
  refine ⟨120579908387915980547359469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80386605591943987031572979 120579908387915980547359469)
  ·
    refine ⟨45217465645468492705259801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120579908387915980547359469 45217465645468492705259801)
    ·
      refine ⟨33913099234101369528944851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45217465645468492705259801 33913099234101369528944851)
      ·
        refine ⟨50869648851152054293417277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33913099234101369528944851 50869648851152054293417277)
        ·
          refine ⟨19076118319182020360031479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50869648851152054293417277 19076118319182020360031479)
          ·
            refine ⟨28614177478773030540047219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19076118319182020360031479 28614177478773030540047219)
            ·
              refine ⟨42921266218159545810070829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28614177478773030540047219 42921266218159545810070829)
              ·
                refine ⟨16095474831809829678776561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42921266218159545810070829 16095474831809829678776561)
                ·
                  refine ⟨12071606123857372259082421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16095474831809829678776561 12071606123857372259082421)
                  ·
                    refine ⟨1131713074111628649288977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12071606123857372259082421 1131713074111628649288977)
                    ·
                      rfl

theorem cell22_3306005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 3, 2, 5].length) (baseStart_3306005 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3306005 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3306005 prefixEnd_3306005 := by exact prefixLift 3306005
  have htrace : WordTrace (prefixWord ++ tailWord_3306005) baseStart_3306005 baseEnd_3306005 := by
    simpa [prefixWord, tailWord_3306005, baseEnd_3306005] using wordTrace_append hprefix tailTrace_3306005
  have hstable : (prefixWord ++ tailWord_3306005).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3306005).length < 2 ^ (prefixWord ++ tailWord_3306005).sum := by decide
  have hdescent : baseEnd_3306005 < baseStart_3306005 := by decide
  rcases family_descends (prefixWord ++ tailWord_3306005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3306037 : List Nat := [1, 3, 3, 1, 1, 2, 1, 5, 1, 4]
def baseStart_3306037 : Nat := 118140960795 + 3306037 * 2 ^ 59
def prefixEnd_3306037 : Nat := 4983230072969 + 3 ^ 40 * 3306037 * 2
def baseEnd_3306037 : Nat := 1131724028365591232488879

theorem tailTrace_3306037 : CollatzResearch.WordTrace tailWord_3306037 prefixEnd_3306037 1131724028365591232488879 := by
  unfold tailWord_3306037
  simp only [CollatzResearch.WordTrace]
  refine ⟨120581075523800050012524365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80387383682533366675016243 120581075523800050012524365)
  ·
    refine ⟨45217903321425018754696637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120581075523800050012524365 45217903321425018754696637)
    ·
      refine ⟨16956713745534382033011239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45217903321425018754696637 16956713745534382033011239)
      ·
        refine ⟨25435070618301573049516859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16956713745534382033011239 25435070618301573049516859)
        ·
          refine ⟨38152605927452359574275289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25435070618301573049516859 38152605927452359574275289)
          ·
            refine ⟨28614454445589269680706467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38152605927452359574275289 28614454445589269680706467)
            ·
              refine ⟨42921681668383904521059701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28614454445589269680706467 42921681668383904521059701)
              ·
                refine ⟨4023907656410991048849347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42921681668383904521059701 4023907656410991048849347)
                ·
                  refine ⟨6035861484616486573274021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4023907656410991048849347 6035861484616486573274021)
                  ·
                    refine ⟨1131724028365591232488879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6035861484616486573274021 1131724028365591232488879)
                    ·
                      rfl

theorem cell22_3306037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 5, 1, 4].length) (baseStart_3306037 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3306037 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3306037 prefixEnd_3306037 := by exact prefixLift 3306037
  have htrace : WordTrace (prefixWord ++ tailWord_3306037) baseStart_3306037 baseEnd_3306037 := by
    simpa [prefixWord, tailWord_3306037, baseEnd_3306037] using wordTrace_append hprefix tailTrace_3306037
  have hstable : (prefixWord ++ tailWord_3306037).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3306037).length < 2 ^ (prefixWord ++ tailWord_3306037).sum := by decide
  have hdescent : baseEnd_3306037 < baseStart_3306037 := by decide
  rcases family_descends (prefixWord ++ tailWord_3306037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3306080 : List Nat := [2, 1, 1, 3, 2, 1, 4, 8]
def baseStart_3306080 : Nat := 118140960795 + 3306080 * 2 ^ 59
def prefixEnd_3306080 : Nat := 4983230072969 + 3 ^ 40 * 3306080 * 2
def baseEnd_3306080 : Nat := 125748749793817050407083

theorem tailTrace_3306080 : CollatzResearch.WordTrace tailWord_3306080 prefixEnd_3306080 125748749793817050407083 := by
  unfold tailWord_3306080
  simp only [CollatzResearch.WordTrace]
  refine ⟨60291321931322134178169847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80388429241762845570893129 60291321931322134178169847)
  ·
    refine ⟨90436982896983201267254771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60291321931322134178169847 90436982896983201267254771)
    ·
      refine ⟨135655474345474801900882157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90436982896983201267254771 135655474345474801900882157)
      ·
        refine ⟨50870802879553050712830809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135655474345474801900882157 50870802879553050712830809)
        ·
          refine ⟨38153102159664788034623107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50870802879553050712830809 38153102159664788034623107)
          ·
            refine ⟨57229653239497182051934661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38153102159664788034623107 57229653239497182051934661)
            ·
              refine ⟨10730559982405721634737749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57229653239497182051934661 10730559982405721634737749)
              ·
                refine ⟨125748749793817050407083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10730559982405721634737749 125748749793817050407083)
                ·
                  rfl

theorem cell22_3306080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4, 8].length) (baseStart_3306080 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3306080 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3306080 prefixEnd_3306080 := by exact prefixLift 3306080
  have htrace : WordTrace (prefixWord ++ tailWord_3306080) baseStart_3306080 baseEnd_3306080 := by
    simpa [prefixWord, tailWord_3306080, baseEnd_3306080] using wordTrace_append hprefix tailTrace_3306080
  have hstable : (prefixWord ++ tailWord_3306080).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3306080).length < 2 ^ (prefixWord ++ tailWord_3306080).sum := by decide
  have hdescent : baseEnd_3306080 < baseStart_3306080 := by decide
  rcases family_descends (prefixWord ++ tailWord_3306080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3306159 : List Nat := [1, 1, 2, 1, 2, 7, 1, 2, 5]
def baseStart_3306159 : Nat := 118140960795 + 3306159 * 2 ^ 59
def prefixEnd_3306159 : Nat := 4983230072969 + 3 ^ 40 * 3306159 * 2
def baseEnd_3306159 : Nat := 377255263819607860312835

theorem tailTrace_3306159 : CollatzResearch.WordTrace tailWord_3306159 prefixEnd_3306159 377255263819607860312835 := by
  unfold tailWord_3306159
  simp only [CollatzResearch.WordTrace]
  refine ⟨120585525229358064848465531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80390350152905376565643687 120585525229358064848465531)
  ·
    refine ⟨180878287844037097272698297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120585525229358064848465531 180878287844037097272698297)
    ·
      refine ⟨135658715883027822954523723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180878287844037097272698297 135658715883027822954523723)
      ·
        refine ⟨203488073824541734431785585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135658715883027822954523723 203488073824541734431785585)
        ·
          refine ⟨152616055368406300823839189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 203488073824541734431785585 152616055368406300823839189)
          ·
            refine ⟨3576938797697022675558731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 152616055368406300823839189 3576938797697022675558731)
            ·
              refine ⟨5365408196545534013338097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3576938797697022675558731 5365408196545534013338097)
              ·
                refine ⟨4024056147409150510003573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5365408196545534013338097 4024056147409150510003573)
                ·
                  refine ⟨377255263819607860312835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4024056147409150510003573 377255263819607860312835)
                  ·
                    rfl

theorem cell22_3306159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 1, 2, 5].length) (baseStart_3306159 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3306159 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3306159 prefixEnd_3306159 := by exact prefixLift 3306159
  have htrace : WordTrace (prefixWord ++ tailWord_3306159) baseStart_3306159 baseEnd_3306159 := by
    simpa [prefixWord, tailWord_3306159, baseEnd_3306159] using wordTrace_append hprefix tailTrace_3306159
  have hstable : (prefixWord ++ tailWord_3306159).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3306159).length < 2 ^ (prefixWord ++ tailWord_3306159).sum := by decide
  have hdescent : baseEnd_3306159 < baseStart_3306159 := by decide
  rcases family_descends (prefixWord ++ tailWord_3306159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3306197 : List Nat := [1, 3, 2, 5, 2, 1, 1, 3, 1, 3]
def baseStart_3306197 : Nat := 118140960795 + 3306197 * 2 ^ 59
def prefixEnd_3306197 : Nat := 4983230072969 + 3 ^ 40 * 3306197 * 2
def baseEnd_3306197 : Nat := 1131778799635404148488389

theorem tailTrace_3306197 : CollatzResearch.WordTrace tailWord_3306197 prefixEnd_3306197 1131778799635404148488389 := by
  unfold tailWord_3306197
  simp only [CollatzResearch.WordTrace]
  refine ⟨120586911203220397338348845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80391274135480264892232563 120586911203220397338348845)
  ·
    refine ⟨45220091701207649001880817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120586911203220397338348845 45220091701207649001880817)
    ·
      refine ⟨33915068775905736751410613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45220091701207649001880817 33915068775905736751410613)
      ·
        refine ⟨3179537697741162820444745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 33915068775905736751410613 3179537697741162820444745)
        ·
          refine ⟨2384653273305872115333559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3179537697741162820444745 2384653273305872115333559)
          ·
            refine ⟨3576979909958808173000339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2384653273305872115333559 3576979909958808173000339)
            ·
              refine ⟨5365469864938212259500509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3576979909958808173000339 5365469864938212259500509)
              ·
                refine ⟨2012051199351829597312691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5365469864938212259500509 2012051199351829597312691)
                ·
                  refine ⟨3018076799027744395969037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2012051199351829597312691 3018076799027744395969037)
                  ·
                    refine ⟨1131778799635404148488389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3018076799027744395969037 1131778799635404148488389)
                    ·
                      rfl

theorem cell22_3306197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 1, 3, 1, 3].length) (baseStart_3306197 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3306197 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3306197 prefixEnd_3306197 := by exact prefixLift 3306197
  have htrace : WordTrace (prefixWord ++ tailWord_3306197) baseStart_3306197 baseEnd_3306197 := by
    simpa [prefixWord, tailWord_3306197, baseEnd_3306197] using wordTrace_append hprefix tailTrace_3306197
  have hstable : (prefixWord ++ tailWord_3306197).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3306197).length < 2 ^ (prefixWord ++ tailWord_3306197).sum := by decide
  have hdescent : baseEnd_3306197 < baseStart_3306197 := by decide
  rcases family_descends (prefixWord ++ tailWord_3306197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3306202 : List Nat := [3, 1, 1, 2, 2, 2, 2, 1, 3, 5]
def baseStart_3306202 : Nat := 118140960795 + 3306202 * 2 ^ 59
def prefixEnd_3306202 : Nat := 4983230072969 + 3 ^ 40 * 3306202 * 2
def baseEnd_3306202 : Nat := 1131780511237585802113373

theorem tailTrace_3306202 : CollatzResearch.WordTrace tailWord_3306202 prefixEnd_3306202 1131780511237585802113373 := by
  unfold tailWord_3306202
  simp only [CollatzResearch.WordTrace]
  refine ⟨30146773392050570798070215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80391395712134855461520573 30146773392050570798070215)
  ·
    refine ⟨45220160088075856197105323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30146773392050570798070215 45220160088075856197105323)
    ·
      refine ⟨67830240132113784295657985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45220160088075856197105323 67830240132113784295657985)
      ·
        refine ⟨50872680099085338221743489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67830240132113784295657985 50872680099085338221743489)
        ·
          refine ⟨38154510074314003666307617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50872680099085338221743489 38154510074314003666307617)
          ·
            refine ⟨28615882555735502749730713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38154510074314003666307617 28615882555735502749730713)
            ·
              refine ⟨21461911916801627062298035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28615882555735502749730713 21461911916801627062298035)
              ·
                refine ⟨32192867875202440593447053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21461911916801627062298035 32192867875202440593447053)
                ·
                  refine ⟨12072325453200915222542645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32192867875202440593447053 12072325453200915222542645)
                  ·
                    refine ⟨1131780511237585802113373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12072325453200915222542645 1131780511237585802113373)
                    ·
                      rfl

theorem cell22_3306202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 1, 3, 5].length) (baseStart_3306202 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3306202 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3306202 prefixEnd_3306202 := by exact prefixLift 3306202
  have htrace : WordTrace (prefixWord ++ tailWord_3306202) baseStart_3306202 baseEnd_3306202 := by
    simpa [prefixWord, tailWord_3306202, baseEnd_3306202] using wordTrace_append hprefix tailTrace_3306202
  have hstable : (prefixWord ++ tailWord_3306202).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3306202).length < 2 ^ (prefixWord ++ tailWord_3306202).sum := by decide
  have hdescent : baseEnd_3306202 < baseStart_3306202 := by decide
  rcases family_descends (prefixWord ++ tailWord_3306202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3306217 : List Nat := [1, 2, 1, 1, 1, 2, 5, 1, 4, 4]
def baseStart_3306217 : Nat := 118140960795 + 3306217 * 2 ^ 59
def prefixEnd_3306217 : Nat := 4983230072969 + 3 ^ 40 * 3306217 * 2
def baseEnd_3306217 : Nat := 1131785646044130762988327

theorem tailTrace_3306217 : CollatzResearch.WordTrace tailWord_3306217 prefixEnd_3306217 1131785646044130762988327 := by
  unfold tailWord_3306217
  simp only [CollatzResearch.WordTrace]
  refine ⟨120587640663147940754076905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80391760442098627169384603 120587640663147940754076905)
  ·
    refine ⟨90440730497360955565557679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120587640663147940754076905 90440730497360955565557679)
    ·
      refine ⟨135661095746041433348336519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90440730497360955565557679 135661095746041433348336519)
      ·
        refine ⟨203491643619062150022504779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135661095746041433348336519 203491643619062150022504779)
        ·
          refine ⟨305237465428593225033757169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203491643619062150022504779 305237465428593225033757169)
          ·
            refine ⟨228928099071444918775317877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 305237465428593225033757169 228928099071444918775317877)
            ·
              refine ⟨21462009287947961135186051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 228928099071444918775317877 21462009287947961135186051)
              ·
                refine ⟨32193013931921941702779077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21462009287947961135186051 32193013931921941702779077)
                ·
                  refine ⟨6036190112235364069271077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32193013931921941702779077 6036190112235364069271077)
                  ·
                    refine ⟨1131785646044130762988327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6036190112235364069271077 1131785646044130762988327)
                    ·
                      rfl

theorem cell22_3306217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 1, 4, 4].length) (baseStart_3306217 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3306217 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3306217 prefixEnd_3306217 := by exact prefixLift 3306217
  have htrace : WordTrace (prefixWord ++ tailWord_3306217) baseStart_3306217 baseEnd_3306217 := by
    simpa [prefixWord, tailWord_3306217, baseEnd_3306217] using wordTrace_append hprefix tailTrace_3306217
  have hstable : (prefixWord ++ tailWord_3306217).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3306217).length < 2 ^ (prefixWord ++ tailWord_3306217).sum := by decide
  have hdescent : baseEnd_3306217 < baseStart_3306217 := by decide
  rcases family_descends (prefixWord ++ tailWord_3306217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3306219 : List Nat := [1, 1, 1, 1, 2, 4, 1, 6, 2, 3]
def baseStart_3306219 : Nat := 118140960795 + 3306219 * 2 ^ 59
def prefixEnd_3306219 : Nat := 4983230072969 + 3 ^ 40 * 3306219 * 2
def baseEnd_3306219 : Nat := 1131786330685003424438321

theorem tailTrace_3306219 : CollatzResearch.WordTrace tailWord_3306219 prefixEnd_3306219 1131786330685003424438321 := by
  unfold tailWord_3306219
  simp only [CollatzResearch.WordTrace]
  refine ⟨120587713609140695095649711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80391809072760463397099807 120587713609140695095649711)
  ·
    refine ⟨180881570413711042643474567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120587713609140695095649711 180881570413711042643474567)
    ·
      refine ⟨271322355620566563965211851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180881570413711042643474567 271322355620566563965211851)
      ·
        refine ⟨406983533430849845947817777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 271322355620566563965211851 406983533430849845947817777)
        ·
          refine ⟨305237650073137384460863333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 406983533430849845947817777 305237650073137384460863333)
          ·
            refine ⟨57232059388713259586411875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 305237650073137384460863333 57232059388713259586411875)
            ·
              refine ⟨85848089083069889379617813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57232059388713259586411875 85848089083069889379617813)
              ·
                refine ⟨4024129175768901064669585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 85848089083069889379617813 4024129175768901064669585)
                ·
                  refine ⟨3018096881826675798502189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4024129175768901064669585 3018096881826675798502189)
                  ·
                    refine ⟨1131786330685003424438321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3018096881826675798502189 1131786330685003424438321)
                    ·
                      rfl

theorem cell22_3306219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 6, 2, 3].length) (baseStart_3306219 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3306219 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3306219 prefixEnd_3306219 := by exact prefixLift 3306219
  have htrace : WordTrace (prefixWord ++ tailWord_3306219) baseStart_3306219 baseEnd_3306219 := by
    simpa [prefixWord, tailWord_3306219, baseEnd_3306219] using wordTrace_append hprefix tailTrace_3306219
  have hstable : (prefixWord ++ tailWord_3306219).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3306219).length < 2 ^ (prefixWord ++ tailWord_3306219).sum := by decide
  have hdescent : baseEnd_3306219 < baseStart_3306219 := by decide
  rcases family_descends (prefixWord ++ tailWord_3306219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3306232 : List Nat := [2, 1, 2, 1, 1, 2, 6, 7]
def baseStart_3306232 : Nat := 118140960795 + 3306232 * 2 ^ 59
def prefixEnd_3306232 : Nat := 4983230072969 + 3 ^ 40 * 3306232 * 2
def baseEnd_3306232 : Nat := 125754531205630635984809

theorem tailTrace_3306232 : CollatzResearch.WordTrace tailWord_3306232 prefixEnd_3306232 125754531205630635984809 := by
  unfold tailWord_3306232
  simp only [CollatzResearch.WordTrace]
  refine ⟨60294093879046799157936475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80392125172062398877248633 60294093879046799157936475)
  ·
    refine ⟨90441140818570198736904713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60294093879046799157936475 90441140818570198736904713)
    ·
      refine ⟨67830855613927649052678535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90441140818570198736904713 67830855613927649052678535)
      ·
        refine ⟨101746283420891473579017803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67830855613927649052678535 101746283420891473579017803)
        ·
          refine ⟨152619425131337210368526705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101746283420891473579017803 152619425131337210368526705)
          ·
            refine ⟨114464568848502907776395029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 152619425131337210368526705 114464568848502907776395029)
            ·
              refine ⟨5365526664773573802018517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 114464568848502907776395029 5365526664773573802018517)
              ·
                refine ⟨125754531205630635984809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5365526664773573802018517 125754531205630635984809)
                ·
                  rfl

theorem cell22_3306232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 6, 7].length) (baseStart_3306232 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3306232 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3306232 prefixEnd_3306232 := by exact prefixLift 3306232
  have htrace : WordTrace (prefixWord ++ tailWord_3306232) baseStart_3306232 baseEnd_3306232 := by
    simpa [prefixWord, tailWord_3306232, baseEnd_3306232] using wordTrace_append hprefix tailTrace_3306232
  have hstable : (prefixWord ++ tailWord_3306232).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3306232).length < 2 ^ (prefixWord ++ tailWord_3306232).sum := by decide
  have hdescent : baseEnd_3306232 < baseStart_3306232 := by decide
  rcases family_descends (prefixWord ++ tailWord_3306232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3306236 : List Nat := [2, 2, 2, 1, 3, 3, 1, 3, 2, 3]
def baseStart_3306236 : Nat := 118140960795 + 3306236 * 2 ^ 59
def prefixEnd_3306236 : Nat := 4983230072969 + 3 ^ 40 * 3306236 * 2
def baseEnd_3306236 : Nat := 1131792150132421046763269

theorem tailTrace_3306236 : CollatzResearch.WordTrace tailWord_3306236 prefixEnd_3306236 1131792150132421046763269 := by
  unfold tailWord_3306236
  simp only [CollatzResearch.WordTrace]
  refine ⟨60294166825039553499509281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80392222433386071332679041 60294166825039553499509281)
  ·
    refine ⟨45220625118779665124631961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60294166825039553499509281 45220625118779665124631961)
    ·
      refine ⟨33915468839084748843473971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45220625118779665124631961 33915468839084748843473971)
      ·
        refine ⟨50873203258627123265210957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33915468839084748843473971 50873203258627123265210957)
        ·
          refine ⟨19077451221985171224454109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50873203258627123265210957 19077451221985171224454109)
          ·
            refine ⟨7154044208244439209170291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19077451221985171224454109 7154044208244439209170291)
            ·
              refine ⟨10731066312366658813755437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7154044208244439209170291 10731066312366658813755437)
              ·
                refine ⟨4024149867137497055158289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10731066312366658813755437 4024149867137497055158289)
                ·
                  refine ⟨3018112400353122791368717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4024149867137497055158289 3018112400353122791368717)
                  ·
                    refine ⟨1131792150132421046763269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3018112400353122791368717 1131792150132421046763269)
                    ·
                      rfl

theorem cell22_3306236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 1, 3, 2, 3].length) (baseStart_3306236 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3306236 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3306236 prefixEnd_3306236 := by exact prefixLift 3306236
  have htrace : WordTrace (prefixWord ++ tailWord_3306236) baseStart_3306236 baseEnd_3306236 := by
    simpa [prefixWord, tailWord_3306236, baseEnd_3306236] using wordTrace_append hprefix tailTrace_3306236
  have hstable : (prefixWord ++ tailWord_3306236).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3306236).length < 2 ^ (prefixWord ++ tailWord_3306236).sum := by decide
  have hdescent : baseEnd_3306236 < baseStart_3306236 := by decide
  rcases family_descends (prefixWord ++ tailWord_3306236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3306281 : List Nat := [1, 2, 1, 1, 1, 1, 1, 10, 1, 3]
def baseStart_3306281 : Nat := 118140960795 + 3306281 * 2 ^ 59
def prefixEnd_3306281 : Nat := 4983230072969 + 3 ^ 40 * 3306281 * 2
def baseEnd_3306281 : Nat := 1131807554552055929388131

theorem tailTrace_3306281 : CollatzResearch.WordTrace tailWord_3306281 prefixEnd_3306281 1131807554552055929388131 := by
  unfold tailWord_3306281
  simp only [CollatzResearch.WordTrace]
  refine ⟨120589974934916079684406697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80393316623277386456271131 120589974934916079684406697)
  ·
    refine ⟨90442481201187059763305023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120589974934916079684406697 90442481201187059763305023)
    ·
      refine ⟨135663721801780589644957535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90442481201187059763305023 135663721801780589644957535)
      ·
        refine ⟨203495582702670884467436303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135663721801780589644957535 203495582702670884467436303)
        ·
          refine ⟨305243374054006326701154455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203495582702670884467436303 305243374054006326701154455)
          ·
            refine ⟨457865061081009490051731683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 305243374054006326701154455 457865061081009490051731683)
            ·
              refine ⟨686797591621514235077597525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 457865061081009490051731683 686797591621514235077597525)
              ·
                refine ⟨2012102319203654985578899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 686797591621514235077597525 2012102319203654985578899)
                ·
                  refine ⟨3018153478805482478368349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2012102319203654985578899 3018153478805482478368349)
                  ·
                    refine ⟨1131807554552055929388131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3018153478805482478368349 1131807554552055929388131)
                    ·
                      rfl

theorem cell22_3306281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 10, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 10, 1, 3].length) (baseStart_3306281 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3306281 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3306281 prefixEnd_3306281 := by exact prefixLift 3306281
  have htrace : WordTrace (prefixWord ++ tailWord_3306281) baseStart_3306281 baseEnd_3306281 := by
    simpa [prefixWord, tailWord_3306281, baseEnd_3306281] using wordTrace_append hprefix tailTrace_3306281
  have hstable : (prefixWord ++ tailWord_3306281).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3306281).length < 2 ^ (prefixWord ++ tailWord_3306281).sum := by decide
  have hdescent : baseEnd_3306281 < baseStart_3306281 := by decide
  rcases family_descends (prefixWord ++ tailWord_3306281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3306339 : List Nat := [1, 1, 1, 5, 3, 1, 1, 3, 6]
def baseStart_3306339 : Nat := 118140960795 + 3306339 * 2 ^ 59
def prefixEnd_3306339 : Nat := 4983230072969 + 3 ^ 40 * 3306339 * 2
def baseEnd_3306339 : Nat := 377275803045787703812651

theorem tailTrace_3306339 : CollatzResearch.WordTrace tailWord_3306339 prefixEnd_3306339 377275803045787703812651 := by
  unfold tailWord_3306339
  simp only [CollatzResearch.WordTrace]
  refine ⟨120592090368705955590018071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80394726912470637060012047 120592090368705955590018071)
  ·
    refine ⟨180888135553058933385027107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120592090368705955590018071 180888135553058933385027107)
    ·
      refine ⟨271332203329588400077540661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180888135553058933385027107 271332203329588400077540661)
      ·
        refine ⟨25437394062148912507269437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 271332203329588400077540661 25437394062148912507269437)
        ·
          refine ⟨9539022773305842190226039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25437394062148912507269437 9539022773305842190226039)
          ·
            refine ⟨14308534159958763285339059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9539022773305842190226039 14308534159958763285339059)
            ·
              refine ⟨21462801239938144928008589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14308534159958763285339059 21462801239938144928008589)
              ·
                refine ⟨8048550464976804348003221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21462801239938144928008589 8048550464976804348003221)
                ·
                  refine ⟨377275803045787703812651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8048550464976804348003221 377275803045787703812651)
                  ·
                    rfl

theorem cell22_3306339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 3, 6].length) (baseStart_3306339 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3306339 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3306339 prefixEnd_3306339 := by exact prefixLift 3306339
  have htrace : WordTrace (prefixWord ++ tailWord_3306339) baseStart_3306339 baseEnd_3306339 := by
    simpa [prefixWord, tailWord_3306339, baseEnd_3306339] using wordTrace_append hprefix tailTrace_3306339
  have hstable : (prefixWord ++ tailWord_3306339).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3306339).length < 2 ^ (prefixWord ++ tailWord_3306339).sum := by decide
  have hdescent : baseEnd_3306339 < baseStart_3306339 := by decide
  rcases family_descends (prefixWord ++ tailWord_3306339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3306358 : List Nat := [5, 1, 1, 3, 1, 1, 1, 4, 1, 4]
def baseStart_3306358 : Nat := 118140960795 + 3306358 * 2 ^ 59
def prefixEnd_3306358 : Nat := 4983230072969 + 3 ^ 40 * 3306358 * 2
def baseEnd_3306358 : Nat := 1131833913225653395212895

theorem tailTrace_3306358 : CollatzResearch.WordTrace tailWord_3306358 prefixEnd_3306358 1131833913225653395212895 := by
  unfold tailWord_3306358
  simp only [CollatzResearch.WordTrace]
  refine ⟨7537048959727320114684983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 80395188903758081223306485 7537048959727320114684983)
  ·
    refine ⟨11305573439590980172027475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7537048959727320114684983 11305573439590980172027475)
    ·
      refine ⟨16958360159386470258041213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11305573439590980172027475 16958360159386470258041213)
      ·
        refine ⟨6359385059769926346765455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16958360159386470258041213 6359385059769926346765455)
        ·
          refine ⟨9539077589654889520148183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6359385059769926346765455 9539077589654889520148183)
          ·
            refine ⟨14308616384482334280222275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9539077589654889520148183 14308616384482334280222275)
            ·
              refine ⟨21462924576723501420333413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14308616384482334280222275 21462924576723501420333413)
              ·
                refine ⟨4024298358135656516312515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21462924576723501420333413 4024298358135656516312515)
                ·
                  refine ⟨6036447537203484774468773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4024298358135656516312515 6036447537203484774468773)
                  ·
                    refine ⟨1131833913225653395212895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6036447537203484774468773 1131833913225653395212895)
                    ·
                      rfl

theorem cell22_3306358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 4, 1, 4].length) (baseStart_3306358 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3306358 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3306358 prefixEnd_3306358 := by exact prefixLift 3306358
  have htrace : WordTrace (prefixWord ++ tailWord_3306358) baseStart_3306358 baseEnd_3306358 := by
    simpa [prefixWord, tailWord_3306358, baseEnd_3306358] using wordTrace_append hprefix tailTrace_3306358
  have hstable : (prefixWord ++ tailWord_3306358).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3306358).length < 2 ^ (prefixWord ++ tailWord_3306358).sum := by decide
  have hdescent : baseEnd_3306358 < baseStart_3306358 := by decide
  rcases family_descends (prefixWord ++ tailWord_3306358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3306373 : List Nat := [1, 3, 1, 1, 3, 5, 1, 3, 4]
def baseStart_3306373 : Nat := 118140960795 + 3306373 * 2 ^ 59
def prefixEnd_3306373 : Nat := 4983230072969 + 3 ^ 40 * 3306373 * 2
def baseEnd_3306373 : Nat := 377279682677399452029283

theorem tailTrace_3306373 : CollatzResearch.WordTrace tailWord_3306373 prefixEnd_3306373 377279682677399452029283 := by
  unfold tailWord_3306373
  simp only [CollatzResearch.WordTrace]
  refine ⟨120593330450582779396755773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80395553633721852931170515 120593330450582779396755773)
  ·
    refine ⟨45222498918968542273783415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120593330450582779396755773 45222498918968542273783415)
    ·
      refine ⟨67833748378452813410675123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45222498918968542273783415 67833748378452813410675123)
      ·
        refine ⟨101750622567679220116012685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67833748378452813410675123 101750622567679220116012685)
        ·
          refine ⟨38156483462879707543504757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101750622567679220116012685 38156483462879707543504757)
          ·
            refine ⟨3577170324644972582203571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 38156483462879707543504757 3577170324644972582203571)
            ·
              refine ⟨5365755486967458873305357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3577170324644972582203571 5365755486967458873305357)
              ·
                refine ⟨2012158307612797077489509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5365755486967458873305357 2012158307612797077489509)
                ·
                  refine ⟨377279682677399452029283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2012158307612797077489509 377279682677399452029283)
                  ·
                    rfl

theorem cell22_3306373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 1, 3, 4].length) (baseStart_3306373 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3306373 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3306373 prefixEnd_3306373 := by exact prefixLift 3306373
  have htrace : WordTrace (prefixWord ++ tailWord_3306373) baseStart_3306373 baseEnd_3306373 := by
    simpa [prefixWord, tailWord_3306373, baseEnd_3306373] using wordTrace_append hprefix tailTrace_3306373
  have hstable : (prefixWord ++ tailWord_3306373).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3306373).length < 2 ^ (prefixWord ++ tailWord_3306373).sum := by decide
  have hdescent : baseEnd_3306373 < baseStart_3306373 := by decide
  rcases family_descends (prefixWord ++ tailWord_3306373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3306388 : List Nat := [2, 4, 2, 1, 1, 1, 2, 4, 2, 3]
def baseStart_3306388 : Nat := 118140960795 + 3306388 * 2 ^ 59
def prefixEnd_3306388 : Nat := 4983230072969 + 3 ^ 40 * 3306388 * 2
def baseEnd_3306388 : Nat := 1131844182838743316962803

theorem tailTrace_3306388 : CollatzResearch.WordTrace tailWord_3306388 prefixEnd_3306388 1131844182838743316962803 := by
  unfold tailWord_3306388
  simp only [CollatzResearch.WordTrace]
  refine ⟨60296938772764218479275909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80395918363685624639034545 60296938772764218479275909)
  ·
    refine ⟨11305676019893290964864233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60296938772764218479275909 11305676019893290964864233)
    ·
      refine ⟨8479257014919968223648175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11305676019893290964864233 8479257014919968223648175)
      ·
        refine ⟨12718885522379952335472263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8479257014919968223648175 12718885522379952335472263)
        ·
          refine ⟨19078328283569928503208395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12718885522379952335472263 19078328283569928503208395)
          ·
            refine ⟨28617492425354892754812593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19078328283569928503208395 28617492425354892754812593)
            ·
              refine ⟨21463119319016169566109445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28617492425354892754812593 21463119319016169566109445)
              ·
                refine ⟨4024334872315531793645521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21463119319016169566109445 4024334872315531793645521)
                ·
                  refine ⟨3018251154236648845234141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4024334872315531793645521 3018251154236648845234141)
                  ·
                    refine ⟨1131844182838743316962803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3018251154236648845234141 1131844182838743316962803)
                    ·
                      rfl

theorem cell22_3306388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 4, 2, 3].length) (baseStart_3306388 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3306388 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3306388 prefixEnd_3306388 := by exact prefixLift 3306388
  have htrace : WordTrace (prefixWord ++ tailWord_3306388) baseStart_3306388 baseEnd_3306388 := by
    simpa [prefixWord, tailWord_3306388, baseEnd_3306388] using wordTrace_append hprefix tailTrace_3306388
  have hstable : (prefixWord ++ tailWord_3306388).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3306388).length < 2 ^ (prefixWord ++ tailWord_3306388).sum := by decide
  have hdescent : baseEnd_3306388 < baseStart_3306388 := by decide
  rcases family_descends (prefixWord ++ tailWord_3306388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3306390 : List Nat := [5, 3, 1, 1, 1, 1, 3, 1, 6]
def baseStart_3306390 : Nat := 118140960795 + 3306390 * 2 ^ 59
def prefixEnd_3306390 : Nat := 4983230072969 + 3 ^ 40 * 3306390 * 2
def baseEnd_3306390 : Nat := 377281622493205326137599

theorem tailTrace_3306390 : CollatzResearch.WordTrace tailWord_3306390 prefixEnd_3306390 377281622493205326137599 := by
  unfold tailWord_3306390
  simp only [CollatzResearch.WordTrace]
  refine ⟨7537121905720074456257789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 80395966994347460866749749 7537121905720074456257789)
  ·
    refine ⟨2826420714645027921096671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7537121905720074456257789 2826420714645027921096671)
    ·
      refine ⟨4239631071967541881645007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2826420714645027921096671 4239631071967541881645007)
      ·
        refine ⟨6359446607951312822467511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4239631071967541881645007 6359446607951312822467511)
        ·
          refine ⟨9539169911926969233701267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6359446607951312822467511 9539169911926969233701267)
          ·
            refine ⟨14308754867890453850551901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9539169911926969233701267 14308754867890453850551901)
            ·
              refine ⟨5365783075458920193956963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14308754867890453850551901 5365783075458920193956963)
              ·
                refine ⟨8048674613188380290935445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5365783075458920193956963 8048674613188380290935445)
                ·
                  refine ⟨377281622493205326137599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8048674613188380290935445 377281622493205326137599)
                  ·
                    rfl

theorem cell22_3306390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 3, 1, 6].length) (baseStart_3306390 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3306390 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3306390 prefixEnd_3306390 := by exact prefixLift 3306390
  have htrace : WordTrace (prefixWord ++ tailWord_3306390) baseStart_3306390 baseEnd_3306390 := by
    simpa [prefixWord, tailWord_3306390, baseEnd_3306390] using wordTrace_append hprefix tailTrace_3306390
  have hstable : (prefixWord ++ tailWord_3306390).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3306390).length < 2 ^ (prefixWord ++ tailWord_3306390).sum := by decide
  have hdescent : baseEnd_3306390 < baseStart_3306390 := by decide
  rcases family_descends (prefixWord ++ tailWord_3306390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3306401 : List Nat := [1, 2, 3, 4, 1, 2, 2, 7]
def baseStart_3306401 : Nat := 118140960795 + 3306401 * 2 ^ 59
def prefixEnd_3306401 : Nat := 4983230072969 + 3 ^ 40 * 3306401 * 2
def baseEnd_3306401 : Nat := 125760959222712846265307

theorem tailTrace_3306401 : CollatzResearch.WordTrace tailWord_3306401 prefixEnd_3306401 125760959222712846265307 := by
  unfold tailWord_3306401
  simp only [CollatzResearch.WordTrace]
  refine ⟨120594351694481340178775057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80396234462987560119183371 120594351694481340178775057)
  ·
    refine ⟨90445763770861005134081293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120594351694481340178775057 90445763770861005134081293)
    ·
      refine ⟨33917161414072876925280485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90445763770861005134081293 33917161414072876925280485)
      ·
        refine ⟨6359467765138664423490091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33917161414072876925280485 6359467765138664423490091)
        ·
          refine ⟨9539201647707996635235137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6359467765138664423490091 9539201647707996635235137)
          ·
            refine ⟨7154401235780997476426353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9539201647707996635235137 7154401235780997476426353)
            ·
              refine ⟨5365800926835748107319765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7154401235780997476426353 5365800926835748107319765)
              ·
                refine ⟨125760959222712846265307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5365800926835748107319765 125760959222712846265307)
                ·
                  rfl

theorem cell22_3306401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 2, 7].length) (baseStart_3306401 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3306401 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3306401 prefixEnd_3306401 := by exact prefixLift 3306401
  have htrace : WordTrace (prefixWord ++ tailWord_3306401) baseStart_3306401 baseEnd_3306401 := by
    simpa [prefixWord, tailWord_3306401, baseEnd_3306401] using wordTrace_append hprefix tailTrace_3306401
  have hstable : (prefixWord ++ tailWord_3306401).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3306401).length < 2 ^ (prefixWord ++ tailWord_3306401).sum := by decide
  have hdescent : baseEnd_3306401 < baseStart_3306401 := by decide
  rcases family_descends (prefixWord ++ tailWord_3306401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3306420 : List Nat := [2, 5, 2, 1, 1, 2, 2, 1, 2, 4]
def baseStart_3306420 : Nat := 118140960795 + 3306420 * 2 ^ 59
def prefixEnd_3306420 : Nat := 4983230072969 + 3 ^ 40 * 3306420 * 2
def baseEnd_3306420 : Nat := 1131855137092705900162705

theorem tailTrace_3306420 : CollatzResearch.WordTrace tailWord_3306420 prefixEnd_3306420 1131855137092705900162705 := by
  unfold tailWord_3306420
  simp only [CollatzResearch.WordTrace]
  refine ⟨60297522340706253211858357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80396696454275004282477809 60297522340706253211858357)
  ·
    refine ⟨5652892719441211238611721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 60297522340706253211858357 5652892719441211238611721)
    ·
      refine ⟨4239669539580908428958791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5652892719441211238611721 4239669539580908428958791)
      ·
        refine ⟨6359504309371362643438187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4239669539580908428958791 6359504309371362643438187)
        ·
          refine ⟨9539256464057043965157281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6359504309371362643438187 9539256464057043965157281)
          ·
            refine ⟨7154442348042782973867961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9539256464057043965157281 7154442348042782973867961)
            ·
              refine ⟨5365831761032087230400971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7154442348042782973867961 5365831761032087230400971)
              ·
                refine ⟨8048747641548130845601457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5365831761032087230400971 8048747641548130845601457)
                ·
                  refine ⟨6036560731161098134201093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8048747641548130845601457 6036560731161098134201093)
                  ·
                    refine ⟨1131855137092705900162705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6036560731161098134201093 1131855137092705900162705)
                    ·
                      rfl

theorem cell22_3306420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_3306420 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3306420 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3306420 prefixEnd_3306420 := by exact prefixLift 3306420
  have htrace : WordTrace (prefixWord ++ tailWord_3306420) baseStart_3306420 baseEnd_3306420 := by
    simpa [prefixWord, tailWord_3306420, baseEnd_3306420] using wordTrace_append hprefix tailTrace_3306420
  have hstable : (prefixWord ++ tailWord_3306420).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3306420).length < 2 ^ (prefixWord ++ tailWord_3306420).sum := by decide
  have hdescent : baseEnd_3306420 < baseStart_3306420 := by decide
  rcases family_descends (prefixWord ++ tailWord_3306420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3306422 : List Nat := [5, 1, 4, 1, 1, 1, 1, 2, 1, 5]
def baseStart_3306422 : Nat := 118140960795 + 3306422 * 2 ^ 59
def prefixEnd_3306422 : Nat := 4983230072969 + 3 ^ 40 * 3306422 * 2
def baseEnd_3306422 : Nat := 1131855821733578561612699

theorem tailTrace_3306422 : CollatzResearch.WordTrace tailWord_3306422 prefixEnd_3306422 1131855821733578561612699 := by
  unfold tailWord_3306422
  simp only [CollatzResearch.WordTrace]
  refine ⟨7537194851712828797830595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 80396745084936840510193013 7537194851712828797830595)
  ·
    refine ⟨11305792277569243196745893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7537194851712828797830595 11305792277569243196745893)
    ·
      refine ⟨2119836052044233099389855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11305792277569243196745893 2119836052044233099389855)
      ·
        refine ⟨3179754078066349649084783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2119836052044233099389855 3179754078066349649084783)
        ·
          refine ⟨4769631117099524473627175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3179754078066349649084783 4769631117099524473627175)
          ·
            refine ⟨7154446675649286710440763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4769631117099524473627175 7154446675649286710440763)
            ·
              refine ⟨10731670013473930065661145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7154446675649286710440763 10731670013473930065661145)
              ·
                refine ⟨8048752510105447549245859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10731670013473930065661145 8048752510105447549245859)
                ·
                  refine ⟨12073128765158171323868789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8048752510105447549245859 12073128765158171323868789)
                  ·
                    refine ⟨1131855821733578561612699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12073128765158171323868789 1131855821733578561612699)
                    ·
                      rfl

theorem cell22_3306422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 1, 2, 1, 5].length) (baseStart_3306422 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3306422 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3306422 prefixEnd_3306422 := by exact prefixLift 3306422
  have htrace : WordTrace (prefixWord ++ tailWord_3306422) baseStart_3306422 baseEnd_3306422 := by
    simpa [prefixWord, tailWord_3306422, baseEnd_3306422] using wordTrace_append hprefix tailTrace_3306422
  have hstable : (prefixWord ++ tailWord_3306422).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3306422).length < 2 ^ (prefixWord ++ tailWord_3306422).sum := by decide
  have hdescent : baseEnd_3306422 < baseStart_3306422 := by decide
  rcases family_descends (prefixWord ++ tailWord_3306422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3306446 : List Nat := [4, 1, 1, 1, 2, 3, 1, 4, 5]
def baseStart_3306446 : Nat := 118140960795 + 3306446 * 2 ^ 59
def prefixEnd_3306446 : Nat := 4983230072969 + 3 ^ 40 * 3306446 * 2
def baseEnd_3306446 : Nat := 377288012474683499670875

theorem tailTrace_3306446 : CollatzResearch.WordTrace tailWord_3306446 prefixEnd_3306446 377288012474683499670875 := by
  unfold tailWord_3306446
  simp only [CollatzResearch.WordTrace]
  refine ⟨15074499122414789108020399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80397328652878875242775461 15074499122414789108020399)
  ·
    refine ⟨22611748683622183662030599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15074499122414789108020399 22611748683622183662030599)
    ·
      refine ⟨33917623025433275493045899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22611748683622183662030599 33917623025433275493045899)
      ·
        refine ⟨50876434538149913239568849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33917623025433275493045899 50876434538149913239568849)
        ·
          refine ⟨38157325903612434929676637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50876434538149913239568849 38157325903612434929676637)
          ·
            refine ⟨14308997213854663098628739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38157325903612434929676637 14308997213854663098628739)
            ·
              refine ⟨21463495820781994647943109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14308997213854663098628739 21463495820781994647943109)
              ·
                refine ⟨4024405466396623996489333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21463495820781994647943109 4024405466396623996489333)
                ·
                  refine ⟨377288012474683499670875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4024405466396623996489333 377288012474683499670875)
                  ·
                    rfl

theorem cell22_3306446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 4, 5].length) (baseStart_3306446 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3306446 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3306446 prefixEnd_3306446 := by exact prefixLift 3306446
  have htrace : WordTrace (prefixWord ++ tailWord_3306446) baseStart_3306446 baseEnd_3306446 := by
    simpa [prefixWord, tailWord_3306446, baseEnd_3306446] using wordTrace_append hprefix tailTrace_3306446
  have hstable : (prefixWord ++ tailWord_3306446).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3306446).length < 2 ^ (prefixWord ++ tailWord_3306446).sum := by decide
  have hdescent : baseEnd_3306446 < baseStart_3306446 := by decide
  rcases family_descends (prefixWord ++ tailWord_3306446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3306461 : List Nat := [1, 4, 3, 1, 2, 1, 1, 1, 1, 7]
def baseStart_3306461 : Nat := 118140960795 + 3306461 * 2 ^ 59
def prefixEnd_3306461 : Nat := 4983230072969 + 3 ^ 40 * 3306461 * 2
def baseEnd_3306461 : Nat := 1131869172230595459887579

theorem tailTrace_3306461 : CollatzResearch.WordTrace tailWord_3306461 prefixEnd_3306461 1131869172230595459887579 := by
  unfold tailWord_3306461
  simp only [CollatzResearch.WordTrace]
  refine ⟨120596540074263970425959237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80397693382842646950639491 120596540074263970425959237)
  ·
    refine ⟨22611851263924494454867357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 120596540074263970425959237 22611851263924494454867357)
    ·
      refine ⟨8479444223971685420575259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22611851263924494454867357 8479444223971685420575259)
      ·
        refine ⟨12719166335957528130862889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8479444223971685420575259 12719166335957528130862889)
        ·
          refine ⟨9539374751968146098147167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12719166335957528130862889 9539374751968146098147167)
          ·
            refine ⟨14309062127952219147220751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9539374751968146098147167 14309062127952219147220751)
            ·
              refine ⟨21463593191928328720831127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14309062127952219147220751 21463593191928328720831127)
              ·
                refine ⟨32195389787892493081246691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21463593191928328720831127 32195389787892493081246691)
                ·
                  refine ⟨48293084681838739621870037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32195389787892493081246691 48293084681838739621870037)
                  ·
                    refine ⟨1131869172230595459887579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48293084681838739621870037 1131869172230595459887579)
                    ·
                      rfl

theorem cell22_3306461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 1, 1, 7].length) (baseStart_3306461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3306461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3306461 prefixEnd_3306461 := by exact prefixLift 3306461
  have htrace : WordTrace (prefixWord ++ tailWord_3306461) baseStart_3306461 baseEnd_3306461 := by
    simpa [prefixWord, tailWord_3306461, baseEnd_3306461] using wordTrace_append hprefix tailTrace_3306461
  have hstable : (prefixWord ++ tailWord_3306461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3306461).length < 2 ^ (prefixWord ++ tailWord_3306461).sum := by decide
  have hdescent : baseEnd_3306461 < baseStart_3306461 := by decide
  rcases family_descends (prefixWord ++ tailWord_3306461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3306508 : List Nat := [2, 2, 1, 2, 3, 2, 2, 4, 4]
def baseStart_3306508 : Nat := 118140960795 + 3306508 * 2 ^ 59
def prefixEnd_3306508 : Nat := 4983230072969 + 3 ^ 40 * 3306508 * 2
def baseEnd_3306508 : Nat := 377295087097034334654145

theorem tailTrace_3306508 : CollatzResearch.WordTrace tailWord_3306508 prefixEnd_3306508 377295087097034334654145 := by
  unfold tailWord_3306508
  simp only [CollatzResearch.WordTrace]
  refine ⟨60299127152546848726460089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80398836203395798301946785 60299127152546848726460089)
  ·
    refine ⟨45224345364410136544845067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60299127152546848726460089 45224345364410136544845067)
    ·
      refine ⟨67836518046615204817267601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45224345364410136544845067 67836518046615204817267601)
      ·
        refine ⟨50877388534961403612950701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67836518046615204817267601 50877388534961403612950701)
        ·
          refine ⟨19079020700610526354856513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50877388534961403612950701 19079020700610526354856513)
          ·
            refine ⟨14309265525457894766142385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19079020700610526354856513 14309265525457894766142385)
            ·
              refine ⟨10731949144093421074606789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14309265525457894766142385 10731949144093421074606789)
              ·
                refine ⟨2012240464517516451488773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10731949144093421074606789 2012240464517516451488773)
                ·
                  refine ⟨377295087097034334654145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2012240464517516451488773 377295087097034334654145)
                  ·
                    rfl

theorem cell22_3306508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2, 4, 4].length) (baseStart_3306508 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3306508 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3306508 prefixEnd_3306508 := by exact prefixLift 3306508
  have htrace : WordTrace (prefixWord ++ tailWord_3306508) baseStart_3306508 baseEnd_3306508 := by
    simpa [prefixWord, tailWord_3306508, baseEnd_3306508] using wordTrace_append hprefix tailTrace_3306508
  have hstable : (prefixWord ++ tailWord_3306508).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3306508).length < 2 ^ (prefixWord ++ tailWord_3306508).sum := by decide
  have hdescent : baseEnd_3306508 < baseStart_3306508 := by decide
  rcases family_descends (prefixWord ++ tailWord_3306508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3306514 : List Nat := [3, 2, 5, 1, 1, 1, 3, 1, 5]
def baseStart_3306514 : Nat := 118140960795 + 3306514 * 2 ^ 59
def prefixEnd_3306514 : Nat := 4983230072969 + 3 ^ 40 * 3306514 * 2
def baseEnd_3306514 : Nat := 377295771737906996104139

theorem tailTrace_3306514 : CollatzResearch.WordTrace tailWord_3306514 prefixEnd_3306514 377295771737906996104139 := by
  unfold tailWord_3306514
  simp only [CollatzResearch.WordTrace]
  refine ⟨30149618285767990119409649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80398982095381306985092397 30149618285767990119409649)
  ·
    refine ⟨22612213714325992589557237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30149618285767990119409649 22612213714325992589557237)
    ·
      refine ⟨2119895035718061805270991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22612213714325992589557237 2119895035718061805270991)
      ·
        refine ⟨3179842553577092707906487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2119895035718061805270991 3179842553577092707906487)
        ·
          refine ⟨4769763830365639061859731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3179842553577092707906487 4769763830365639061859731)
          ·
            refine ⟨7154645745548458592789597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4769763830365639061859731 7154645745548458592789597)
            ·
              refine ⟨2682992154580671972296099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7154645745548458592789597 2682992154580671972296099)
              ·
                refine ⟨4024488231871007958444149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2682992154580671972296099 4024488231871007958444149)
                ·
                  refine ⟨377295771737906996104139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4024488231871007958444149 377295771737906996104139)
                  ·
                    rfl

theorem cell22_3306514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 3, 1, 5].length) (baseStart_3306514 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3306514 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3306514 prefixEnd_3306514 := by exact prefixLift 3306514
  have htrace : WordTrace (prefixWord ++ tailWord_3306514) baseStart_3306514 baseEnd_3306514 := by
    simpa [prefixWord, tailWord_3306514, baseEnd_3306514] using wordTrace_append hprefix tailTrace_3306514
  have hstable : (prefixWord ++ tailWord_3306514).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3306514).length < 2 ^ (prefixWord ++ tailWord_3306514).sum := by decide
  have hdescent : baseEnd_3306514 < baseStart_3306514 := by decide
  rcases family_descends (prefixWord ++ tailWord_3306514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3306596 : List Nat := [2, 3, 1, 1, 2, 1, 1, 2, 4, 5]
def baseStart_3306596 : Nat := 118140960795 + 3306596 * 2 ^ 59
def prefixEnd_3306596 : Nat := 4983230072969 + 3 ^ 40 * 3306596 * 2
def baseEnd_3306596 : Nat := 1131915385489500107762165

theorem tailTrace_3306596 : CollatzResearch.WordTrace tailWord_3306596 prefixEnd_3306596 1131915385489500107762165 := by
  unfold tailWord_3306596
  simp only [CollatzResearch.WordTrace]
  refine ⟨60300731964387444241061821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80400975952516592321415761 60300731964387444241061821)
  ·
    refine ⟨22612774486645291590398183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60300731964387444241061821 22612774486645291590398183)
    ·
      refine ⟨33919161729967937385597275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22612774486645291590398183 33919161729967937385597275)
      ·
        refine ⟨50878742594951906078395913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33919161729967937385597275 50878742594951906078395913)
        ·
          refine ⟨38159056946213929558796935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50878742594951906078395913 38159056946213929558796935)
          ·
            refine ⟨57238585419320894338195403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38159056946213929558796935 57238585419320894338195403)
            ·
              refine ⟨85857878128981341507293105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57238585419320894338195403 85857878128981341507293105)
              ·
                refine ⟨64393408596736006130469829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85857878128981341507293105 64393408596736006130469829)
                ·
                  refine ⟨12073764111888001149463093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 64393408596736006130469829 12073764111888001149463093)
                  ·
                    refine ⟨1131915385489500107762165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12073764111888001149463093 1131915385489500107762165)
                    ·
                      rfl

theorem cell22_3306596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 2, 4, 5].length) (baseStart_3306596 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3306596 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3306596 prefixEnd_3306596 := by exact prefixLift 3306596
  have htrace : WordTrace (prefixWord ++ tailWord_3306596) baseStart_3306596 baseEnd_3306596 := by
    simpa [prefixWord, tailWord_3306596, baseEnd_3306596] using wordTrace_append hprefix tailTrace_3306596
  have hstable : (prefixWord ++ tailWord_3306596).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3306596).length < 2 ^ (prefixWord ++ tailWord_3306596).sum := by decide
  have hdescent : baseEnd_3306596 < baseStart_3306596 := by decide
  rcases family_descends (prefixWord ++ tailWord_3306596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3306628 : List Nat := [2, 3, 2, 1, 2, 2, 1, 2, 3, 4]
def baseStart_3306628 : Nat := 118140960795 + 3306628 * 2 ^ 59
def prefixEnd_3306628 : Nat := 4983230072969 + 3 ^ 40 * 3306628 * 2
def baseEnd_3306628 : Nat := 1131926339743462690962067

theorem tailTrace_3306628 : CollatzResearch.WordTrace tailWord_3306628 prefixEnd_3306628 1131926339743462690962067 := by
  unfold tailWord_3306628
  simp only [CollatzResearch.WordTrace]
  refine ⟨60301315532329478973644269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80401754043105971964859025 60301315532329478973644269)
  ·
    refine ⟨22612993324623554615116601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60301315532329478973644269 22612993324623554615116601)
    ·
      refine ⟨16959744993467665961337451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22612993324623554615116601 16959744993467665961337451)
      ·
        refine ⟨25439617490201498942006177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16959744993467665961337451 25439617490201498942006177)
        ·
          refine ⟨19079713117651124206504633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25439617490201498942006177 19079713117651124206504633)
          ·
            refine ⟨14309784838238343154878475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19079713117651124206504633 14309784838238343154878475)
            ·
              refine ⟨21464677257357514732317713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14309784838238343154878475 21464677257357514732317713)
              ·
                refine ⟨16098507943018136049238285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21464677257357514732317713 16098507943018136049238285)
                ·
                  refine ⟨6036940478631801018464357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16098507943018136049238285 6036940478631801018464357)
                  ·
                    refine ⟨1131926339743462690962067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6036940478631801018464357 1131926339743462690962067)
                    ·
                      rfl

theorem cell22_3306628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 2, 3, 4].length) (baseStart_3306628 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3306628 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3306628 prefixEnd_3306628 := by exact prefixLift 3306628
  have htrace : WordTrace (prefixWord ++ tailWord_3306628) baseStart_3306628 baseEnd_3306628 := by
    simpa [prefixWord, tailWord_3306628, baseEnd_3306628] using wordTrace_append hprefix tailTrace_3306628
  have hstable : (prefixWord ++ tailWord_3306628).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3306628).length < 2 ^ (prefixWord ++ tailWord_3306628).sum := by decide
  have hdescent : baseEnd_3306628 < baseStart_3306628 := by decide
  rcases family_descends (prefixWord ++ tailWord_3306628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3306660 : List Nat := [2, 3, 1, 2, 3, 1, 1, 5, 4]
def baseStart_3306660 : Nat := 118140960795 + 3306660 * 2 ^ 59
def prefixEnd_3306660 : Nat := 4983230072969 + 3 ^ 40 * 3306660 * 2
def baseEnd_3306660 : Nat := 377312431332475091387323

theorem tailTrace_3306660 : CollatzResearch.WordTrace tailWord_3306660 prefixEnd_3306660 377312431332475091387323 := by
  unfold tailWord_3306660
  simp only [CollatzResearch.WordTrace]
  refine ⟨60301899100271513706226717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80402532133695351608302289 60301899100271513706226717)
  ·
    refine ⟨22613212162601817639835019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60301899100271513706226717 22613212162601817639835019)
    ·
      refine ⟨33919818243902726459752529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22613212162601817639835019 33919818243902726459752529)
      ·
        refine ⟨25439863682927044844814397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33919818243902726459752529 25439863682927044844814397)
        ·
          refine ⟨9539948881097641816805399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25439863682927044844814397 9539948881097641816805399)
          ·
            refine ⟨14309923321646462725208099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9539948881097641816805399 14309923321646462725208099)
            ·
              refine ⟨21464884982469694087812149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14309923321646462725208099 21464884982469694087812149)
              ·
                refine ⟨2012332967106533820732389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21464884982469694087812149 2012332967106533820732389)
                ·
                  refine ⟨377312431332475091387323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2012332967106533820732389 377312431332475091387323)
                  ·
                    rfl

theorem cell22_3306660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 5, 4].length) (baseStart_3306660 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3306660 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3306660 prefixEnd_3306660 := by exact prefixLift 3306660
  have htrace : WordTrace (prefixWord ++ tailWord_3306660) baseStart_3306660 baseEnd_3306660 := by
    simpa [prefixWord, tailWord_3306660, baseEnd_3306660] using wordTrace_append hprefix tailTrace_3306660
  have hstable : (prefixWord ++ tailWord_3306660).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3306660).length < 2 ^ (prefixWord ++ tailWord_3306660).sum := by decide
  have hdescent : baseEnd_3306660 < baseStart_3306660 := by decide
  rcases family_descends (prefixWord ++ tailWord_3306660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3306675 : List Nat := [1, 1, 1, 2, 3, 2, 5, 2, 2, 3]
def baseStart_3306675 : Nat := 118140960795 + 3306675 * 2 ^ 59
def prefixEnd_3306675 : Nat := 4983230072969 + 3 ^ 40 * 3306675 * 2
def baseEnd_3306675 : Nat := 1131942428803970235036923

theorem tailTrace_3306675 : CollatzResearch.WordTrace tailWord_3306675 prefixEnd_3306675 1131942428803970235036923 := by
  unfold tailWord_3306675
  simp only [CollatzResearch.WordTrace]
  refine ⟨120604345295488684974249479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80402896863659123316166319 120604345295488684974249479)
  ·
    refine ⟨180906517943233027461374219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120604345295488684974249479 180906517943233027461374219)
    ·
      refine ⟨271359776914849541192061329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180906517943233027461374219 271359776914849541192061329)
      ·
        refine ⟨203519832686137155894045997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 271359776914849541192061329 203519832686137155894045997)
        ·
          refine ⟨76319937257301433460267249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 203519832686137155894045997 76319937257301433460267249)
          ·
            refine ⟨57239952942976075095200437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76319937257301433460267249 57239952942976075095200437)
            ·
              refine ⟨5366245588404007040175041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 57239952942976075095200437 5366245588404007040175041)
              ·
                refine ⟨4024684191303005280131281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5366245588404007040175041 4024684191303005280131281)
                ·
                  refine ⟨3018513143477253960098461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4024684191303005280131281 3018513143477253960098461)
                  ·
                    refine ⟨1131942428803970235036923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3018513143477253960098461 1131942428803970235036923)
                    ·
                      rfl

theorem cell22_3306675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 5, 2, 2, 3].length) (baseStart_3306675 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3306675 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3306675 prefixEnd_3306675 := by exact prefixLift 3306675
  have htrace : WordTrace (prefixWord ++ tailWord_3306675) baseStart_3306675 baseEnd_3306675 := by
    simpa [prefixWord, tailWord_3306675, baseEnd_3306675] using wordTrace_append hprefix tailTrace_3306675
  have hstable : (prefixWord ++ tailWord_3306675).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3306675).length < 2 ^ (prefixWord ++ tailWord_3306675).sum := by decide
  have hdescent : baseEnd_3306675 < baseStart_3306675 := by decide
  rcases family_descends (prefixWord ++ tailWord_3306675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3306692 : List Nat := [2, 3, 3, 1, 3, 2, 1, 1, 1, 5]
def baseStart_3306692 : Nat := 118140960795 + 3306692 * 2 ^ 59
def prefixEnd_3306692 : Nat := 4983230072969 + 3 ^ 40 * 3306692 * 2
def baseEnd_3306692 : Nat := 1131948248251387857361871

theorem tailTrace_3306692 : CollatzResearch.WordTrace tailWord_3306692 prefixEnd_3306692 1131948248251387857361871 := by
  unfold tailWord_3306692
  simp only [CollatzResearch.WordTrace]
  refine ⟨60302482668213548438809165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80403310224284731251745553 60302482668213548438809165)
  ·
    refine ⟨22613431000580080664553437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60302482668213548438809165 22613431000580080664553437)
    ·
      refine ⟨8480036625217530249207539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22613431000580080664553437 8480036625217530249207539)
      ·
        refine ⟨12720054937826295373811309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8480036625217530249207539 12720054937826295373811309)
        ·
          refine ⟨4770020601684860765179241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12720054937826295373811309 4770020601684860765179241)
          ·
            refine ⟨3577515451263645573884431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4770020601684860765179241 3577515451263645573884431)
            ·
              refine ⟨5366273176895468360826647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3577515451263645573884431 5366273176895468360826647)
              ·
                refine ⟨8049409765343202541239971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5366273176895468360826647 8049409765343202541239971)
                ·
                  refine ⟨12074114648014803811859957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8049409765343202541239971 12074114648014803811859957)
                  ·
                    refine ⟨1131948248251387857361871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12074114648014803811859957 1131948248251387857361871)
                    ·
                      rfl

theorem cell22_3306692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 1, 1, 1, 5].length) (baseStart_3306692 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3306692 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3306692 prefixEnd_3306692 := by exact prefixLift 3306692
  have htrace : WordTrace (prefixWord ++ tailWord_3306692) baseStart_3306692 baseEnd_3306692 := by
    simpa [prefixWord, tailWord_3306692, baseEnd_3306692] using wordTrace_append hprefix tailTrace_3306692
  have hstable : (prefixWord ++ tailWord_3306692).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3306692).length < 2 ^ (prefixWord ++ tailWord_3306692).sum := by decide
  have hdescent : baseEnd_3306692 < baseStart_3306692 := by decide
  rcases family_descends (prefixWord ++ tailWord_3306692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3306703 : List Nat := [1, 1, 2, 1, 1, 3, 2, 3, 5, 3]
def baseStart_3306703 : Nat := 118140960795 + 3306703 * 2 ^ 59
def prefixEnd_3306703 : Nat := 4983230072969 + 3 ^ 40 * 3306703 * 2
def baseEnd_3306703 : Nat := 1131952013776187495336837

theorem tailTrace_3306703 : CollatzResearch.WordTrace tailWord_3306703 prefixEnd_3306703 1131952013776187495336837 := by
  unfold tailWord_3306703
  simp only [CollatzResearch.WordTrace]
  refine ⟨120605366539387245756268763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80403577692924830504179175 120605366539387245756268763)
  ·
    refine ⟨180908049809080868634403145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120605366539387245756268763 180908049809080868634403145)
    ·
      refine ⟨135681037356810651475802359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180908049809080868634403145 135681037356810651475802359)
      ·
        refine ⟨203521556035215977213703539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135681037356810651475802359 203521556035215977213703539)
        ·
          refine ⟨305282334052823965820555309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203521556035215977213703539 305282334052823965820555309)
          ·
            refine ⟨114480875269808987182708241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 305282334052823965820555309 114480875269808987182708241)
            ·
              refine ⟨85860656452356740387031181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114480875269808987182708241 85860656452356740387031181)
              ·
                refine ⟨32197746169633777645136693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 85860656452356740387031181 32197746169633777645136693)
                ·
                  refine ⟨3018538703403166654231565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32197746169633777645136693 3018538703403166654231565)
                  ·
                    refine ⟨1131952013776187495336837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3018538703403166654231565 1131952013776187495336837)
                    ·
                      rfl

theorem cell22_3306703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 3, 5, 3].length) (baseStart_3306703 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3306703 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3306703 prefixEnd_3306703 := by exact prefixLift 3306703
  have htrace : WordTrace (prefixWord ++ tailWord_3306703) baseStart_3306703 baseEnd_3306703 := by
    simpa [prefixWord, tailWord_3306703, baseEnd_3306703] using wordTrace_append hprefix tailTrace_3306703
  have hstable : (prefixWord ++ tailWord_3306703).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3306703).length < 2 ^ (prefixWord ++ tailWord_3306703).sum := by decide
  have hdescent : baseEnd_3306703 < baseStart_3306703 := by decide
  rcases family_descends (prefixWord ++ tailWord_3306703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3306780 : List Nat := [2, 2, 3, 1, 1, 1, 2, 5, 1, 4]
def baseStart_3306780 : Nat := 118140960795 + 3306780 * 2 ^ 59
def prefixEnd_3306780 : Nat := 4983230072969 + 3 ^ 40 * 3306780 * 2
def baseEnd_3306780 : Nat := 1131978372449784961161601

theorem tailTrace_3306780 : CollatzResearch.WordTrace tailWord_3306780 prefixEnd_3306780 1131978372449784961161601 := by
  unfold tailWord_3306780
  simp only [CollatzResearch.WordTrace]
  refine ⟨60304087480054143953410897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80405449973405525271214529 60304087480054143953410897)
  ·
    refine ⟨45228065610040607965058173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60304087480054143953410897 45228065610040607965058173)
    ·
      refine ⟨16960524603765227986896815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45228065610040607965058173 16960524603765227986896815)
      ·
        refine ⟨25440786905647841980345223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16960524603765227986896815 25440786905647841980345223)
        ·
          refine ⟨38161180358471762970517835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25440786905647841980345223 38161180358471762970517835)
          ·
            refine ⟨57241770537707644455776753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38161180358471762970517835 57241770537707644455776753)
            ·
              refine ⟨42931327903280733341832565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57241770537707644455776753 42931327903280733341832565)
              ·
                refine ⟨4024811990932568750796803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42931327903280733341832565 4024811990932568750796803)
                ·
                  refine ⟨6037217986398853126195205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4024811990932568750796803 6037217986398853126195205)
                  ·
                    refine ⟨1131978372449784961161601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6037217986398853126195205 1131978372449784961161601)
                    ·
                      rfl

theorem cell22_3306780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 5, 1, 4].length) (baseStart_3306780 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3306780 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3306780 prefixEnd_3306780 := by exact prefixLift 3306780
  have htrace : WordTrace (prefixWord ++ tailWord_3306780) baseStart_3306780 baseEnd_3306780 := by
    simpa [prefixWord, tailWord_3306780, baseEnd_3306780] using wordTrace_append hprefix tailTrace_3306780
  have hstable : (prefixWord ++ tailWord_3306780).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3306780).length < 2 ^ (prefixWord ++ tailWord_3306780).sum := by decide
  have hdescent : baseEnd_3306780 < baseStart_3306780 := by decide
  rcases family_descends (prefixWord ++ tailWord_3306780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3306797 : List Nat := [1, 5, 3, 1, 1, 1, 1, 2, 3, 4]
def baseStart_3306797 : Nat := 118140960795 + 3306797 * 2 ^ 59
def prefixEnd_3306797 : Nat := 4983230072969 + 3 ^ 40 * 3306797 * 2
def baseEnd_3306797 : Nat := 1131984191897202583486549

theorem tailTrace_3306797 : CollatzResearch.WordTrace tailWord_3306797 prefixEnd_3306797 1131984191897202583486549 := by
  unfold tailWord_3306797
  simp only [CollatzResearch.WordTrace]
  refine ⟨120608795001046699810190645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80405863334031133206793763 120608795001046699810190645)
  ·
    refine ⟨11307074531348128107205373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 120608795001046699810190645 11307074531348128107205373)
    ·
      refine ⟨4240152949255548040202015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11307074531348128107205373 4240152949255548040202015)
      ·
        refine ⟨6360229423883322060303023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4240152949255548040202015 6360229423883322060303023)
        ·
          refine ⟨9540344135824983090454535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6360229423883322060303023 9540344135824983090454535)
          ·
            refine ⟨14310516203737474635681803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9540344135824983090454535 14310516203737474635681803)
            ·
              refine ⟨21465774305606211953522705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14310516203737474635681803 21465774305606211953522705)
              ·
                refine ⟨16099330729204658965142029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21465774305606211953522705 16099330729204658965142029)
                ·
                  refine ⟨6037249023451747111928261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16099330729204658965142029 6037249023451747111928261)
                  ·
                    refine ⟨1131984191897202583486549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6037249023451747111928261 1131984191897202583486549)
                    ·
                      rfl

theorem cell22_3306797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_3306797 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3306797 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3306797 prefixEnd_3306797 := by exact prefixLift 3306797
  have htrace : WordTrace (prefixWord ++ tailWord_3306797) baseStart_3306797 baseEnd_3306797 := by
    simpa [prefixWord, tailWord_3306797, baseEnd_3306797] using wordTrace_append hprefix tailTrace_3306797
  have hstable : (prefixWord ++ tailWord_3306797).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3306797).length < 2 ^ (prefixWord ++ tailWord_3306797).sum := by decide
  have hdescent : baseEnd_3306797 < baseStart_3306797 := by decide
  rcases family_descends (prefixWord ++ tailWord_3306797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3306808 : List Nat := [2, 1, 2, 1, 3, 1, 1, 4, 1, 6]
def baseStart_3306808 : Nat := 118140960795 + 3306808 * 2 ^ 59
def prefixEnd_3306808 : Nat := 4983230072969 + 3 ^ 40 * 3306808 * 2
def baseEnd_3306808 : Nat := 1131987957422002221461515

theorem tailTrace_3306808 : CollatzResearch.WordTrace tailWord_3306808 prefixEnd_3306808 1131987957422002221461515 := by
  unfold tailWord_3306808
  simp only [CollatzResearch.WordTrace]
  refine ⟨60304598102003424344420539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80406130802671232459227385 60304598102003424344420539)
  ·
    refine ⟨90456897153005136516630809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60304598102003424344420539 90456897153005136516630809)
    ·
      refine ⟨67842672864753852387473107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90456897153005136516630809 67842672864753852387473107)
      ·
        refine ⟨101764009297130778581209661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67842672864753852387473107 101764009297130778581209661)
        ·
          refine ⟨38161503486424041967953623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101764009297130778581209661 38161503486424041967953623)
          ·
            refine ⟨57242255229636062951930435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38161503486424041967953623 57242255229636062951930435)
            ·
              refine ⟨85863382844454094427895653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57242255229636062951930435 85863382844454094427895653)
              ·
                refine ⟨16099384283335142705230435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 85863382844454094427895653 16099384283335142705230435)
                ·
                  refine ⟨24149076425002714057845653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16099384283335142705230435 24149076425002714057845653)
                  ·
                    refine ⟨1131987957422002221461515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24149076425002714057845653 1131987957422002221461515)
                    ·
                      rfl

theorem cell22_3306808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 4, 1, 6].length) (baseStart_3306808 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3306808 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3306808 prefixEnd_3306808 := by exact prefixLift 3306808
  have htrace : WordTrace (prefixWord ++ tailWord_3306808) baseStart_3306808 baseEnd_3306808 := by
    simpa [prefixWord, tailWord_3306808, baseEnd_3306808] using wordTrace_append hprefix tailTrace_3306808
  have hstable : (prefixWord ++ tailWord_3306808).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3306808).length < 2 ^ (prefixWord ++ tailWord_3306808).sum := by decide
  have hdescent : baseEnd_3306808 < baseStart_3306808 := by decide
  rcases family_descends (prefixWord ++ tailWord_3306808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3306810 : List Nat := [3, 1, 1, 1, 4, 1, 4, 1, 1, 5]
def baseStart_3306810 : Nat := 118140960795 + 3306810 * 2 ^ 59
def prefixEnd_3306810 : Nat := 4983230072969 + 3 ^ 40 * 3306810 * 2
def baseEnd_3306810 : Nat := 1131988642062874882911509

theorem tailTrace_3306810 : CollatzResearch.WordTrace tailWord_3306810 prefixEnd_3306810 1131988642062874882911509 := by
  unfold tailWord_3306810
  simp only [CollatzResearch.WordTrace]
  refine ⟨30152317287499900757603471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80406179433333068686942589 30152317287499900757603471)
  ·
    refine ⟨45228475931249851136405207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30152317287499900757603471 45228475931249851136405207)
    ·
      refine ⟨67842713896874776704607811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45228475931249851136405207 67842713896874776704607811)
      ·
        refine ⟨101764070845312165056911717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67842713896874776704607811 101764070845312165056911717)
        ·
          refine ⟨19080763283496030948170947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 101764070845312165056911717 19080763283496030948170947)
          ·
            refine ⟨28621144925244046422256421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19080763283496030948170947 28621144925244046422256421)
            ·
              refine ⟨5366464673483258704173079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28621144925244046422256421 5366464673483258704173079)
              ·
                refine ⟨8049697010224888056259619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5366464673483258704173079 8049697010224888056259619)
                ·
                  refine ⟨12074545515337332084389429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8049697010224888056259619 12074545515337332084389429)
                  ·
                    refine ⟨1131988642062874882911509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12074545515337332084389429 1131988642062874882911509)
                    ·
                      rfl

theorem cell22_3306810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 4, 1, 1, 5].length) (baseStart_3306810 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3306810 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3306810 prefixEnd_3306810 := by exact prefixLift 3306810
  have htrace : WordTrace (prefixWord ++ tailWord_3306810) baseStart_3306810 baseEnd_3306810 := by
    simpa [prefixWord, tailWord_3306810, baseEnd_3306810] using wordTrace_append hprefix tailTrace_3306810
  have hstable : (prefixWord ++ tailWord_3306810).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3306810).length < 2 ^ (prefixWord ++ tailWord_3306810).sum := by decide
  have hdescent : baseEnd_3306810 < baseStart_3306810 := by decide
  rcases family_descends (prefixWord ++ tailWord_3306810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3306825 : List Nat := [1, 2, 1, 1, 2, 3, 5, 1, 2, 4]
def baseStart_3306825 : Nat := 118140960795 + 3306825 * 2 ^ 59
def prefixEnd_3306825 : Nat := 4983230072969 + 3 ^ 40 * 3306825 * 2
def baseEnd_3306825 : Nat := 1131993776869419843786463

theorem tailTrace_3306825 : CollatzResearch.WordTrace tailWord_3306825 prefixEnd_3306825 1131993776869419843786463 := by
  unfold tailWord_3306825
  simp only [CollatzResearch.WordTrace]
  refine ⟨120609816244945260592209929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80406544163296840394806619 120609816244945260592209929)
  ·
    refine ⟨90457362183708945444157447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120609816244945260592209929 90457362183708945444157447)
    ·
      refine ⟨135686043275563418166236171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90457362183708945444157447 135686043275563418166236171)
      ·
        refine ⟨203529064913345127249354257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135686043275563418166236171 203529064913345127249354257)
        ·
          refine ⟨152646798685008845437015693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 203529064913345127249354257 152646798685008845437015693)
          ·
            refine ⟨57242549506878317038880885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 152646798685008845437015693 57242549506878317038880885)
            ·
              refine ⟨5366489016269842222395083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 57242549506878317038880885 5366489016269842222395083)
              ·
                refine ⟨8049733524404763333592625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5366489016269842222395083 8049733524404763333592625)
                ·
                  refine ⟨6037300143303572500194469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8049733524404763333592625 6037300143303572500194469)
                  ·
                    refine ⟨1131993776869419843786463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6037300143303572500194469 1131993776869419843786463)
                    ·
                      rfl

theorem cell22_3306825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 5, 1, 2, 4].length) (baseStart_3306825 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3306825 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3306825 prefixEnd_3306825 := by exact prefixLift 3306825
  have htrace : WordTrace (prefixWord ++ tailWord_3306825) baseStart_3306825 baseEnd_3306825 := by
    simpa [prefixWord, tailWord_3306825, baseEnd_3306825] using wordTrace_append hprefix tailTrace_3306825
  have hstable : (prefixWord ++ tailWord_3306825).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3306825).length < 2 ^ (prefixWord ++ tailWord_3306825).sum := by decide
  have hdescent : baseEnd_3306825 < baseStart_3306825 := by decide
  rcases family_descends (prefixWord ++ tailWord_3306825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3306906 : List Nat := [3, 1, 1, 4, 1, 1, 5, 2, 1, 3]
def baseStart_3306906 : Nat := 118140960795 + 3306906 * 2 ^ 59
def prefixEnd_3306906 : Nat := 4983230072969 + 3 ^ 40 * 3306906 * 2
def baseEnd_3306906 : Nat := 1132021504824762632511215

theorem tailTrace_3306906 : CollatzResearch.WordTrace tailWord_3306906 prefixEnd_3306906 1132021504824762632511215 := by
  unfold tailWord_3306906
  simp only [CollatzResearch.WordTrace]
  refine ⟨30153192639412952856477143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80408513705101207617272381 30153192639412952856477143)
  ·
    refine ⟨45229788959119429284715715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30153192639412952856477143 45229788959119429284715715)
    ·
      refine ⟨67844683438679143927073573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45229788959119429284715715 67844683438679143927073573)
      ·
        refine ⟨12720878144752339486326295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67844683438679143927073573 12720878144752339486326295)
        ·
          refine ⟨19081317217128509229489443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12720878144752339486326295 19081317217128509229489443)
          ·
            refine ⟨28621975825692763844234165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19081317217128509229489443 28621975825692763844234165)
            ·
              refine ⟨2683310233658696610396953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28621975825692763844234165 2683310233658696610396953)
              ·
                refine ⟨2012482675244022457797715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2683310233658696610396953 2012482675244022457797715)
                ·
                  refine ⟨3018724012866033686696573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2012482675244022457797715 3018724012866033686696573)
                  ·
                    refine ⟨1132021504824762632511215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3018724012866033686696573 1132021504824762632511215)
                    ·
                      rfl

theorem cell22_3306906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 5, 2, 1, 3].length) (baseStart_3306906 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3306906 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3306906 prefixEnd_3306906 := by exact prefixLift 3306906
  have htrace : WordTrace (prefixWord ++ tailWord_3306906) baseStart_3306906 baseEnd_3306906 := by
    simpa [prefixWord, tailWord_3306906, baseEnd_3306906] using wordTrace_append hprefix tailTrace_3306906
  have hstable : (prefixWord ++ tailWord_3306906).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3306906).length < 2 ^ (prefixWord ++ tailWord_3306906).sum := by decide
  have hdescent : baseEnd_3306906 < baseStart_3306906 := by decide
  rcases family_descends (prefixWord ++ tailWord_3306906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3306915 : List Nat := [1, 1, 1, 4, 1, 3, 2, 2, 3, 4]
def baseStart_3306915 : Nat := 118140960795 + 3306915 * 2 ^ 59
def prefixEnd_3306915 : Nat := 4983230072969 + 3 ^ 40 * 3306915 * 2
def baseEnd_3306915 : Nat := 1132024585708689609036187

theorem tailTrace_3306915 : CollatzResearch.WordTrace tailWord_3306915 prefixEnd_3306915 1132024585708689609036187 := by
  unfold tailWord_3306915
  simp only [CollatzResearch.WordTrace]
  refine ⟨120613098814619205962986199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80408732543079470641990799 120613098814619205962986199)
  ·
    refine ⟨180919648221928808944479299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120613098814619205962986199 180919648221928808944479299)
    ·
      refine ⟨271379472332893213416718949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180919648221928808944479299 271379472332893213416718949)
      ·
        refine ⟨50883651062417477515634803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 271379472332893213416718949 50883651062417477515634803)
        ·
          refine ⟨76325476593626216273452205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50883651062417477515634803 76325476593626216273452205)
          ·
            refine ⟨28622053722609831102544577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76325476593626216273452205 28622053722609831102544577)
            ·
              refine ⟨21466540291957373326908433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28622053722609831102544577 21466540291957373326908433)
              ·
                refine ⟨16099905218968029995181325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21466540291957373326908433 16099905218968029995181325)
                ·
                  refine ⟨6037464457113011248192997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16099905218968029995181325 6037464457113011248192997)
                  ·
                    refine ⟨1132024585708689609036187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6037464457113011248192997 1132024585708689609036187)
                    ·
                      rfl

theorem cell22_3306915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 2, 3, 4].length) (baseStart_3306915 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3306915 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3306915 prefixEnd_3306915 := by exact prefixLift 3306915
  have htrace : WordTrace (prefixWord ++ tailWord_3306915) baseStart_3306915 baseEnd_3306915 := by
    simpa [prefixWord, tailWord_3306915, baseEnd_3306915] using wordTrace_append hprefix tailTrace_3306915
  have hstable : (prefixWord ++ tailWord_3306915).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3306915).length < 2 ^ (prefixWord ++ tailWord_3306915).sum := by decide
  have hdescent : baseEnd_3306915 < baseStart_3306915 := by decide
  rcases family_descends (prefixWord ++ tailWord_3306915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3306979 : List Nat := [1, 1, 1, 6, 2, 1, 2, 3, 2, 3]
def baseStart_3306979 : Nat := 118140960795 + 3306979 * 2 ^ 59
def prefixEnd_3306979 : Nat := 4983230072969 + 3 ^ 40 * 3306979 * 2
def baseEnd_3306979 : Nat := 1132046494216614775435991

theorem tailTrace_3306979 : CollatzResearch.WordTrace tailWord_3306979 prefixEnd_3306979 1132046494216614775435991 := by
  unfold tailWord_3306979
  simp only [CollatzResearch.WordTrace]
  refine ⟨120615433086387344893315991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80410288724258229928877327 120615433086387344893315991)
  ·
    refine ⟨180923149629581017339973987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120615433086387344893315991 180923149629581017339973987)
    ·
      refine ⟨271384724444371526009960981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180923149629581017339973987 271384724444371526009960981)
      ·
        refine ⟨12721158958329915281716921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 271384724444371526009960981 12721158958329915281716921)
        ·
          refine ⟨9540869218747436461287691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12721158958329915281716921 9540869218747436461287691)
          ·
            refine ⟨14311303828121154691931537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9540869218747436461287691 14311303828121154691931537)
            ·
              refine ⟨10733477871090866018948653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14311303828121154691931537 10733477871090866018948653)
              ·
                refine ⟨4025054201659074757105745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10733477871090866018948653 4025054201659074757105745)
                ·
                  refine ⟨3018790651244306067829309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4025054201659074757105745 3018790651244306067829309)
                  ·
                    refine ⟨1132046494216614775435991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3018790651244306067829309 1132046494216614775435991)
                    ·
                      rfl

theorem cell22_3306979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 2, 3, 2, 3].length) (baseStart_3306979 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3306979 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3306979 prefixEnd_3306979 := by exact prefixLift 3306979
  have htrace : WordTrace (prefixWord ++ tailWord_3306979) baseStart_3306979 baseEnd_3306979 := by
    simpa [prefixWord, tailWord_3306979, baseEnd_3306979] using wordTrace_append hprefix tailTrace_3306979
  have hstable : (prefixWord ++ tailWord_3306979).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3306979).length < 2 ^ (prefixWord ++ tailWord_3306979).sum := by decide
  have hdescent : baseEnd_3306979 < baseStart_3306979 := by decide
  rcases family_descends (prefixWord ++ tailWord_3306979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3306992 : List Nat := [2, 1, 1, 1, 3, 5, 3, 6]
def baseStart_3306992 : Nat := 118140960795 + 3306992 * 2 ^ 59
def prefixEnd_3306992 : Nat := 4983230072969 + 3 ^ 40 * 3306992 * 2
def baseEnd_3306992 : Nat := 125783438264698563873439

theorem tailTrace_3306992 : CollatzResearch.WordTrace tailWord_3306992 prefixEnd_3306992 125783438264698563873439 := by
  unfold tailWord_3306992
  simp only [CollatzResearch.WordTrace]
  refine ⟨60307953617670124056769615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80410604823560165409026153 60307953617670124056769615)
  ·
    refine ⟨90461930426505186085154423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60307953617670124056769615 90461930426505186085154423)
    ·
      refine ⟨135692895639757779127731635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90461930426505186085154423 135692895639757779127731635)
      ·
        refine ⟨203539343459636668691597453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135692895639757779127731635 203539343459636668691597453)
        ·
          refine ⟨76327253797363750759349045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 203539343459636668691597453 76327253797363750759349045)
          ·
            refine ⟨7155680043502851633688973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 76327253797363750759349045 7155680043502851633688973)
            ·
              refine ⟨2683380016313569362633365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7155680043502851633688973 2683380016313569362633365)
              ·
                refine ⟨125783438264698563873439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2683380016313569362633365 125783438264698563873439)
                ·
                  rfl

theorem cell22_3306992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 3, 6].length) (baseStart_3306992 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3306992 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3306992 prefixEnd_3306992 := by exact prefixLift 3306992
  have htrace : WordTrace (prefixWord ++ tailWord_3306992) baseStart_3306992 baseEnd_3306992 := by
    simpa [prefixWord, tailWord_3306992, baseEnd_3306992] using wordTrace_append hprefix tailTrace_3306992
  have hstable : (prefixWord ++ tailWord_3306992).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3306992).length < 2 ^ (prefixWord ++ tailWord_3306992).sum := by decide
  have hdescent : baseEnd_3306992 < baseStart_3306992 := by decide
  rcases family_descends (prefixWord ++ tailWord_3306992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3306994 : List Nat := [3, 2, 1, 4, 1, 1, 3, 1, 2, 4]
def baseStart_3306994 : Nat := 118140960795 + 3306994 * 2 ^ 59
def prefixEnd_3306994 : Nat := 4983230072969 + 3 ^ 40 * 3306994 * 2
def baseEnd_3306994 : Nat := 1132051629023159736310945

theorem tailTrace_3306994 : CollatzResearch.WordTrace tailWord_3306994 prefixEnd_3306994 1132051629023159736310945 := by
  unfold tailWord_3306994
  simp only [CollatzResearch.WordTrace]
  refine ⟨30153995045333250613778009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80410653454222001636741357 30153995045333250613778009)
  ·
    refine ⟨22615496283999937960333507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30153995045333250613778009 22615496283999937960333507)
    ·
      refine ⟨33923244425999906940500261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22615496283999937960333507 33923244425999906940500261)
      ·
        refine ⟨6360608329874982551343799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33923244425999906940500261 6360608329874982551343799)
        ·
          refine ⟨9540912494812473827015699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6360608329874982551343799 9540912494812473827015699)
          ·
            refine ⟨14311368742218710740523549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9540912494812473827015699 14311368742218710740523549)
            ·
              refine ⟨5366763278332016527696331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14311368742218710740523549 5366763278332016527696331)
              ·
                refine ⟨8050144917498024791544497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5366763278332016527696331 8050144917498024791544497)
                ·
                  refine ⟨6037608688123518593658373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8050144917498024791544497 6037608688123518593658373)
                  ·
                    refine ⟨1132051629023159736310945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6037608688123518593658373 1132051629023159736310945)
                    ·
                      rfl

theorem cell22_3306994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 3, 1, 2, 4].length) (baseStart_3306994 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3306994 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3306994 prefixEnd_3306994 := by exact prefixLift 3306994
  have htrace : WordTrace (prefixWord ++ tailWord_3306994) baseStart_3306994 baseEnd_3306994 := by
    simpa [prefixWord, tailWord_3306994, baseEnd_3306994] using wordTrace_append hprefix tailTrace_3306994
  have hstable : (prefixWord ++ tailWord_3306994).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3306994).length < 2 ^ (prefixWord ++ tailWord_3306994).sum := by decide
  have hdescent : baseEnd_3306994 < baseStart_3306994 := by decide
  rcases family_descends (prefixWord ++ tailWord_3306994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3307114 : List Nat := [3, 1, 3, 2, 1, 3, 1, 2, 1, 5]
def baseStart_3307114 : Nat := 118140960795 + 3307114 * 2 ^ 59
def prefixEnd_3307114 : Nat := 4983230072969 + 3 ^ 40 * 3307114 * 2
def baseEnd_3307114 : Nat := 1132092707475519423310577

theorem tailTrace_3307114 : CollatzResearch.WordTrace tailWord_3307114 prefixEnd_3307114 1132092707475519423310577 := by
  unfold tailWord_3307114
  simp only [CollatzResearch.WordTrace]
  refine ⟨30155089235224565737370099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80413571293932175299653597 30155089235224565737370099)
  ·
    refine ⟨45232633852836848606055149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30155089235224565737370099 45232633852836848606055149)
    ·
      refine ⟨16962237694813818227270681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45232633852836848606055149 16962237694813818227270681)
      ·
        refine ⟨12721678271110363670453011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16962237694813818227270681 12721678271110363670453011)
        ·
          refine ⟨19082517406665545505679517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12721678271110363670453011 19082517406665545505679517)
          ·
            refine ⟨7155944027499579564629819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19082517406665545505679517 7155944027499579564629819)
            ·
              refine ⟨10733916041249369346944729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7155944027499579564629819 10733916041249369346944729)
              ·
                refine ⟨8050437030937027010208547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10733916041249369346944729 8050437030937027010208547)
                ·
                  refine ⟨12075655546405540515312821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8050437030937027010208547 12075655546405540515312821)
                  ·
                    refine ⟨1132092707475519423310577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12075655546405540515312821 1132092707475519423310577)
                    ·
                      rfl

theorem cell22_3307114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 1, 2, 1, 5].length) (baseStart_3307114 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3307114 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3307114 prefixEnd_3307114 := by exact prefixLift 3307114
  have htrace : WordTrace (prefixWord ++ tailWord_3307114) baseStart_3307114 baseEnd_3307114 := by
    simpa [prefixWord, tailWord_3307114, baseEnd_3307114] using wordTrace_append hprefix tailTrace_3307114
  have hstable : (prefixWord ++ tailWord_3307114).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3307114).length < 2 ^ (prefixWord ++ tailWord_3307114).sum := by decide
  have hdescent : baseEnd_3307114 < baseStart_3307114 := by decide
  rcases family_descends (prefixWord ++ tailWord_3307114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3307118 : List Nat := [4, 1, 2, 2, 3, 1, 3, 1, 1, 4]
def baseStart_3307118 : Nat := 118140960795 + 3307118 * 2 ^ 59
def prefixEnd_3307118 : Nat := 4983230072969 + 3 ^ 40 * 3307118 * 2
def baseEnd_3307118 : Nat := 1132094076757264746210565

theorem tailTrace_3307118 : CollatzResearch.WordTrace tailWord_3307118 prefixEnd_3307118 1132094076757264746210565 := by
  unfold tailWord_3307118
  simp only [CollatzResearch.WordTrace]
  refine ⟨15077562854110471454078251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80413668555255847755084005 15077562854110471454078251)
  ·
    refine ⟨22616344281165707181117377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15077562854110471454078251 22616344281165707181117377)
    ·
      refine ⟨16962258210874280385838033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22616344281165707181117377 16962258210874280385838033)
      ·
        refine ⟨12721693658155710289378525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16962258210874280385838033 12721693658155710289378525)
        ·
          refine ⟨4770635121808391358516947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12721693658155710289378525 4770635121808391358516947)
          ·
            refine ⟨7155952682712587037775421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4770635121808391358516947 7155952682712587037775421)
            ·
              refine ⟨2683482256017220139165783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7155952682712587037775421 2683482256017220139165783)
              ·
                refine ⟨4025223384025830208748675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2683482256017220139165783 4025223384025830208748675)
                ·
                  refine ⟨6037835076038745313123013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4025223384025830208748675 6037835076038745313123013)
                  ·
                    refine ⟨1132094076757264746210565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6037835076038745313123013 1132094076757264746210565)
                    ·
                      rfl

theorem cell22_3307118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 3, 1, 1, 4].length) (baseStart_3307118 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3307118 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3307118 prefixEnd_3307118 := by exact prefixLift 3307118
  have htrace : WordTrace (prefixWord ++ tailWord_3307118) baseStart_3307118 baseEnd_3307118 := by
    simpa [prefixWord, tailWord_3307118, baseEnd_3307118] using wordTrace_append hprefix tailTrace_3307118
  have hstable : (prefixWord ++ tailWord_3307118).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3307118).length < 2 ^ (prefixWord ++ tailWord_3307118).sum := by decide
  have hdescent : baseEnd_3307118 < baseStart_3307118 := by decide
  rcases family_descends (prefixWord ++ tailWord_3307118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3307133 : List Nat := [1, 4, 1, 1, 4, 3, 2, 2, 4]
def baseStart_3307133 : Nat := 118140960795 + 3307133 * 2 ^ 59
def prefixEnd_3307133 : Nat := 4983230072969 + 3 ^ 40 * 3307133 * 2
def baseEnd_3307133 : Nat := 377366403854603235695173

theorem tailTrace_3307133 : CollatzResearch.WordTrace tailWord_3307133 prefixEnd_3307133 377366403854603235695173 := by
  unfold tailWord_3307133
  simp only [CollatzResearch.WordTrace]
  refine ⟨120621049927829429194422053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80414033285219619462948035 120621049927829429194422053)
  ·
    refine ⟨22616446861468017973954135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 120621049927829429194422053 22616446861468017973954135)
    ·
      refine ⟨33924670292202026960931203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22616446861468017973954135 33924670292202026960931203)
      ·
        refine ⟨50887005438303040441396805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33924670292202026960931203 50887005438303040441396805)
        ·
          refine ⟨9541313519681820082761901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50887005438303040441396805 9541313519681820082761901)
          ·
            refine ⟨3577992569880682531035713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9541313519681820082761901 3577992569880682531035713)
            ·
              refine ⟨2683494427410511898276785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3577992569880682531035713 2683494427410511898276785)
              ·
                refine ⟨2012620820557883923707589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2683494427410511898276785 2012620820557883923707589)
                ·
                  refine ⟨377366403854603235695173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2012620820557883923707589 377366403854603235695173)
                  ·
                    rfl

theorem cell22_3307133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 2, 2, 4].length) (baseStart_3307133 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3307133 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3307133 prefixEnd_3307133 := by exact prefixLift 3307133
  have htrace : WordTrace (prefixWord ++ tailWord_3307133) baseStart_3307133 baseEnd_3307133 := by
    simpa [prefixWord, tailWord_3307133, baseEnd_3307133] using wordTrace_append hprefix tailTrace_3307133
  have hstable : (prefixWord ++ tailWord_3307133).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3307133).length < 2 ^ (prefixWord ++ tailWord_3307133).sum := by decide
  have hdescent : baseEnd_3307133 < baseStart_3307133 := by decide
  rcases family_descends (prefixWord ++ tailWord_3307133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3307159 : List Nat := [1, 1, 3, 3, 2, 2, 1, 1, 5, 3]
def baseStart_3307159 : Nat := 118140960795 + 3307159 * 2 ^ 59
def prefixEnd_3307159 : Nat := 4983230072969 + 3 ^ 40 * 3307159 * 2
def baseEnd_3307159 : Nat := 1132108111895154305935439

theorem tailTrace_3307159 : CollatzResearch.WordTrace tailWord_3307159 prefixEnd_3307159 1132108111895154305935439 := by
  unfold tailWord_3307159
  simp only [CollatzResearch.WordTrace]
  refine ⟨120621998225735235634868531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80414665483823490423245687 120621998225735235634868531)
  ·
    refine ⟨180932997338602853452302797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120621998225735235634868531 180932997338602853452302797)
    ·
      refine ⟨67849874001976070044613549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 180932997338602853452302797 67849874001976070044613549)
      ·
        refine ⟨25443702750741026266730081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67849874001976070044613549 25443702750741026266730081)
        ·
          refine ⟨19082777063055769700047561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25443702750741026266730081 19082777063055769700047561)
          ·
            refine ⟨14312082797291827275035671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19082777063055769700047561 14312082797291827275035671)
            ·
              refine ⟨21468124195937740912553507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14312082797291827275035671 21468124195937740912553507)
              ·
                refine ⟨32202186293906611368830261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21468124195937740912553507 32202186293906611368830261)
                ·
                  refine ⟨3018954965053744815827837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32202186293906611368830261 3018954965053744815827837)
                  ·
                    refine ⟨1132108111895154305935439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3018954965053744815827837 1132108111895154305935439)
                    ·
                      rfl

theorem cell22_3307159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 1, 5, 3].length) (baseStart_3307159 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3307159 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3307159 prefixEnd_3307159 := by exact prefixLift 3307159
  have htrace : WordTrace (prefixWord ++ tailWord_3307159) baseStart_3307159 baseEnd_3307159 := by
    simpa [prefixWord, tailWord_3307159, baseEnd_3307159] using wordTrace_append hprefix tailTrace_3307159
  have hstable : (prefixWord ++ tailWord_3307159).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3307159).length < 2 ^ (prefixWord ++ tailWord_3307159).sum := by decide
  have hdescent : baseEnd_3307159 < baseStart_3307159 := by decide
  rcases family_descends (prefixWord ++ tailWord_3307159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3307182 : List Nat := [4, 1, 4, 1, 3, 1, 1, 2, 2, 3]
def baseStart_3307182 : Nat := 118140960795 + 3307182 * 2 ^ 59
def prefixEnd_3307182 : Nat := 4983230072969 + 3 ^ 40 * 3307182 * 2
def baseEnd_3307182 : Nat := 1132115985265189912610369

theorem tailTrace_3307182 : CollatzResearch.WordTrace tailWord_3307182 prefixEnd_3307182 1132115985265189912610369 := by
  unfold tailWord_3307182
  simp only [CollatzResearch.WordTrace]
  refine ⟨15077854638081488820369475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80415224736434607041970533 15077854638081488820369475)
  ·
    refine ⟨22616781957122233230554213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15077854638081488820369475 22616781957122233230554213)
    ·
      refine ⟨4240646616960418730728915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22616781957122233230554213 4240646616960418730728915)
      ·
        refine ⟨6360969925440628096093373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4240646616960418730728915 6360969925440628096093373)
        ·
          refine ⟨2385363722040235536035015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6360969925440628096093373 2385363722040235536035015)
          ·
            refine ⟨3578045583060353304052523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2385363722040235536035015 3578045583060353304052523)
            ·
              refine ⟨5367068374590529956078785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3578045583060353304052523 5367068374590529956078785)
              ·
                refine ⟨4025301280942897467059089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5367068374590529956078785 4025301280942897467059089)
                ·
                  refine ⟨3018975960707173100294317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4025301280942897467059089 3018975960707173100294317)
                  ·
                    refine ⟨1132115985265189912610369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3018975960707173100294317 1132115985265189912610369)
                    ·
                      rfl

theorem cell22_3307182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 1, 2, 2, 3].length) (baseStart_3307182 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3307182 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3307182 prefixEnd_3307182 := by exact prefixLift 3307182
  have htrace : WordTrace (prefixWord ++ tailWord_3307182) baseStart_3307182 baseEnd_3307182 := by
    simpa [prefixWord, tailWord_3307182, baseEnd_3307182] using wordTrace_append hprefix tailTrace_3307182
  have hstable : (prefixWord ++ tailWord_3307182).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3307182).length < 2 ^ (prefixWord ++ tailWord_3307182).sum := by decide
  have hdescent : baseEnd_3307182 < baseStart_3307182 := by decide
  rcases family_descends (prefixWord ++ tailWord_3307182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3307187 : List Nat := [1, 1, 1, 2, 3, 3, 1, 1, 4, 5]
def baseStart_3307187 : Nat := 118140960795 + 3307187 * 2 ^ 59
def prefixEnd_3307187 : Nat := 4983230072969 + 3 ^ 40 * 3307187 * 2
def baseEnd_3307187 : Nat := 1132117696867371566235353

theorem tailTrace_3307187 : CollatzResearch.WordTrace tailWord_3307187 prefixEnd_3307187 1132117696867371566235353 := by
  unfold tailWord_3307187
  simp only [CollatzResearch.WordTrace]
  refine ⟨120623019469633796416887815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80415346313089197611258543 120623019469633796416887815)
  ·
    refine ⟨180934529204450694625331723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120623019469633796416887815 180934529204450694625331723)
    ·
      refine ⟨271401793806676041937997585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180934529204450694625331723 271401793806676041937997585)
      ·
        refine ⟨203551345355007031453498189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 271401793806676041937997585 203551345355007031453498189)
        ·
          refine ⟨76331754508127636795061821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 203551345355007031453498189 76331754508127636795061821)
          ·
            refine ⟨28624407940547863798148183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76331754508127636795061821 28624407940547863798148183)
            ·
              refine ⟨42936611910821795697222275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28624407940547863798148183 42936611910821795697222275)
              ·
                refine ⟨64404917866232693545833413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42936611910821795697222275 64404917866232693545833413)
                ·
                  refine ⟨12075922099918630039843765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 64404917866232693545833413 12075922099918630039843765)
                  ·
                    refine ⟨1132117696867371566235353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12075922099918630039843765 1132117696867371566235353)
                    ·
                      rfl

theorem cell22_3307187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 1, 4, 5].length) (baseStart_3307187 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3307187 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3307187 prefixEnd_3307187 := by exact prefixLift 3307187
  have htrace : WordTrace (prefixWord ++ tailWord_3307187) baseStart_3307187 baseEnd_3307187 := by
    simpa [prefixWord, tailWord_3307187, baseEnd_3307187] using wordTrace_append hprefix tailTrace_3307187
  have hstable : (prefixWord ++ tailWord_3307187).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3307187).length < 2 ^ (prefixWord ++ tailWord_3307187).sum := by decide
  have hdescent : baseEnd_3307187 < baseStart_3307187 := by decide
  rcases family_descends (prefixWord ++ tailWord_3307187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3307204 : List Nat := [2, 3, 3, 1, 1, 1, 1, 3, 2, 5]
def baseStart_3307204 : Nat := 118140960795 + 3307204 * 2 ^ 59
def prefixEnd_3307204 : Nat := 4983230072969 + 3 ^ 40 * 3307204 * 2
def baseEnd_3307204 : Nat := 1132123516314789188560301

theorem tailTrace_3307204 : CollatzResearch.WordTrace tailWord_3307204 prefixEnd_3307204 1132123516314789188560301 := by
  unfold tailWord_3307204
  simp only [CollatzResearch.WordTrace]
  refine ⟨60311819755286104160128333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80415759673714805546837777 60311819755286104160128333)
  ·
    refine ⟨22616932408232289060048125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60311819755286104160128333 22616932408232289060048125)
    ·
      refine ⟨8481349653087108397518047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22616932408232289060048125 8481349653087108397518047)
      ·
        refine ⟨12722024479630662596277071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8481349653087108397518047 12722024479630662596277071)
        ·
          refine ⟨19083036719445993894415607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12722024479630662596277071 19083036719445993894415607)
          ·
            refine ⟨28624555079168990841623411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19083036719445993894415607 28624555079168990841623411)
            ·
              refine ⟨42936832618753486262435117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28624555079168990841623411 42936832618753486262435117)
              ·
                refine ⟨16101312232032557348413169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42936832618753486262435117 16101312232032557348413169)
                ·
                  refine ⟨12075984174024418011309877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16101312232032557348413169 12075984174024418011309877)
                  ·
                    refine ⟨1132123516314789188560301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12075984174024418011309877 1132123516314789188560301)
                    ·
                      rfl

theorem cell22_3307204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 3, 2, 5].length) (baseStart_3307204 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3307204 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3307204 prefixEnd_3307204 := by exact prefixLift 3307204
  have htrace : WordTrace (prefixWord ++ tailWord_3307204) baseStart_3307204 baseEnd_3307204 := by
    simpa [prefixWord, tailWord_3307204, baseEnd_3307204] using wordTrace_append hprefix tailTrace_3307204
  have hstable : (prefixWord ++ tailWord_3307204).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3307204).length < 2 ^ (prefixWord ++ tailWord_3307204).sum := by decide
  have hdescent : baseEnd_3307204 < baseStart_3307204 := by decide
  rcases family_descends (prefixWord ++ tailWord_3307204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3307266 : List Nat := [3, 4, 1, 1, 1, 1, 2, 3, 1, 5]
def baseStart_3307266 : Nat := 118140960795 + 3307266 * 2 ^ 59
def prefixEnd_3307266 : Nat := 4983230072969 + 3 ^ 40 * 3307266 * 2
def baseEnd_3307266 : Nat := 1132144740181841693510111

theorem tailTrace_3307266 : CollatzResearch.WordTrace tailWord_3307266 prefixEnd_3307266 1132144740181841693510111 := by
  unfold tailWord_3307266
  simp only [CollatzResearch.WordTrace]
  refine ⟨30156475209086898227253413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80417267224231728606009101 30156475209086898227253413)
  ·
    refine ⟨5654339101703793417610015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30156475209086898227253413 5654339101703793417610015)
    ·
      refine ⟨8481508652555690126415023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5654339101703793417610015 8481508652555690126415023)
      ·
        refine ⟨12722262978833535189622535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8481508652555690126415023 12722262978833535189622535)
        ·
          refine ⟨19083394468250302784433803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12722262978833535189622535 19083394468250302784433803)
          ·
            refine ⟨28625091702375454176650705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19083394468250302784433803 28625091702375454176650705)
            ·
              refine ⟨21468818776781590632488029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28625091702375454176650705 21468818776781590632488029)
              ·
                refine ⟨8050807041293096487183011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21468818776781590632488029 8050807041293096487183011)
                ·
                  refine ⟨12076210561939644730774517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8050807041293096487183011 12076210561939644730774517)
                  ·
                    refine ⟨1132144740181841693510111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12076210561939644730774517 1132144740181841693510111)
                    ·
                      rfl

theorem cell22_3307266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 3, 1, 5].length) (baseStart_3307266 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3307266 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3307266 prefixEnd_3307266 := by exact prefixLift 3307266
  have htrace : WordTrace (prefixWord ++ tailWord_3307266) baseStart_3307266 baseEnd_3307266 := by
    simpa [prefixWord, tailWord_3307266, baseEnd_3307266] using wordTrace_append hprefix tailTrace_3307266
  have hstable : (prefixWord ++ tailWord_3307266).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3307266).length < 2 ^ (prefixWord ++ tailWord_3307266).sum := by decide
  have hdescent : baseEnd_3307266 < baseStart_3307266 := by decide
  rcases family_descends (prefixWord ++ tailWord_3307266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3307345 : List Nat := [1, 2, 2, 1, 5, 2, 2, 3, 1, 3]
def baseStart_3307345 : Nat := 118140960795 + 3307345 * 2 ^ 59
def prefixEnd_3307345 : Nat := 4983230072969 + 3 ^ 40 * 3307345 * 2
def baseEnd_3307345 : Nat := 1132171783496311820784869

theorem tailTrace_3307345 : CollatzResearch.WordTrace tailWord_3307345 prefixEnd_3307345 1132171783496311820784869 := by
  unfold tailWord_3307345
  simp only [CollatzResearch.WordTrace]
  refine ⟨120628782203061389401139489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80419188135374259600759659 120628782203061389401139489)
  ·
    refine ⟨90471586652296042050854617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120628782203061389401139489 90471586652296042050854617)
    ·
      refine ⟨67853689989222031538140963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90471586652296042050854617 67853689989222031538140963)
      ·
        refine ⟨101780534983833047307211445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67853689989222031538140963 101780534983833047307211445)
        ·
          refine ⟨9541925154734348185051073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 101780534983833047307211445 9541925154734348185051073)
          ·
            refine ⟨7156443866050761138788305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9541925154734348185051073 7156443866050761138788305)
            ·
              refine ⟨5367332899538070854091229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7156443866050761138788305 5367332899538070854091229)
              ·
                refine ⟨2012749837326776570284211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5367332899538070854091229 2012749837326776570284211)
                ·
                  refine ⟨3019124755990164855426317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2012749837326776570284211 3019124755990164855426317)
                  ·
                    refine ⟨1132171783496311820784869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3019124755990164855426317 1132171783496311820784869)
                    ·
                      rfl

theorem cell22_3307345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 2, 3, 1, 3].length) (baseStart_3307345 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3307345 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3307345 prefixEnd_3307345 := by exact prefixLift 3307345
  have htrace : WordTrace (prefixWord ++ tailWord_3307345) baseStart_3307345 baseEnd_3307345 := by
    simpa [prefixWord, tailWord_3307345, baseEnd_3307345] using wordTrace_append hprefix tailTrace_3307345
  have hstable : (prefixWord ++ tailWord_3307345).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3307345).length < 2 ^ (prefixWord ++ tailWord_3307345).sum := by decide
  have hdescent : baseEnd_3307345 < baseStart_3307345 := by decide
  rcases family_descends (prefixWord ++ tailWord_3307345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3307401 : List Nat := [1, 2, 1, 1, 5, 1, 1, 1, 6, 3]
def baseStart_3307401 : Nat := 118140960795 + 3307401 * 2 ^ 59
def prefixEnd_3307401 : Nat := 4983230072969 + 3 ^ 40 * 3307401 * 2
def baseEnd_3307401 : Nat := 1132190953440746341384697

theorem tailTrace_3307401 : CollatzResearch.WordTrace tailWord_3307401 prefixEnd_3307401 1132190953440746341384697 := by
  unfold tailWord_3307401
  simp only [CollatzResearch.WordTrace]
  refine ⟨120630824690858510965178057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80420549793905673976785371 120630824690858510965178057)
  ·
    refine ⟨90473118518143883223883543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120630824690858510965178057 90473118518143883223883543)
    ·
      refine ⟨135709677777215824835825315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90473118518143883223883543 135709677777215824835825315)
      ·
        refine ⟨203564516665823737253737973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135709677777215824835825315 203564516665823737253737973)
        ·
          refine ⟨19084173437420975367537935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 203564516665823737253737973 19084173437420975367537935)
          ·
            refine ⟨28626260156131463051306903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19084173437420975367537935 28626260156131463051306903)
            ·
              refine ⟨42939390234197194576960355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28626260156131463051306903 42939390234197194576960355)
              ·
                refine ⟨64409085351295791865440533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42939390234197194576960355 64409085351295791865440533)
                ·
                  refine ⟨3019175875841990243692525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 64409085351295791865440533 3019175875841990243692525)
                  ·
                    refine ⟨1132190953440746341384697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3019175875841990243692525 1132190953440746341384697)
                    ·
                      rfl

theorem cell22_3307401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 1, 6, 3].length) (baseStart_3307401 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3307401 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3307401 prefixEnd_3307401 := by exact prefixLift 3307401
  have htrace : WordTrace (prefixWord ++ tailWord_3307401) baseStart_3307401 baseEnd_3307401 := by
    simpa [prefixWord, tailWord_3307401, baseEnd_3307401] using wordTrace_append hprefix tailTrace_3307401
  have hstable : (prefixWord ++ tailWord_3307401).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3307401).length < 2 ^ (prefixWord ++ tailWord_3307401).sum := by decide
  have hdescent : baseEnd_3307401 < baseStart_3307401 := by decide
  rcases family_descends (prefixWord ++ tailWord_3307401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3307418 : List Nat := [3, 1, 1, 4, 2, 1, 2, 1, 4, 3]
def baseStart_3307418 : Nat := 118140960795 + 3307418 * 2 ^ 59
def prefixEnd_3307418 : Nat := 4983230072969 + 3 ^ 40 * 3307418 * 2
def baseEnd_3307418 : Nat := 1132196772888163963709645

theorem tailTrace_3307418 : CollatzResearch.WordTrace tailWord_3307418 prefixEnd_3307418 1132196772888163963709645 := by
  unfold tailWord_3307418
  simp only [CollatzResearch.WordTrace]
  refine ⟨30157861182949230717136727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80420963154531281912364605 30157861182949230717136727)
  ·
    refine ⟨45236791774423846075705091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30157861182949230717136727 45236791774423846075705091)
    ·
      refine ⟨67855187661635769113557637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45236791774423846075705091 67855187661635769113557637)
      ·
        refine ⟨12722847686556706708792057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67855187661635769113557637 12722847686556706708792057)
        ·
          refine ⟨9542135764917530031594043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12722847686556706708792057 9542135764917530031594043)
          ·
            refine ⟨14313203647376295047391065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9542135764917530031594043 14313203647376295047391065)
            ·
              refine ⟨10734902735532221285543299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14313203647376295047391065 10734902735532221285543299)
              ·
                refine ⟨16102354103298331928314949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10734902735532221285543299 16102354103298331928314949)
                ·
                  refine ⟨3019191394368437236559053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16102354103298331928314949 3019191394368437236559053)
                  ·
                    refine ⟨1132196772888163963709645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3019191394368437236559053 1132196772888163963709645)
                    ·
                      rfl

theorem cell22_3307418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 2, 1, 4, 3].length) (baseStart_3307418 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3307418 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3307418 prefixEnd_3307418 := by exact prefixLift 3307418
  have htrace : WordTrace (prefixWord ++ tailWord_3307418) baseStart_3307418 baseEnd_3307418 := by
    simpa [prefixWord, tailWord_3307418, baseEnd_3307418] using wordTrace_append hprefix tailTrace_3307418
  have hstable : (prefixWord ++ tailWord_3307418).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3307418).length < 2 ^ (prefixWord ++ tailWord_3307418).sum := by decide
  have hdescent : baseEnd_3307418 < baseStart_3307418 := by decide
  rcases family_descends (prefixWord ++ tailWord_3307418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3307431 : List Nat := [1, 1, 6, 1, 2, 1, 1, 9]
def baseStart_3307431 : Nat := 118140960795 + 3307431 * 2 ^ 59
def prefixEnd_3307431 : Nat := 4983230072969 + 3 ^ 40 * 3307431 * 2
def baseEnd_3307431 : Nat := 125800135894870695903845

theorem tailTrace_3307431 : CollatzResearch.WordTrace tailWord_3307431 prefixEnd_3307431 125800135894870695903845 := by
  unfold tailWord_3307431
  simp only [CollatzResearch.WordTrace]
  refine ⟨120631918880749826088770147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80421279253833217392513431 120631918880749826088770147)
  ·
    refine ⟨180947878321124739133155221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120631918880749826088770147 180947878321124739133155221)
    ·
      refine ⟨8481931796302722146866651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 180947878321124739133155221 8481931796302722146866651)
      ·
        refine ⟨12722897694454083220299977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8481931796302722146866651 12722897694454083220299977)
        ·
          refine ⟨9542173270840562415224983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12722897694454083220299977 9542173270840562415224983)
          ·
            refine ⟨14313259906260843622837475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9542173270840562415224983 14313259906260843622837475)
            ·
              refine ⟨21469889859391265434256213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14313259906260843622837475 21469889859391265434256213)
              ·
                refine ⟨125800135894870695903845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 21469889859391265434256213 125800135894870695903845)
                ·
                  rfl

theorem cell22_3307431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 9].length) (baseStart_3307431 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3307431 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3307431 prefixEnd_3307431 := by exact prefixLift 3307431
  have htrace : WordTrace (prefixWord ++ tailWord_3307431) baseStart_3307431 baseEnd_3307431 := by
    simpa [prefixWord, tailWord_3307431, baseEnd_3307431] using wordTrace_append hprefix tailTrace_3307431
  have hstable : (prefixWord ++ tailWord_3307431).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3307431).length < 2 ^ (prefixWord ++ tailWord_3307431).sum := by decide
  have hdescent : baseEnd_3307431 < baseStart_3307431 := by decide
  rcases family_descends (prefixWord ++ tailWord_3307431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3307480 : List Nat := [2, 1, 2, 2, 2, 2, 3, 4, 1, 3]
def baseStart_3307480 : Nat := 118140960795 + 3307480 * 2 ^ 59
def prefixEnd_3307480 : Nat := 4983230072969 + 3 ^ 40 * 3307480 * 2
def baseEnd_3307480 : Nat := 1132217996755216468659455

theorem tailTrace_3307480 : CollatzResearch.WordTrace tailWord_3307480 prefixEnd_3307480 1132217996755216468659455 := by
  unfold tailWord_3307480
  simp only [CollatzResearch.WordTrace]
  refine ⟨60316853028786153728651947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80422470705048204971535929 60316853028786153728651947)
  ·
    refine ⟨90475279543179230592977921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60316853028786153728651947 90475279543179230592977921)
    ·
      refine ⟨67856459657384422944733441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90475279543179230592977921 67856459657384422944733441)
      ·
        refine ⟨50892344743038317208550081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67856459657384422944733441 50892344743038317208550081)
        ·
          refine ⟨38169258557278737906412561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50892344743038317208550081 38169258557278737906412561)
          ·
            refine ⟨28626943917959053429809421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38169258557278737906412561 28626943917959053429809421)
            ·
              refine ⟨10735103969234645036178533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28626943917959053429809421 10735103969234645036178533)
              ·
                refine ⟨2012831994231495944283475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10735103969234645036178533 2012831994231495944283475)
                ·
                  refine ⟨3019247991347243916425213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2012831994231495944283475 3019247991347243916425213)
                  ·
                    refine ⟨1132217996755216468659455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3019247991347243916425213 1132217996755216468659455)
                    ·
                      rfl

theorem cell22_3307480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3, 4, 1, 3].length) (baseStart_3307480 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3307480 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3307480 prefixEnd_3307480 := by exact prefixLift 3307480
  have htrace : WordTrace (prefixWord ++ tailWord_3307480) baseStart_3307480 baseEnd_3307480 := by
    simpa [prefixWord, tailWord_3307480, baseEnd_3307480] using wordTrace_append hprefix tailTrace_3307480
  have hstable : (prefixWord ++ tailWord_3307480).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3307480).length < 2 ^ (prefixWord ++ tailWord_3307480).sum := by decide
  have hdescent : baseEnd_3307480 < baseStart_3307480 := by decide
  rcases family_descends (prefixWord ++ tailWord_3307480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3307491 : List Nat := [1, 1, 1, 6, 1, 2, 1, 1, 1, 7]
def baseStart_3307491 : Nat := 118140960795 + 3307491 * 2 ^ 59
def prefixEnd_3307491 : Nat := 4983230072969 + 3 ^ 40 * 3307491 * 2
def baseEnd_3307491 : Nat := 1132221762280016106634421

theorem tailTrace_3307491 : CollatzResearch.WordTrace tailWord_3307491 prefixEnd_3307491 1132221762280016106634421 := by
  unfold tailWord_3307491
  simp only [CollatzResearch.WordTrace]
  refine ⟨120634107260532456335954327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80422738173688304223969551 120634107260532456335954327)
  ·
    refine ⟨180951160890798684503931491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120634107260532456335954327 180951160890798684503931491)
    ·
      refine ⟨271426741336198026755897237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180951160890798684503931491 271426741336198026755897237)
      ·
        refine ⟨12723128500134282504182683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 271426741336198026755897237 12723128500134282504182683)
        ·
          refine ⟨19084692750201423756274025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12723128500134282504182683 19084692750201423756274025)
          ·
            refine ⟨14313519562651067817205519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19084692750201423756274025 14313519562651067817205519)
            ·
              refine ⟨21470279343976601725808279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14313519562651067817205519 21470279343976601725808279)
              ·
                refine ⟨32205419015964902588712419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21470279343976601725808279 32205419015964902588712419)
                ·
                  refine ⟨48308128523947353883068629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32205419015964902588712419 48308128523947353883068629)
                  ·
                    refine ⟨1132221762280016106634421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48308128523947353883068629 1132221762280016106634421)
                    ·
                      rfl

theorem cell22_3307491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 1, 1, 7].length) (baseStart_3307491 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3307491 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3307491 prefixEnd_3307491 := by exact prefixLift 3307491
  have htrace : WordTrace (prefixWord ++ tailWord_3307491) baseStart_3307491 baseEnd_3307491 := by
    simpa [prefixWord, tailWord_3307491, baseEnd_3307491] using wordTrace_append hprefix tailTrace_3307491
  have hstable : (prefixWord ++ tailWord_3307491).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3307491).length < 2 ^ (prefixWord ++ tailWord_3307491).sum := by decide
  have hdescent : baseEnd_3307491 < baseStart_3307491 := by decide
  rcases family_descends (prefixWord ++ tailWord_3307491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3307521 : List Nat := [1, 2, 4, 1, 2, 1, 1, 2, 8]
def baseStart_3307521 : Nat := 118140960795 + 3307521 * 2 ^ 59
def prefixEnd_3307521 : Nat := 4983230072969 + 3 ^ 40 * 3307521 * 2
def baseEnd_3307521 : Nat := 377410677297702009461443

theorem tailTrace_3307521 : CollatzResearch.WordTrace tailWord_3307521 prefixEnd_3307521 377410677297702009461443 := by
  unfold tailWord_3307521
  simp only [CollatzResearch.WordTrace]
  refine ⟨120635201450423771459546417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80423467633615847639697611 120635201450423771459546417)
  ·
    refine ⟨90476401087817828594659813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120635201450423771459546417 90476401087817828594659813)
    ·
      refine ⟨16964325203965842861498715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 90476401087817828594659813 16964325203965842861498715)
      ·
        refine ⟨25446487805948764292248073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16964325203965842861498715 25446487805948764292248073)
        ·
          refine ⟨19084865854461573219186055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25446487805948764292248073 19084865854461573219186055)
          ·
            refine ⟨28627298781692359828779083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19084865854461573219186055 28627298781692359828779083)
            ·
              refine ⟨42940948172538539743168625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28627298781692359828779083 42940948172538539743168625)
              ·
                refine ⟨32205711129403904807376469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42940948172538539743168625 32205711129403904807376469)
                ·
                  refine ⟨377410677297702009461443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 32205711129403904807376469 377410677297702009461443)
                  ·
                    rfl

theorem cell22_3307521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 2, 8].length) (baseStart_3307521 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3307521 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3307521 prefixEnd_3307521 := by exact prefixLift 3307521
  have htrace : WordTrace (prefixWord ++ tailWord_3307521) baseStart_3307521 baseEnd_3307521 := by
    simpa [prefixWord, tailWord_3307521, baseEnd_3307521] using wordTrace_append hprefix tailTrace_3307521
  have hstable : (prefixWord ++ tailWord_3307521).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3307521).length < 2 ^ (prefixWord ++ tailWord_3307521).sum := by decide
  have hdescent : baseEnd_3307521 < baseStart_3307521 := by decide
  rcases family_descends (prefixWord ++ tailWord_3307521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3307551 : List Nat := [1, 1, 2, 4, 1, 2, 1, 1, 3, 6]
def baseStart_3307551 : Nat := 118140960795 + 3307551 * 2 ^ 59
def prefixEnd_3307551 : Nat := 4983230072969 + 3 ^ 40 * 3307551 * 2
def baseEnd_3307551 : Nat := 1132242301506195950134237

theorem tailTrace_3307551 : CollatzResearch.WordTrace tailWord_3307551 prefixEnd_3307551 1132242301506195950134237 := by
  unfold tailWord_3307551
  simp only [CollatzResearch.WordTrace]
  refine ⟨120636295640315086583138507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80424197093543391055425671 120636295640315086583138507)
  ·
    refine ⟨180954443460472629874707761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120636295640315086583138507 180954443460472629874707761)
    ·
      refine ⟨135715832595354472406030821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180954443460472629874707761 135715832595354472406030821)
      ·
        refine ⟨25446718611628963576130779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 135715832595354472406030821 25446718611628963576130779)
        ·
          refine ⟨38170077917443445364196169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25446718611628963576130779 38170077917443445364196169)
          ·
            refine ⟨28627558438082584023147127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38170077917443445364196169 28627558438082584023147127)
            ·
              refine ⟨42941337657123876034720691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28627558438082584023147127 42941337657123876034720691)
              ·
                refine ⟨64412006485685814052081037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42941337657123876034720691 64412006485685814052081037)
                ·
                  refine ⟨24154502432132180269530389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64412006485685814052081037 24154502432132180269530389)
                  ·
                    refine ⟨1132242301506195950134237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24154502432132180269530389 1132242301506195950134237)
                    ·
                      rfl

theorem cell22_3307551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 1, 3, 6].length) (baseStart_3307551 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3307551 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3307551 prefixEnd_3307551 := by exact prefixLift 3307551
  have htrace : WordTrace (prefixWord ++ tailWord_3307551) baseStart_3307551 baseEnd_3307551 := by
    simpa [prefixWord, tailWord_3307551, baseEnd_3307551] using wordTrace_append hprefix tailTrace_3307551
  have hstable : (prefixWord ++ tailWord_3307551).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3307551).length < 2 ^ (prefixWord ++ tailWord_3307551).sum := by decide
  have hdescent : baseEnd_3307551 < baseStart_3307551 := by decide
  rcases family_descends (prefixWord ++ tailWord_3307551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3307585 : List Nat := [1, 2, 5, 1, 2, 2, 1, 2, 2, 4]
def baseStart_3307585 : Nat := 118140960795 + 3307585 * 2 ^ 59
def prefixEnd_3307585 : Nat := 4983230072969 + 3 ^ 40 * 3307585 * 2
def baseEnd_3307585 : Nat := 1132253940401031194784133

theorem tailTrace_3307585 : CollatzResearch.WordTrace tailWord_3307585 prefixEnd_3307585 1132253940401031194784133 := by
  unfold tailWord_3307585
  simp only [CollatzResearch.WordTrace]
  refine ⟨120637535722191910389876209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80425023814794606926584139 120637535722191910389876209)
  ·
    refine ⟨90478151791643932792407157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120637535722191910389876209 90478151791643932792407157)
    ·
      refine ⟨8482326730466618699288171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 90478151791643932792407157 8482326730466618699288171)
      ·
        refine ⟨12723490095699928048932257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8482326730466618699288171 12723490095699928048932257)
        ·
          refine ⟨9542617571774946036699193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12723490095699928048932257 9542617571774946036699193)
          ·
            refine ⟨7156963178831209527524395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9542617571774946036699193 7156963178831209527524395)
            ·
              refine ⟨10735444768246814291286593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7156963178831209527524395 10735444768246814291286593)
              ·
                refine ⟨8051583576185110718464945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10735444768246814291286593 8051583576185110718464945)
                ·
                  refine ⟨6038687682138833038848709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8051583576185110718464945 6038687682138833038848709)
                  ·
                    refine ⟨1132253940401031194784133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6038687682138833038848709 1132253940401031194784133)
                    ·
                      rfl

theorem cell22_3307585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 1, 2, 2, 4].length) (baseStart_3307585 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3307585 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3307585 prefixEnd_3307585 := by exact prefixLift 3307585
  have htrace : WordTrace (prefixWord ++ tailWord_3307585) baseStart_3307585 baseEnd_3307585 := by
    simpa [prefixWord, tailWord_3307585, baseEnd_3307585] using wordTrace_append hprefix tailTrace_3307585
  have hstable : (prefixWord ++ tailWord_3307585).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3307585).length < 2 ^ (prefixWord ++ tailWord_3307585).sum := by decide
  have hdescent : baseEnd_3307585 < baseStart_3307585 := by decide
  rcases family_descends (prefixWord ++ tailWord_3307585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3307645 : List Nat := [1, 4, 1, 1, 3, 3, 2, 2, 5]
def baseStart_3307645 : Nat := 118140960795 + 3307645 * 2 ^ 59
def prefixEnd_3307645 : Nat := 4983230072969 + 3 ^ 40 * 3307645 * 2
def baseEnd_3307645 : Nat := 377424826542403679427983

theorem tailTrace_3307645 : CollatzResearch.WordTrace tailWord_3307645 prefixEnd_3307645 377424826542403679427983 := by
  unfold tailWord_3307645
  simp only [CollatzResearch.WordTrace]
  refine ⟨120639724101974540637060389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80426482734649693758040259 120639724101974540637060389)
  ·
    refine ⟨22619948269120226369448823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 120639724101974540637060389 22619948269120226369448823)
    ·
      refine ⟨33929922403680339554173235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22619948269120226369448823 33929922403680339554173235)
      ·
        refine ⟨50894883605520509331259853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33929922403680339554173235 50894883605520509331259853)
        ·
          refine ⟨19085581352070190999222445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50894883605520509331259853 19085581352070190999222445)
          ·
            refine ⟨7157093007026321624708417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19085581352070190999222445 7157093007026321624708417)
            ·
              refine ⟨5367819755269741218531313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7157093007026321624708417 5367819755269741218531313)
              ·
                refine ⟨4025864816452305913898485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5367819755269741218531313 4025864816452305913898485)
                ·
                  refine ⟨377424826542403679427983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4025864816452305913898485 377424826542403679427983)
                  ·
                    rfl

theorem cell22_3307645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 2, 2, 5].length) (baseStart_3307645 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3307645 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3307645 prefixEnd_3307645 := by exact prefixLift 3307645
  have htrace : WordTrace (prefixWord ++ tailWord_3307645) baseStart_3307645 baseEnd_3307645 := by
    simpa [prefixWord, tailWord_3307645, baseEnd_3307645] using wordTrace_append hprefix tailTrace_3307645
  have hstable : (prefixWord ++ tailWord_3307645).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3307645).length < 2 ^ (prefixWord ++ tailWord_3307645).sum := by decide
  have hdescent : baseEnd_3307645 < baseStart_3307645 := by decide
  rcases family_descends (prefixWord ++ tailWord_3307645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3307649 : List Nat := [1, 2, 4, 2, 3, 1, 1, 4, 1, 3]
def baseStart_3307649 : Nat := 118140960795 + 3307649 * 2 ^ 59
def prefixEnd_3307649 : Nat := 4983230072969 + 3 ^ 40 * 3307649 * 2
def baseEnd_3307649 : Nat := 1132275848908956361183937

theorem tailTrace_3307649 : CollatzResearch.WordTrace tailWord_3307649 prefixEnd_3307649 1132275848908956361183937 := by
  unfold tailWord_3307649
  simp only [CollatzResearch.WordTrace]
  refine ⟨120639869993960049320206001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80426579995973366213470667 120639869993960049320206001)
  ·
    refine ⟨90479902495470036990154501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120639869993960049320206001 90479902495470036990154501)
    ·
      refine ⟨16964981717900631935653969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 90479902495470036990154501 16964981717900631935653969)
      ·
        refine ⟨12723736288425473951740477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16964981717900631935653969 12723736288425473951740477)
        ·
          refine ⟨4771401108159552731902679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12723736288425473951740477 4771401108159552731902679)
          ·
            refine ⟨7157101662239329097854019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4771401108159552731902679 7157101662239329097854019)
            ·
              refine ⟨10735652493358993646781029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7157101662239329097854019 10735652493358993646781029)
              ·
                refine ⟨2012934842504811308771443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10735652493358993646781029 2012934842504811308771443)
                ·
                  refine ⟨3019402263757216963157165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2012934842504811308771443 3019402263757216963157165)
                  ·
                    refine ⟨1132275848908956361183937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3019402263757216963157165 1132275848908956361183937)
                    ·
                      rfl

theorem cell22_3307649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 1, 4, 1, 3].length) (baseStart_3307649 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3307649 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3307649 prefixEnd_3307649 := by exact prefixLift 3307649
  have htrace : WordTrace (prefixWord ++ tailWord_3307649) baseStart_3307649 baseEnd_3307649 := by
    simpa [prefixWord, tailWord_3307649, baseEnd_3307649] using wordTrace_append hprefix tailTrace_3307649
  have hstable : (prefixWord ++ tailWord_3307649).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3307649).length < 2 ^ (prefixWord ++ tailWord_3307649).sum := by decide
  have hdescent : baseEnd_3307649 < baseStart_3307649 := by decide
  rcases family_descends (prefixWord ++ tailWord_3307649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3307670 : List Nat := [5, 3, 2, 1, 2, 1, 1, 1, 2, 4]
def baseStart_3307670 : Nat := 118140960795 + 3307670 * 2 ^ 59
def prefixEnd_3307670 : Nat := 4983230072969 + 3 ^ 40 * 3307670 * 2
def baseEnd_3307670 : Nat := 1132283037638119306408873

theorem tailTrace_3307670 : CollatzResearch.WordTrace tailWord_3307670 prefixEnd_3307670 1132283037638119306408873 := by
  unfold tailWord_3307670
  simp only [CollatzResearch.WordTrace]
  refine ⟨7540039745430248119170029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 80427090617922646604480309 7540039745430248119170029)
  ·
    refine ⟨2827514904536343044688761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7540039745430248119170029 2827514904536343044688761)
    ·
      refine ⟨2120636178402257283516571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2827514904536343044688761 2120636178402257283516571)
      ·
        refine ⟨3180954267603385925274857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2120636178402257283516571 3180954267603385925274857)
        ·
          refine ⟨2385715700702539443956143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3180954267603385925274857 2385715700702539443956143)
          ·
            refine ⟨3578573551053809165934215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2385715700702539443956143 3578573551053809165934215)
            ·
              refine ⟨5367860326580713748901323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3578573551053809165934215 5367860326580713748901323)
              ·
                refine ⟨8051790489871070623351985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5367860326580713748901323 8051790489871070623351985)
                ·
                  refine ⟨6038842867403302967513989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8051790489871070623351985 6038842867403302967513989)
                  ·
                    refine ⟨1132283037638119306408873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6038842867403302967513989 1132283037638119306408873)
                    ·
                      rfl

theorem cell22_3307670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 1, 1, 2, 4].length) (baseStart_3307670 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3307670 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3307670 prefixEnd_3307670 := by exact prefixLift 3307670
  have htrace : WordTrace (prefixWord ++ tailWord_3307670) baseStart_3307670 baseEnd_3307670 := by
    simpa [prefixWord, tailWord_3307670, baseEnd_3307670] using wordTrace_append hprefix tailTrace_3307670
  have hstable : (prefixWord ++ tailWord_3307670).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3307670).length < 2 ^ (prefixWord ++ tailWord_3307670).sum := by decide
  have hdescent : baseEnd_3307670 < baseStart_3307670 := by decide
  rcases family_descends (prefixWord ++ tailWord_3307670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3307705 : List Nat := [1, 2, 1, 4, 1, 2, 3, 1, 4, 3]
def baseStart_3307705 : Nat := 118140960795 + 3307705 * 2 ^ 59
def prefixEnd_3307705 : Nat := 4983230072969 + 3 ^ 40 * 3307705 * 2
def baseEnd_3307705 : Nat := 1132295018853390881783765

theorem tailTrace_3307705 : CollatzResearch.WordTrace tailWord_3307705 prefixEnd_3307705 1132295018853390881783765 := by
  unfold tailWord_3307705
  simp only [CollatzResearch.WordTrace]
  refine ⟨120641912481757170884244569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80427941654504780589496379 120641912481757170884244569)
  ·
    refine ⟨90481434361317878163183427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120641912481757170884244569 90481434361317878163183427)
    ·
      refine ⟨135722151541976817244775141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90481434361317878163183427 135722151541976817244775141)
      ·
        refine ⟨25447903414120653233395339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 135722151541976817244775141 25447903414120653233395339)
        ·
          refine ⟨38171855121180979850093009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25447903414120653233395339 38171855121180979850093009)
          ·
            refine ⟨28628891340885734887569757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38171855121180979850093009 28628891340885734887569757)
            ·
              refine ⟨10735834252832150582838659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28628891340885734887569757 10735834252832150582838659)
              ·
                refine ⟨16103751379248225874257989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10735834252832150582838659 16103751379248225874257989)
                ·
                  refine ⟨3019453383609042351423373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16103751379248225874257989 3019453383609042351423373)
                  ·
                    refine ⟨1132295018853390881783765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3019453383609042351423373 1132295018853390881783765)
                    ·
                      rfl

theorem cell22_3307705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3, 1, 4, 3].length) (baseStart_3307705 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3307705 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3307705 prefixEnd_3307705 := by exact prefixLift 3307705
  have htrace : WordTrace (prefixWord ++ tailWord_3307705) baseStart_3307705 baseEnd_3307705 := by
    simpa [prefixWord, tailWord_3307705, baseEnd_3307705] using wordTrace_append hprefix tailTrace_3307705
  have hstable : (prefixWord ++ tailWord_3307705).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3307705).length < 2 ^ (prefixWord ++ tailWord_3307705).sum := by decide
  have hdescent : baseEnd_3307705 < baseStart_3307705 := by decide
  rcases family_descends (prefixWord ++ tailWord_3307705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3307748 : List Nat := [2, 3, 1, 1, 1, 2, 1, 2, 1, 8]
def baseStart_3307748 : Nat := 118140960795 + 3307748 * 2 ^ 59
def prefixEnd_3307748 : Nat := 4983230072969 + 3 ^ 40 * 3307748 * 2
def baseEnd_3307748 : Nat := 1132309738632153102958633

theorem tailTrace_3307748 : CollatzResearch.WordTrace tailWord_3307748 prefixEnd_3307748 1132309738632153102958633 := by
  unfold tailWord_3307748
  simp only [CollatzResearch.WordTrace]
  refine ⟨60321740410300694614029949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80428987213734259485373265 60321740410300694614029949)
  ·
    refine ⟨22620652653862760480261231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60321740410300694614029949 22620652653862760480261231)
    ·
      refine ⟨33930978980794140720391847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22620652653862760480261231 33930978980794140720391847)
      ·
        refine ⟨50896468471191211080587771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33930978980794140720391847 50896468471191211080587771)
        ·
          refine ⟨76344702706786816620881657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50896468471191211080587771 76344702706786816620881657)
          ·
            refine ⟨57258527030090112465661243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76344702706786816620881657 57258527030090112465661243)
            ·
              refine ⟨85887790545135168698491865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57258527030090112465661243 85887790545135168698491865)
              ·
                refine ⟨64415842908851376523868899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85887790545135168698491865 64415842908851376523868899)
                ·
                  refine ⟨96623764363277064785803349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64415842908851376523868899 96623764363277064785803349)
                  ·
                    refine ⟨1132309738632153102958633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 96623764363277064785803349 1132309738632153102958633)
                    ·
                      rfl

theorem cell22_3307748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 2, 1, 8].length) (baseStart_3307748 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3307748 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3307748 prefixEnd_3307748 := by exact prefixLift 3307748
  have htrace : WordTrace (prefixWord ++ tailWord_3307748) baseStart_3307748 baseEnd_3307748 := by
    simpa [prefixWord, tailWord_3307748, baseEnd_3307748] using wordTrace_append hprefix tailTrace_3307748
  have hstable : (prefixWord ++ tailWord_3307748).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3307748).length < 2 ^ (prefixWord ++ tailWord_3307748).sum := by decide
  have hdescent : baseEnd_3307748 < baseStart_3307748 := by decide
  rcases family_descends (prefixWord ++ tailWord_3307748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3307763 : List Nat := [1, 1, 1, 2, 2, 4, 1, 3, 7]
def baseStart_3307763 : Nat := 118140960795 + 3307763 * 2 ^ 59
def prefixEnd_3307763 : Nat := 4983230072969 + 3 ^ 40 * 3307763 * 2
def baseEnd_3307763 : Nat := 377438291146232687944529

theorem tailTrace_3307763 : CollatzResearch.WordTrace tailWord_3307763 prefixEnd_3307763 377438291146232687944529 := by
  unfold tailWord_3307763
  simp only [CollatzResearch.WordTrace]
  refine ⟨120644027915547046789855943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80429351943698031193237295 120644027915547046789855943)
  ·
    refine ⟨180966041873320570184783915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120644027915547046789855943 180966041873320570184783915)
    ·
      refine ⟨271449062809980855277175873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180966041873320570184783915 271449062809980855277175873)
      ·
        refine ⟨203586797107485641457881905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 271449062809980855277175873 203586797107485641457881905)
        ·
          refine ⟨152690097830614231093411429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 203586797107485641457881905 152690097830614231093411429)
          ·
            refine ⟨28629393343240168330014643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 152690097830614231093411429 28629393343240168330014643)
            ·
              refine ⟨42944090014860252495021965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28629393343240168330014643 42944090014860252495021965)
              ·
                refine ⟨16104033755572594685633237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42944090014860252495021965 16104033755572594685633237)
                ·
                  refine ⟨377438291146232687944529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16104033755572594685633237 377438291146232687944529)
                  ·
                    rfl

theorem cell22_3307763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 3, 7].length) (baseStart_3307763 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3307763 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3307763 prefixEnd_3307763 := by exact prefixLift 3307763
  have htrace : WordTrace (prefixWord ++ tailWord_3307763) baseStart_3307763 baseEnd_3307763 := by
    simpa [prefixWord, tailWord_3307763, baseEnd_3307763] using wordTrace_append hprefix tailTrace_3307763
  have hstable : (prefixWord ++ tailWord_3307763).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3307763).length < 2 ^ (prefixWord ++ tailWord_3307763).sum := by decide
  have hdescent : baseEnd_3307763 < baseStart_3307763 := by decide
  rcases family_descends (prefixWord ++ tailWord_3307763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3307855 : List Nat := [1, 1, 2, 1, 1, 2, 1, 7, 2, 4]
def baseStart_3307855 : Nat := 118140960795 + 3307855 * 2 ^ 59
def prefixEnd_3307855 : Nat := 4983230072969 + 3 ^ 40 * 3307855 * 2
def baseEnd_3307855 : Nat := 1132346366918840490533305

theorem tailTrace_3307855 : CollatzResearch.WordTrace tailWord_3307855 prefixEnd_3307855 1132346366918840490533305 := by
  unfold tailWord_3307855
  simp only [CollatzResearch.WordTrace]
  refine ⟨120647383431213746502205019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80431588954142497668136679 120647383431213746502205019)
  ·
    refine ⟨180971075146820619753307529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120647383431213746502205019 180971075146820619753307529)
    ·
      refine ⟨135728306360115464814980647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180971075146820619753307529 135728306360115464814980647)
      ·
        refine ⟨203592459540173197222470971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135728306360115464814980647 203592459540173197222470971)
        ·
          refine ⟨305388689310259795833706457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203592459540173197222470971 305388689310259795833706457)
          ·
            refine ⟨229041516982694846875279843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 305388689310259795833706457 229041516982694846875279843)
            ·
              refine ⟨343562275474042270312919765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 229041516982694846875279843 343562275474042270312919765)
              ·
                refine ⟨8052240831422865710459057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 343562275474042270312919765 8052240831422865710459057)
                ·
                  refine ⟨6039180623567149282844293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8052240831422865710459057 6039180623567149282844293)
                  ·
                    refine ⟨1132346366918840490533305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6039180623567149282844293 1132346366918840490533305)
                    ·
                      rfl

theorem cell22_3307855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 7, 2, 4].length) (baseStart_3307855 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3307855 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3307855 prefixEnd_3307855 := by exact prefixLift 3307855
  have htrace : WordTrace (prefixWord ++ tailWord_3307855) baseStart_3307855 baseEnd_3307855 := by
    simpa [prefixWord, tailWord_3307855, baseEnd_3307855] using wordTrace_append hprefix tailTrace_3307855
  have hstable : (prefixWord ++ tailWord_3307855).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3307855).length < 2 ^ (prefixWord ++ tailWord_3307855).sum := by decide
  have hdescent : baseEnd_3307855 < baseStart_3307855 := by decide
  rcases family_descends (prefixWord ++ tailWord_3307855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3307861 : List Nat := [1, 3, 2, 2, 4, 2, 2, 1, 1, 4]
def baseStart_3307861 : Nat := 118140960795 + 3307861 * 2 ^ 59
def prefixEnd_3307861 : Nat := 4983230072969 + 3 ^ 40 * 3307861 * 2
def baseEnd_3307861 : Nat := 1132348420841458474883287

theorem tailTrace_3307861 : CollatzResearch.WordTrace tailWord_3307861 prefixEnd_3307861 1132348420841458474883287 := by
  unfold tailWord_3307861
  simp only [CollatzResearch.WordTrace]
  refine ⟨120647602269192009526923437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80431734846128006351282291 120647602269192009526923437)
  ·
    refine ⟨45242850850947003572596289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120647602269192009526923437 45242850850947003572596289)
    ·
      refine ⟨33932138138210252679447217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45242850850947003572596289 33932138138210252679447217)
      ·
        refine ⟨25449103603657689509585413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33932138138210252679447217 25449103603657689509585413)
        ·
          refine ⟨4771706925685816783047265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25449103603657689509585413 4771706925685816783047265)
          ·
            refine ⟨3578780194264362587285449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4771706925685816783047265 3578780194264362587285449)
            ·
              refine ⟨2684085145698271940464087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3578780194264362587285449 2684085145698271940464087)
              ·
                refine ⟨4026127718547407910696131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2684085145698271940464087 4026127718547407910696131)
                ·
                  refine ⟨6039191577821111866044197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4026127718547407910696131 6039191577821111866044197)
                  ·
                    refine ⟨1132348420841458474883287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6039191577821111866044197 1132348420841458474883287)
                    ·
                      rfl

theorem cell22_3307861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 2, 1, 1, 4].length) (baseStart_3307861 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3307861 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3307861 prefixEnd_3307861 := by exact prefixLift 3307861
  have htrace : WordTrace (prefixWord ++ tailWord_3307861) baseStart_3307861 baseEnd_3307861 := by
    simpa [prefixWord, tailWord_3307861, baseEnd_3307861] using wordTrace_append hprefix tailTrace_3307861
  have hstable : (prefixWord ++ tailWord_3307861).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3307861).length < 2 ^ (prefixWord ++ tailWord_3307861).sum := by decide
  have hdescent : baseEnd_3307861 < baseStart_3307861 := by decide
  rcases family_descends (prefixWord ++ tailWord_3307861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3307874 : List Nat := [3, 3, 2, 1, 1, 3, 1, 1, 4, 3]
def baseStart_3307874 : Nat := 118140960795 + 3307874 * 2 ^ 59
def prefixEnd_3307874 : Nat := 4983230072969 + 3 ^ 40 * 3307874 * 2
def baseEnd_3307874 : Nat := 1132352871007130774308247

theorem tailTrace_3307874 : CollatzResearch.WordTrace tailWord_3307874 prefixEnd_3307874 1132352871007130774308247 := by
  unfold tailWord_3307874
  simp only [CollatzResearch.WordTrace]
  refine ⟨30162019104536228186786669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80432050945429941831431117 30162019104536228186786669)
  ·
    refine ⟨11310757164201085570045001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30162019104536228186786669 11310757164201085570045001)
    ·
      refine ⟨8483067873150814177533751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11310757164201085570045001 8483067873150814177533751)
      ·
        refine ⟨12724601809726221266300627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8483067873150814177533751 12724601809726221266300627)
        ·
          refine ⟨19086902714589331899450941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12724601809726221266300627 19086902714589331899450941)
          ·
            refine ⟨7157588517970999462294103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19086902714589331899450941 7157588517970999462294103)
            ·
              refine ⟨10736382776956499193441155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7157588517970999462294103 10736382776956499193441155)
              ·
                refine ⟨16104574165434748790161733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10736382776956499193441155 16104574165434748790161733)
                ·
                  refine ⟨3019607656019015398155325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16104574165434748790161733 3019607656019015398155325)
                  ·
                    refine ⟨1132352871007130774308247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3019607656019015398155325 1132352871007130774308247)
                    ·
                      rfl

theorem cell22_3307874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 1, 1, 4, 3].length) (baseStart_3307874 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3307874 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3307874 prefixEnd_3307874 := by exact prefixLift 3307874
  have htrace : WordTrace (prefixWord ++ tailWord_3307874) baseStart_3307874 baseEnd_3307874 := by
    simpa [prefixWord, tailWord_3307874, baseEnd_3307874] using wordTrace_append hprefix tailTrace_3307874
  have hstable : (prefixWord ++ tailWord_3307874).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3307874).length < 2 ^ (prefixWord ++ tailWord_3307874).sum := by decide
  have hdescent : baseEnd_3307874 < baseStart_3307874 := by decide
  rcases family_descends (prefixWord ++ tailWord_3307874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3307915 : List Nat := [1, 1, 1, 1, 4, 4, 1, 2, 7]
def baseStart_3307915 : Nat := 118140960795 + 3307915 * 2 ^ 59
def prefixEnd_3307915 : Nat := 4983230072969 + 3 ^ 40 * 3307915 * 2
def baseEnd_3307915 : Nat := 377455635381673444677707

theorem tailTrace_3307915 : CollatzResearch.WordTrace tailWord_3307915 prefixEnd_3307915 377455635381673444677707 := by
  unfold tailWord_3307915
  simp only [CollatzResearch.WordTrace]
  refine ⟨120649571810996376749389199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80433047873997584499592799 120649571810996376749389199)
  ·
    refine ⟨180974357716494565124083799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120649571810996376749389199 180974357716494565124083799)
    ·
      refine ⟨271461536574741847686125699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180974357716494565124083799 271461536574741847686125699)
      ·
        refine ⟨407192304862112771529188549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 271461536574741847686125699 407192304862112771529188549)
        ·
          refine ⟨76348557161646144661722853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 407192304862112771529188549 76348557161646144661722853)
          ·
            refine ⟨14315354467808652124073035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76348557161646144661722853 14315354467808652124073035)
            ·
              refine ⟨21473031701712978186109553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14315354467808652124073035 21473031701712978186109553)
              ·
                refine ⟨16104773776284733639582165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21473031701712978186109553 16104773776284733639582165)
                ·
                  refine ⟨377455635381673444677707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16104773776284733639582165 377455635381673444677707)
                  ·
                    rfl

theorem cell22_3307915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 2, 7].length) (baseStart_3307915 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3307915 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3307915 prefixEnd_3307915 := by exact prefixLift 3307915
  have htrace : WordTrace (prefixWord ++ tailWord_3307915) baseStart_3307915 baseEnd_3307915 := by
    simpa [prefixWord, tailWord_3307915, baseEnd_3307915] using wordTrace_append hprefix tailTrace_3307915
  have hstable : (prefixWord ++ tailWord_3307915).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3307915).length < 2 ^ (prefixWord ++ tailWord_3307915).sum := by decide
  have hdescent : baseEnd_3307915 < baseStart_3307915 := by decide
  rcases family_descends (prefixWord ++ tailWord_3307915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3307960 : List Nat := [2, 1, 2, 1, 2, 2, 1, 3, 8]
def baseStart_3307960 : Nat := 118140960795 + 3307960 * 2 ^ 59
def prefixEnd_3307960 : Nat := 4983230072969 + 3 ^ 40 * 3307960 * 2
def baseEnd_3307960 : Nat := 377460770188218405552661

theorem tailTrace_3307960 : CollatzResearch.WordTrace tailWord_3307960 prefixEnd_3307960 377460770188218405552661 := by
  unfold tailWord_3307960
  simp only [CollatzResearch.WordTrace]
  refine ⟨60325606547916674717388667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80434142063888899623184889 60325606547916674717388667)
  ·
    refine ⟨90488409821875012076083001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60325606547916674717388667 90488409821875012076083001)
    ·
      refine ⟨67866307366406259057062251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90488409821875012076083001 67866307366406259057062251)
      ·
        refine ⟨101799461049609388585593377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67866307366406259057062251 101799461049609388585593377)
        ·
          refine ⟨76349595787207041439195033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101799461049609388585593377 76349595787207041439195033)
          ·
            refine ⟨57262196840405281079396275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76349595787207041439195033 57262196840405281079396275)
            ·
              refine ⟨85893295260607921619094413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57262196840405281079396275 85893295260607921619094413)
              ·
                refine ⟨32209985722727970607160405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 85893295260607921619094413 32209985722727970607160405)
                ·
                  refine ⟨377460770188218405552661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 32209985722727970607160405 377460770188218405552661)
                  ·
                    rfl

theorem cell22_3307960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 3, 8].length) (baseStart_3307960 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3307960 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3307960 prefixEnd_3307960 := by exact prefixLift 3307960
  have htrace : WordTrace (prefixWord ++ tailWord_3307960) baseStart_3307960 baseEnd_3307960 := by
    simpa [prefixWord, tailWord_3307960, baseEnd_3307960] using wordTrace_append hprefix tailTrace_3307960
  have hstable : (prefixWord ++ tailWord_3307960).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3307960).length < 2 ^ (prefixWord ++ tailWord_3307960).sum := by decide
  have hdescent : baseEnd_3307960 < baseStart_3307960 := by decide
  rcases family_descends (prefixWord ++ tailWord_3307960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3307994 : List Nat := [3, 1, 1, 2, 3, 1, 3, 4, 4]
def baseStart_3307994 : Nat := 118140960795 + 3307994 * 2 ^ 59
def prefixEnd_3307994 : Nat := 4983230072969 + 3 ^ 40 * 3307994 * 2
def baseEnd_3307994 : Nat := 377464649819830153769293

theorem tailTrace_3307994 : CollatzResearch.WordTrace tailWord_3307994 prefixEnd_3307994 377464649819830153769293 := by
  unfold tailWord_3307994
  simp only [CollatzResearch.WordTrace]
  refine ⟨30163113294427543310378759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80434968785140115494343357 30163113294427543310378759)
  ·
    refine ⟨45244669941641314965568139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30163113294427543310378759 45244669941641314965568139)
    ·
      refine ⟨67867004912461972448352209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45244669941641314965568139 67867004912461972448352209)
      ·
        refine ⟨50900253684346479336264157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67867004912461972448352209 50900253684346479336264157)
        ·
          refine ⟨19087595131629929751099059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50900253684346479336264157 19087595131629929751099059)
          ·
            refine ⟨28631392697444894626648589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19087595131629929751099059 28631392697444894626648589)
            ·
              refine ⟨10736772261541835484993221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28631392697444894626648589 10736772261541835484993221)
              ·
                refine ⟨2013144799039094153436229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10736772261541835484993221 2013144799039094153436229)
                ·
                  refine ⟨377464649819830153769293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2013144799039094153436229 377464649819830153769293)
                  ·
                    rfl

theorem cell22_3307994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 3, 4, 4].length) (baseStart_3307994 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3307994 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3307994 prefixEnd_3307994 := by exact prefixLift 3307994
  have htrace : WordTrace (prefixWord ++ tailWord_3307994) baseStart_3307994 baseEnd_3307994 := by
    simpa [prefixWord, tailWord_3307994, baseEnd_3307994] using wordTrace_append hprefix tailTrace_3307994
  have hstable : (prefixWord ++ tailWord_3307994).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3307994).length < 2 ^ (prefixWord ++ tailWord_3307994).sum := by decide
  have hdescent : baseEnd_3307994 < baseStart_3307994 := by decide
  rcases family_descends (prefixWord ++ tailWord_3307994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3308007 : List Nat := [1, 1, 5, 2, 1, 1, 2, 2, 1, 6]
def baseStart_3308007 : Nat := 118140960795 + 3308007 * 2 ^ 59
def prefixEnd_3308007 : Nat := 4983230072969 + 3 ^ 40 * 3308007 * 2
def baseEnd_3308007 : Nat := 1132398399625162760732839

theorem tailTrace_3308007 : CollatzResearch.WordTrace tailWord_3308007 prefixEnd_3308007 1132398399625162760732839 := by
  unfold tailWord_3308007
  simp only [CollatzResearch.WordTrace]
  refine ⟨120652927326663076461738275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80435284884442050974492183 120652927326663076461738275)
  ·
    refine ⟨180979390989994614692607413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120652927326663076461738275 180979390989994614692607413)
    ·
      refine ⟨16966817905311995127431945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 180979390989994614692607413 16966817905311995127431945)
      ·
        refine ⟨12725113428983996345573959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16966817905311995127431945 12725113428983996345573959)
        ·
          refine ⟨19087670143475994518360939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12725113428983996345573959 19087670143475994518360939)
          ·
            refine ⟨28631505215213991777541409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19087670143475994518360939 28631505215213991777541409)
            ·
              refine ⟨21473628911410493833156057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28631505215213991777541409 21473628911410493833156057)
              ·
                refine ⟨16105221683557870374867043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21473628911410493833156057 16105221683557870374867043)
                ·
                  refine ⟨24157832525336805562300565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16105221683557870374867043 24157832525336805562300565)
                  ·
                    refine ⟨1132398399625162760732839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24157832525336805562300565 1132398399625162760732839)
                    ·
                      rfl

theorem cell22_3308007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 2, 1, 6].length) (baseStart_3308007 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3308007 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3308007 prefixEnd_3308007 := by exact prefixLift 3308007
  have htrace : WordTrace (prefixWord ++ tailWord_3308007) baseStart_3308007 baseEnd_3308007 := by
    simpa [prefixWord, tailWord_3308007, baseEnd_3308007] using wordTrace_append hprefix tailTrace_3308007
  have hstable : (prefixWord ++ tailWord_3308007).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3308007).length < 2 ^ (prefixWord ++ tailWord_3308007).sum := by decide
  have hdescent : baseEnd_3308007 < baseStart_3308007 := by decide
  rcases family_descends (prefixWord ++ tailWord_3308007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3308082 : List Nat := [3, 2, 1, 1, 2, 1, 2, 2, 1, 7]
def baseStart_3308082 : Nat := 118140960795 + 3308082 * 2 ^ 59
def prefixEnd_3308082 : Nat := 4983230072969 + 3 ^ 40 * 3308082 * 2
def baseEnd_3308082 : Nat := 1132424073657887565107609

theorem tailTrace_3308082 : CollatzResearch.WordTrace tailWord_3308082 prefixEnd_3308082 1132424073657887565107609 := by
  unfold tailWord_3308082
  simp only [CollatzResearch.WordTrace]
  refine ⟨30163915700347841067679625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80437108534260909513812333 30163915700347841067679625)
  ·
    refine ⟨22622936775260880800759719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30163915700347841067679625 22622936775260880800759719)
    ·
      refine ⟨33934405162891321201139579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22622936775260880800759719 33934405162891321201139579)
      ·
        refine ⟨50901607744336981801709369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33934405162891321201139579 50901607744336981801709369)
        ·
          refine ⟨38176205808252736351282027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50901607744336981801709369 38176205808252736351282027)
          ·
            refine ⟨57264308712379104526923041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38176205808252736351282027 57264308712379104526923041)
            ·
              refine ⟨42948231534284328395192281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57264308712379104526923041 42948231534284328395192281)
              ·
                refine ⟨32211173650713246296394211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42948231534284328395192281 32211173650713246296394211)
                ·
                  refine ⟨48316760476069869444591317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32211173650713246296394211 48316760476069869444591317)
                  ·
                    refine ⟨1132424073657887565107609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48316760476069869444591317 1132424073657887565107609)
                    ·
                      rfl

theorem cell22_3308082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 2, 1, 7].length) (baseStart_3308082 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3308082 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3308082 prefixEnd_3308082 := by exact prefixLift 3308082
  have htrace : WordTrace (prefixWord ++ tailWord_3308082) baseStart_3308082 baseEnd_3308082 := by
    simpa [prefixWord, tailWord_3308082, baseEnd_3308082] using wordTrace_append hprefix tailTrace_3308082
  have hstable : (prefixWord ++ tailWord_3308082).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3308082).length < 2 ^ (prefixWord ++ tailWord_3308082).sum := by decide
  have hdescent : baseEnd_3308082 < baseStart_3308082 := by decide
  rcases family_descends (prefixWord ++ tailWord_3308082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3308112 : List Nat := [2, 1, 1, 1, 1, 3, 2, 5, 6]
def baseStart_3308112 : Nat := 118140960795 + 3308112 * 2 ^ 59
def prefixEnd_3308112 : Nat := 4983230072969 + 3 ^ 40 * 3308112 * 2
def baseEnd_3308112 : Nat := 377478114423659162285839

theorem tailTrace_3308112 : CollatzResearch.WordTrace tailWord_3308112 prefixEnd_3308112 377478114423659162285839 := by
  unfold tailWord_3308112
  simp only [CollatzResearch.WordTrace]
  refine ⟨60328378495641339697155295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80437837994188452929540393 60328378495641339697155295)
  ·
    refine ⟨90492567743462009545732943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60328378495641339697155295 90492567743462009545732943)
    ·
      refine ⟨135738851615193014318599415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90492567743462009545732943 135738851615193014318599415)
      ·
        refine ⟨203608277422789521477899123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135738851615193014318599415 203608277422789521477899123)
        ·
          refine ⟨305412416134184282216848685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203608277422789521477899123 305412416134184282216848685)
          ·
            refine ⟨114529656050319105831318257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 305412416134184282216848685 114529656050319105831318257)
            ·
              refine ⟨85897242037739329373488693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114529656050319105831318257 85897242037739329373488693)
              ·
                refine ⟨8052866441038062128764565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 85897242037739329373488693 8052866441038062128764565)
                ·
                  refine ⟨377478114423659162285839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8052866441038062128764565 377478114423659162285839)
                  ·
                    rfl

theorem cell22_3308112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 5, 6].length) (baseStart_3308112 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3308112 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3308112 prefixEnd_3308112 := by exact prefixLift 3308112
  have htrace : WordTrace (prefixWord ++ tailWord_3308112) baseStart_3308112 baseEnd_3308112 := by
    simpa [prefixWord, tailWord_3308112, baseEnd_3308112] using wordTrace_append hprefix tailTrace_3308112
  have hstable : (prefixWord ++ tailWord_3308112).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3308112).length < 2 ^ (prefixWord ++ tailWord_3308112).sum := by decide
  have hdescent : baseEnd_3308112 < baseStart_3308112 := by decide
  rcases family_descends (prefixWord ++ tailWord_3308112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3308114 : List Nat := [3, 2, 2, 1, 2, 1, 2, 2, 3, 4]
def baseStart_3308114 : Nat := 118140960795 + 3308114 * 2 ^ 59
def prefixEnd_3308114 : Nat := 4983230072969 + 3 ^ 40 * 3308114 * 2
def baseEnd_3308114 : Nat := 1132435027911850148307511

theorem tailTrace_3308114 : CollatzResearch.WordTrace tailWord_3308114 prefixEnd_3308114 1132435027911850148307511 := by
  unfold tailWord_3308114
  simp only [CollatzResearch.WordTrace]
  refine ⟨30164207484318858433970849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80437886624850289157255597 30164207484318858433970849)
  ·
    refine ⟨22623155613239143825478137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30164207484318858433970849 22623155613239143825478137)
    ·
      refine ⟨16967366709929357869108603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22623155613239143825478137 16967366709929357869108603)
      ·
        refine ⟨25451050064894036803662905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16967366709929357869108603 25451050064894036803662905)
        ·
          refine ⟨19088287548670527602747179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25451050064894036803662905 19088287548670527602747179)
          ·
            refine ⟨28632431323005791404120769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19088287548670527602747179 28632431323005791404120769)
            ·
              refine ⟨21474323492254343553090577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28632431323005791404120769 21474323492254343553090577)
              ·
                refine ⟨16105742619190757664817933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21474323492254343553090577 16105742619190757664817933)
                ·
                  refine ⟨6039653482196534124306725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16105742619190757664817933 6039653482196534124306725)
                  ·
                    refine ⟨1132435027911850148307511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6039653482196534124306725 1132435027911850148307511)
                    ·
                      rfl

theorem cell22_3308114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 2, 3, 4].length) (baseStart_3308114 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3308114 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3308114 prefixEnd_3308114 := by exact prefixLift 3308114
  have htrace : WordTrace (prefixWord ++ tailWord_3308114) baseStart_3308114 baseEnd_3308114 := by
    simpa [prefixWord, tailWord_3308114, baseEnd_3308114] using wordTrace_append hprefix tailTrace_3308114
  have hstable : (prefixWord ++ tailWord_3308114).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3308114).length < 2 ^ (prefixWord ++ tailWord_3308114).sum := by decide
  have hdescent : baseEnd_3308114 < baseStart_3308114 := by decide
  rcases family_descends (prefixWord ++ tailWord_3308114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3308127 : List Nat := [1, 1, 2, 3, 1, 1, 1, 2, 5, 5]
def baseStart_3308127 : Nat := 118140960795 + 3308127 * 2 ^ 59
def prefixEnd_3308127 : Nat := 4983230072969 + 3 ^ 40 * 3308127 * 2
def baseEnd_3308127 : Nat := 1132439478077522447732471

theorem tailTrace_3308127 : CollatzResearch.WordTrace tailWord_3308127 prefixEnd_3308127 1132439478077522447732471 := by
  unfold tailWord_3308127
  simp only [CollatzResearch.WordTrace]
  refine ⟨120657304086228336956106635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80438202724152224637404423 120657304086228336956106635)
  ·
    refine ⟨180985956129342505434159953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120657304086228336956106635 180985956129342505434159953)
    ·
      refine ⟨135739467097006879075619965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180985956129342505434159953 135739467097006879075619965)
      ·
        refine ⟨50902300161377579653357487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135739467097006879075619965 50902300161377579653357487)
        ·
          refine ⟨76353450242066369480036231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50902300161377579653357487 76353450242066369480036231)
          ·
            refine ⟨114530175363099554220054347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76353450242066369480036231 114530175363099554220054347)
            ·
              refine ⟨171795263044649331330081521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114530175363099554220054347 171795263044649331330081521)
              ·
                refine ⟨128846447283486998497561141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 171795263044649331330081521 128846447283486998497561141)
                ·
                  refine ⟨12079354432826906109146357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 128846447283486998497561141 12079354432826906109146357)
                  ·
                    refine ⟨1132439478077522447732471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12079354432826906109146357 1132439478077522447732471)
                    ·
                      rfl

theorem cell22_3308127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 2, 5, 5].length) (baseStart_3308127 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3308127 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3308127 prefixEnd_3308127 := by exact prefixLift 3308127
  have htrace : WordTrace (prefixWord ++ tailWord_3308127) baseStart_3308127 baseEnd_3308127 := by
    simpa [prefixWord, tailWord_3308127, baseEnd_3308127] using wordTrace_append hprefix tailTrace_3308127
  have hstable : (prefixWord ++ tailWord_3308127).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3308127).length < 2 ^ (prefixWord ++ tailWord_3308127).sum := by decide
  have hdescent : baseEnd_3308127 < baseStart_3308127 := by decide
  rcases family_descends (prefixWord ++ tailWord_3308127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3308157 : List Nat := [1, 4, 1, 1, 15]
def baseStart_3308157 : Nat := 118140960795 + 3308157 * 2 ^ 59
def prefixEnd_3308157 : Nat := 4983230072969 + 3 ^ 40 * 3308157 * 2
def baseEnd_3308157 : Nat := 4660287027533384236553

theorem tailTrace_3308157 : CollatzResearch.WordTrace tailWord_3308157 prefixEnd_3308157 4660287027533384236553 := by
  unfold tailWord_3308157
  simp only [CollatzResearch.WordTrace]
  refine ⟨120658398276119652079698725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80438932184079768053132483 120658398276119652079698725)
  ·
    refine ⟨22623449676772434764943511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 120658398276119652079698725 22623449676772434764943511)
    ·
      refine ⟨33935174515158652147415267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22623449676772434764943511 33935174515158652147415267)
      ·
        refine ⟨50902761772737978221122901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33935174515158652147415267 50902761772737978221122901)
        ·
          refine ⟨4660287027533384236553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 15 50902761772737978221122901 4660287027533384236553)
          ·
            rfl

theorem cell22_3308157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 15].length) (baseStart_3308157 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3308157 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3308157 prefixEnd_3308157 := by exact prefixLift 3308157
  have htrace : WordTrace (prefixWord ++ tailWord_3308157) baseStart_3308157 baseEnd_3308157 := by
    simpa [prefixWord, tailWord_3308157, baseEnd_3308157] using wordTrace_append hprefix tailTrace_3308157
  have hstable : (prefixWord ++ tailWord_3308157).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3308157).length < 2 ^ (prefixWord ++ tailWord_3308157).sum := by decide
  have hdescent : baseEnd_3308157 < baseStart_3308157 := by decide
  rcases family_descends (prefixWord ++ tailWord_3308157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3308178 : List Nat := [3, 2, 3, 1, 2, 1, 2, 3, 2, 3]
def baseStart_3308178 : Nat := 118140960795 + 3308178 * 2 ^ 59
def prefixEnd_3308178 : Nat := 4983230072969 + 3 ^ 40 * 3308178 * 2
def baseEnd_3308178 : Nat := 1132456936419775314707315

theorem tailTrace_3308178 : CollatzResearch.WordTrace tailWord_3308178 prefixEnd_3308178 1132456936419775314707315 := by
  unfold tailWord_3308178
  simp only [CollatzResearch.WordTrace]
  refine ⟨30164791052260893166553297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80439442806029048444142125 30164791052260893166553297)
  ·
    refine ⟨22623593289195669874914973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30164791052260893166553297 22623593289195669874914973)
    ·
      refine ⟨8483847483448376203093115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22623593289195669874914973 8483847483448376203093115)
      ·
        refine ⟨12725771225172564304639673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8483847483448376203093115 12725771225172564304639673)
        ·
          refine ⟨9544328418879423228479755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12725771225172564304639673 9544328418879423228479755)
          ·
            refine ⟨14316492628319134842719633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9544328418879423228479755 14316492628319134842719633)
            ·
              refine ⟨10737369471239351132039725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14316492628319134842719633 10737369471239351132039725)
              ·
                refine ⟨4026513551714756674514897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10737369471239351132039725 4026513551714756674514897)
                ·
                  refine ⟨3019885163786067505886173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4026513551714756674514897 3019885163786067505886173)
                  ·
                    refine ⟨1132456936419775314707315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3019885163786067505886173 1132456936419775314707315)
                    ·
                      rfl

theorem cell22_3308178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 2, 3, 2, 3].length) (baseStart_3308178 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3308178 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3308178 prefixEnd_3308178 := by exact prefixLift 3308178
  have htrace : WordTrace (prefixWord ++ tailWord_3308178) baseStart_3308178 baseEnd_3308178 := by
    simpa [prefixWord, tailWord_3308178, baseEnd_3308178] using wordTrace_append hprefix tailTrace_3308178
  have hstable : (prefixWord ++ tailWord_3308178).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3308178).length < 2 ^ (prefixWord ++ tailWord_3308178).sum := by decide
  have hdescent : baseEnd_3308178 < baseStart_3308178 := by decide
  rcases family_descends (prefixWord ++ tailWord_3308178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3308193 : List Nat := [1, 2, 3, 3, 3, 2, 1, 1, 2, 4]
def baseStart_3308193 : Nat := 118140960795 + 3308193 * 2 ^ 59
def prefixEnd_3308193 : Nat := 4983230072969 + 3 ^ 40 * 3308193 * 2
def baseEnd_3308193 : Nat := 1132462071226320275582269

theorem tailTrace_3308193 : CollatzResearch.WordTrace tailWord_3308193 prefixEnd_3308193 1132462071226320275582269 := by
  unfold tailWord_3308193
  simp only [CollatzResearch.WordTrace]
  refine ⟨120659711303989230228009233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80439807535992820152006155 120659711303989230228009233)
  ·
    refine ⟨90494783477991922671006925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120659711303989230228009233 90494783477991922671006925)
    ·
      refine ⟨33935543804246971001627597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90494783477991922671006925 33935543804246971001627597)
      ·
        refine ⟨12725828926592614125610349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33935543804246971001627597 12725828926592614125610349)
        ·
          refine ⟨4772185847472230297103881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12725828926592614125610349 4772185847472230297103881)
          ·
            refine ⟨3579139385604172722827911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4772185847472230297103881 3579139385604172722827911)
            ·
              refine ⟨5368709078406259084241867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3579139385604172722827911 5368709078406259084241867)
              ·
                refine ⟨8053063617609388626362801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5368709078406259084241867 8053063617609388626362801)
                ·
                  refine ⟨6039797713207041469772101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8053063617609388626362801 6039797713207041469772101)
                  ·
                    refine ⟨1132462071226320275582269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6039797713207041469772101 1132462071226320275582269)
                    ·
                      rfl

theorem cell22_3308193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 1, 1, 2, 4].length) (baseStart_3308193 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3308193 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3308193 prefixEnd_3308193 := by exact prefixLift 3308193
  have htrace : WordTrace (prefixWord ++ tailWord_3308193) baseStart_3308193 baseEnd_3308193 := by
    simpa [prefixWord, tailWord_3308193, baseEnd_3308193] using wordTrace_append hprefix tailTrace_3308193
  have hstable : (prefixWord ++ tailWord_3308193).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3308193).length < 2 ^ (prefixWord ++ tailWord_3308193).sum := by decide
  have hdescent : baseEnd_3308193 < baseStart_3308193 := by decide
  rcases family_descends (prefixWord ++ tailWord_3308193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3308223 : List Nat := [1, 1, 2, 2, 2, 4, 2, 4, 1, 3]
def baseStart_3308223 : Nat := 118140960795 + 3308223 * 2 ^ 59
def prefixEnd_3308223 : Nat := 4983230072969 + 3 ^ 40 * 3308223 * 2
def baseEnd_3308223 : Nat := 1132472340839410197332177

theorem tailTrace_3308223 : CollatzResearch.WordTrace tailWord_3308223 prefixEnd_3308223 1132472340839410197332177 := by
  unfold tailWord_3308223
  simp only [CollatzResearch.WordTrace]
  refine ⟨120660805493880545351601323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80440536995920363567734215 120660805493880545351601323)
  ·
    refine ⟨180991208240820818027401985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120660805493880545351601323 180991208240820818027401985)
    ·
      refine ⟨135743406180615613520551489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180991208240820818027401985 135743406180615613520551489)
      ·
        refine ⟨101807554635461710140413617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135743406180615613520551489 101807554635461710140413617)
        ·
          refine ⟨76355665976596282605310213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101807554635461710140413617 76355665976596282605310213)
          ·
            refine ⟨14316687370611802988495665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76355665976596282605310213 14316687370611802988495665)
            ·
              refine ⟨10737515527958852241371749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14316687370611802988495665 10737515527958852241371749)
              ·
                refine ⟨2013284161492284795257203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10737515527958852241371749 2013284161492284795257203)
                ·
                  refine ⟨3019926242238427192885805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2013284161492284795257203 3019926242238427192885805)
                  ·
                    refine ⟨1132472340839410197332177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3019926242238427192885805 1132472340839410197332177)
                    ·
                      rfl

theorem cell22_3308223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 2, 4, 1, 3].length) (baseStart_3308223 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3308223 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3308223 prefixEnd_3308223 := by exact prefixLift 3308223
  have htrace : WordTrace (prefixWord ++ tailWord_3308223) baseStart_3308223 baseEnd_3308223 := by
    simpa [prefixWord, tailWord_3308223, baseEnd_3308223] using wordTrace_append hprefix tailTrace_3308223
  have hstable : (prefixWord ++ tailWord_3308223).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3308223).length < 2 ^ (prefixWord ++ tailWord_3308223).sum := by decide
  have hdescent : baseEnd_3308223 < baseStart_3308223 := by decide
  rcases family_descends (prefixWord ++ tailWord_3308223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3308281 : List Nat := [1, 2, 1, 3, 1, 1, 1, 8, 4]
def baseStart_3308281 : Nat := 118140960795 + 3308281 * 2 ^ 59
def prefixEnd_3308281 : Nat := 4983230072969 + 3 ^ 40 * 3308281 * 2
def baseEnd_3308281 : Nat := 377497398474905793127333

theorem tailTrace_3308281 : CollatzResearch.WordTrace tailWord_3308281 prefixEnd_3308281 377497398474905793127333 := by
  unfold tailWord_3308281
  simp only [CollatzResearch.WordTrace]
  refine ⟨120662920927670421257212697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80441947285113614171475131 120662920927670421257212697)
  ·
    refine ⟨90497190695752815942909523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120662920927670421257212697 90497190695752815942909523)
    ·
      refine ⟨135745786043629223914364285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90497190695752815942909523 135745786043629223914364285)
      ·
        refine ⟨50904669766360958967886607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135745786043629223914364285 50904669766360958967886607)
        ·
          refine ⟨76357004649541438451829911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50904669766360958967886607 76357004649541438451829911)
          ·
            refine ⟨114535506974312157677744867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76357004649541438451829911 114535506974312157677744867)
            ·
              refine ⟨171803260461468236516617301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114535506974312157677744867 171803260461468236516617301)
              ·
                refine ⟨2013319458532830896679109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 171803260461468236516617301 2013319458532830896679109)
                ·
                  refine ⟨377497398474905793127333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2013319458532830896679109 377497398474905793127333)
                  ·
                    rfl

theorem cell22_3308281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 8, 4].length) (baseStart_3308281 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3308281 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3308281 prefixEnd_3308281 := by exact prefixLift 3308281
  have htrace : WordTrace (prefixWord ++ tailWord_3308281) baseStart_3308281 baseEnd_3308281 := by
    simpa [prefixWord, tailWord_3308281, baseEnd_3308281] using wordTrace_append hprefix tailTrace_3308281
  have hstable : (prefixWord ++ tailWord_3308281).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3308281).length < 2 ^ (prefixWord ++ tailWord_3308281).sum := by decide
  have hdescent : baseEnd_3308281 < baseStart_3308281 := by decide
  rcases family_descends (prefixWord ++ tailWord_3308281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3308309 : List Nat := [1, 3, 2, 1, 2, 2, 1, 10]
def baseStart_3308309 : Nat := 118140960795 + 3308309 * 2 ^ 59
def prefixEnd_3308309 : Nat := 4983230072969 + 3 ^ 40 * 3308309 * 2
def baseEnd_3308309 : Nat := 125833531155214959964657

theorem tailTrace_3308309 : CollatzResearch.WordTrace tailWord_3308309 prefixEnd_3308309 125833531155214959964657 := by
  unfold tailWord_3308309
  simp only [CollatzResearch.WordTrace]
  refine ⟨120663942171568982039231981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80442628114379321359487987 120663942171568982039231981)
  ·
    refine ⟨45248978314338368264711993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120663942171568982039231981 45248978314338368264711993)
    ·
      refine ⟨33936733735753776198533995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45248978314338368264711993 33936733735753776198533995)
      ·
        refine ⟨50905100603630664297800993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33936733735753776198533995 50905100603630664297800993)
        ·
          refine ⟨38178825452722998223350745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50905100603630664297800993 38178825452722998223350745)
          ·
            refine ⟨28634119089542248667513059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38178825452722998223350745 28634119089542248667513059)
            ·
              refine ⟨42951178634313373001269589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28634119089542248667513059 42951178634313373001269589)
              ·
                refine ⟨125833531155214959964657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 42951178634313373001269589 125833531155214959964657)
                ·
                  rfl

theorem cell22_3308309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 10].length) (baseStart_3308309 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3308309 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3308309 prefixEnd_3308309 := by exact prefixLift 3308309
  have htrace : WordTrace (prefixWord ++ tailWord_3308309) baseStart_3308309 baseEnd_3308309 := by
    simpa [prefixWord, tailWord_3308309, baseEnd_3308309] using wordTrace_append hprefix tailTrace_3308309
  have hstable : (prefixWord ++ tailWord_3308309).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3308309).length < 2 ^ (prefixWord ++ tailWord_3308309).sum := by decide
  have hdescent : baseEnd_3308309 < baseStart_3308309 := by decide
  rcases family_descends (prefixWord ++ tailWord_3308309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3308317 : List Nat := [1, 4, 2, 4, 1, 1, 3, 1, 1, 4]
def baseStart_3308317 : Nat := 118140960795 + 3308317 * 2 ^ 59
def prefixEnd_3308317 : Nat := 4983230072969 + 3 ^ 40 * 3308317 * 2
def baseEnd_3308317 : Nat := 1132504518960425285481889

theorem tailTrace_3308317 : CollatzResearch.WordTrace tailWord_3308317 prefixEnd_3308317 1132504518960425285481889 := by
  unfold tailWord_3308317
  simp only [CollatzResearch.WordTrace]
  refine ⟨120664233955539999405523205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80442822637026666270348803 120664233955539999405523205)
  ·
    refine ⟨22624543866663749888535601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 120664233955539999405523205 22624543866663749888535601)
    ·
      refine ⟨16968407899997812416401701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22624543866663749888535601 16968407899997812416401701)
      ·
        refine ⟨3181576481249589828075319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16968407899997812416401701 3181576481249589828075319)
        ·
          refine ⟨4772364721874384742112979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3181576481249589828075319 4772364721874384742112979)
          ·
            refine ⟨7158547082811577113169469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4772364721874384742112979 7158547082811577113169469)
            ·
              refine ⟨2684455156054341417438551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7158547082811577113169469 2684455156054341417438551)
              ·
                refine ⟨4026682734081512126157827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2684455156054341417438551 4026682734081512126157827)
                ·
                  refine ⟨6040024101122268189236741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4026682734081512126157827 6040024101122268189236741)
                  ·
                    refine ⟨1132504518960425285481889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6040024101122268189236741 1132504518960425285481889)
                    ·
                      rfl

theorem cell22_3308317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 3, 1, 1, 4].length) (baseStart_3308317 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3308317 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3308317 prefixEnd_3308317 := by exact prefixLift 3308317
  have htrace : WordTrace (prefixWord ++ tailWord_3308317) baseStart_3308317 baseEnd_3308317 := by
    simpa [prefixWord, tailWord_3308317, baseEnd_3308317] using wordTrace_append hprefix tailTrace_3308317
  have hstable : (prefixWord ++ tailWord_3308317).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3308317).length < 2 ^ (prefixWord ++ tailWord_3308317).sum := by decide
  have hdescent : baseEnd_3308317 < baseStart_3308317 := by decide
  rcases family_descends (prefixWord ++ tailWord_3308317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3308375 : List Nat := [1, 1, 3, 2, 4, 1, 1, 5, 1, 3]
def baseStart_3308375 : Nat := 118140960795 + 3308375 * 2 ^ 59
def prefixEnd_3308375 : Nat := 4983230072969 + 3 ^ 40 * 3308375 * 2
def baseEnd_3308375 : Nat := 1132524373545732467531711

theorem tailTrace_3308375 : CollatzResearch.WordTrace tailWord_3308375 prefixEnd_3308375 1132524373545732467531711 := by
  unfold tailWord_3308375
  simp only [CollatzResearch.WordTrace]
  refine ⟨120666349389329875311134579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80444232926219916874089719 120666349389329875311134579)
  ·
    refine ⟨180999524083994812966701869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120666349389329875311134579 180999524083994812966701869)
    ·
      refine ⟨67874821531498054862513201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 180999524083994812966701869 67874821531498054862513201)
      ·
        refine ⟨50906116148623541146884901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67874821531498054862513201 50906116148623541146884901)
        ·
          refine ⟨9544896777866913965040919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50906116148623541146884901 9544896777866913965040919)
          ·
            refine ⟨14317345166800370947561379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9544896777866913965040919 14317345166800370947561379)
            ·
              refine ⟨21476017750200556421342069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14317345166800370947561379 21476017750200556421342069)
              ·
                refine ⟨2013376664081302164500819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21476017750200556421342069 2013376664081302164500819)
                ·
                  refine ⟨3020064996121953246751229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2013376664081302164500819 3020064996121953246751229)
                  ·
                    refine ⟨1132524373545732467531711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3020064996121953246751229 1132524373545732467531711)
                    ·
                      rfl

theorem cell22_3308375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 5, 1, 3].length) (baseStart_3308375 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3308375 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3308375 prefixEnd_3308375 := by exact prefixLift 3308375
  have htrace : WordTrace (prefixWord ++ tailWord_3308375) baseStart_3308375 baseEnd_3308375 := by
    simpa [prefixWord, tailWord_3308375, baseEnd_3308375] using wordTrace_append hprefix tailTrace_3308375
  have hstable : (prefixWord ++ tailWord_3308375).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3308375).length < 2 ^ (prefixWord ++ tailWord_3308375).sum := by decide
  have hdescent : baseEnd_3308375 < baseStart_3308375 := by decide
  rcases family_descends (prefixWord ++ tailWord_3308375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3308388 : List Nat := [2, 3, 1, 1, 4, 1, 3, 2, 5]
def baseStart_3308388 : Nat := 118140960795 + 3308388 * 2 ^ 59
def prefixEnd_3308388 : Nat := 4983230072969 + 3 ^ 40 * 3308388 * 2
def baseEnd_3308388 : Nat := 377509607903801588985557

theorem tailTrace_3308388 : CollatzResearch.WordTrace tailWord_3308388 prefixEnd_3308388 377509607903801588985557 := by
  unfold tailWord_3308388
  simp only [CollatzResearch.WordTrace]
  refine ⟨60333411769141389265678909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80444549025521852354238545 60333411769141389265678909)
  ·
    refine ⟨22625029413428020974629591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60333411769141389265678909 22625029413428020974629591)
    ·
      refine ⟨33937544120142031461944387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22625029413428020974629591 33937544120142031461944387)
      ·
        refine ⟨50906316180213047192916581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33937544120142031461944387 50906316180213047192916581)
        ·
          refine ⟨9544934283789946348671859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50906316180213047192916581 9544934283789946348671859)
          ·
            refine ⟨14317401425684919523007789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9544934283789946348671859 14317401425684919523007789)
            ·
              refine ⟨5369025534631844821127921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14317401425684919523007789 5369025534631844821127921)
              ·
                refine ⟨4026769150973883615845941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5369025534631844821127921 4026769150973883615845941)
                ·
                  refine ⟨377509607903801588985557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4026769150973883615845941 377509607903801588985557)
                  ·
                    rfl

theorem cell22_3308388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 3, 2, 5].length) (baseStart_3308388 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3308388 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3308388 prefixEnd_3308388 := by exact prefixLift 3308388
  have htrace : WordTrace (prefixWord ++ tailWord_3308388) baseStart_3308388 baseEnd_3308388 := by
    simpa [prefixWord, tailWord_3308388, baseEnd_3308388] using wordTrace_append hprefix tailTrace_3308388
  have hstable : (prefixWord ++ tailWord_3308388).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3308388).length < 2 ^ (prefixWord ++ tailWord_3308388).sum := by decide
  have hdescent : baseEnd_3308388 < baseStart_3308388 := by decide
  rcases family_descends (prefixWord ++ tailWord_3308388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3308405 : List Nat := [1, 3, 4, 1, 1, 3, 3, 1, 5]
def baseStart_3308405 : Nat := 118140960795 + 3308405 * 2 ^ 59
def prefixEnd_3308405 : Nat := 4983230072969 + 3 ^ 40 * 3308405 * 2
def baseEnd_3308405 : Nat := 377511547719607463093873

theorem tailTrace_3308405 : CollatzResearch.WordTrace tailWord_3308405 prefixEnd_3308405 377511547719607463093873 := by
  unfold tailWord_3308405
  simp only [CollatzResearch.WordTrace]
  refine ⟨120667443579221190434726669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80444962386147460289817779 120667443579221190434726669)
  ·
    refine ⟨45250291342207946413022501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120667443579221190434726669 45250291342207946413022501)
    ·
      refine ⟨8484429626663989952441719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45250291342207946413022501 8484429626663989952441719)
      ·
        refine ⟨12726644439995984928662579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8484429626663989952441719 12726644439995984928662579)
        ·
          refine ⟨19089966659993977392993869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12726644439995984928662579 19089966659993977392993869)
          ·
            refine ⟨7158737497497741522372701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19089966659993977392993869 7158737497497741522372701)
            ·
              refine ⟨2684526561561653070889763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7158737497497741522372701 2684526561561653070889763)
              ·
                refine ⟨4026789842342479606334645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2684526561561653070889763 4026789842342479606334645)
                ·
                  refine ⟨377511547719607463093873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4026789842342479606334645 377511547719607463093873)
                  ·
                    rfl

theorem cell22_3308405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 3, 1, 5].length) (baseStart_3308405 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3308405 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3308405 prefixEnd_3308405 := by exact prefixLift 3308405
  have htrace : WordTrace (prefixWord ++ tailWord_3308405) baseStart_3308405 baseEnd_3308405 := by
    simpa [prefixWord, tailWord_3308405, baseEnd_3308405] using wordTrace_append hprefix tailTrace_3308405
  have hstable : (prefixWord ++ tailWord_3308405).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3308405).length < 2 ^ (prefixWord ++ tailWord_3308405).sum := by decide
  have hdescent : baseEnd_3308405 < baseStart_3308405 := by decide
  rcases family_descends (prefixWord ++ tailWord_3308405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3308448 : List Nat := [2, 1, 1, 4, 1, 1, 4, 1, 4, 3]
def baseStart_3308448 : Nat := 118140960795 + 3308448 * 2 ^ 59
def prefixEnd_3308448 : Nat := 4983230072969 + 3 ^ 40 * 3308448 * 2
def baseEnd_3308448 : Nat := 1132549362937584610456487

theorem tailTrace_3308448 : CollatzResearch.WordTrace tailWord_3308448 prefixEnd_3308448 1132549362937584610456487 := by
  unfold tailWord_3308448
  simp only [CollatzResearch.WordTrace]
  refine ⟨60334505959032704389270999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80446007945376939185694665 60334505959032704389270999)
  ·
    refine ⟨90501758938549056583906499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60334505959032704389270999 90501758938549056583906499)
    ·
      refine ⟨135752638407823584875859749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90501758938549056583906499 135752638407823584875859749)
      ·
        refine ⟨25453619701466922164223703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 135752638407823584875859749 25453619701466922164223703)
        ·
          refine ⟨38180429552200383246335555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25453619701466922164223703 38180429552200383246335555)
          ·
            refine ⟨57270644328300574869503333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38180429552200383246335555 57270644328300574869503333)
            ·
              refine ⟨10738245811556357788031875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57270644328300574869503333 10738245811556357788031875)
              ·
                refine ⟨16107368717334536682047813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10738245811556357788031875 16107368717334536682047813)
                ·
                  refine ⟨3020131634500225627883965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16107368717334536682047813 3020131634500225627883965)
                  ·
                    refine ⟨1132549362937584610456487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3020131634500225627883965 1132549362937584610456487)
                    ·
                      rfl

theorem cell22_3308448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4, 1, 4, 3].length) (baseStart_3308448 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3308448 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3308448 prefixEnd_3308448 := by exact prefixLift 3308448
  have htrace : WordTrace (prefixWord ++ tailWord_3308448) baseStart_3308448 baseEnd_3308448 := by
    simpa [prefixWord, tailWord_3308448, baseEnd_3308448] using wordTrace_append hprefix tailTrace_3308448
  have hstable : (prefixWord ++ tailWord_3308448).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3308448).length < 2 ^ (prefixWord ++ tailWord_3308448).sum := by decide
  have hdescent : baseEnd_3308448 < baseStart_3308448 := by decide
  rcases family_descends (prefixWord ++ tailWord_3308448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3308450 : List Nat := [3, 3, 1, 2, 2, 3, 1, 1, 6]
def baseStart_3308450 : Nat := 118140960795 + 3308450 * 2 ^ 59
def prefixEnd_3308450 : Nat := 4983230072969 + 3 ^ 40 * 3308450 * 2
def baseEnd_3308450 : Nat := 377516682526152423968827

theorem tailTrace_3308450 : CollatzResearch.WordTrace tailWord_3308450 prefixEnd_3308450 377516682526152423968827 := by
  unfold tailWord_3308450
  simp only [CollatzResearch.WordTrace]
  refine ⟨30167271216014540780028701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80446056576038775413409869 30167271216014540780028701)
  ·
    refine ⟨11312726706005452792510763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30167271216014540780028701 11312726706005452792510763)
    ·
      refine ⟨16969090059008179188766145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11312726706005452792510763 16969090059008179188766145)
      ·
        refine ⟨12726817544256134391574609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16969090059008179188766145 12726817544256134391574609)
        ·
          refine ⟨9545113158192100793680957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12726817544256134391574609 9545113158192100793680957)
          ·
            refine ⟨3579417434322037797630359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9545113158192100793680957 3579417434322037797630359)
            ·
              refine ⟨5369126151483056696445539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3579417434322037797630359 5369126151483056696445539)
              ·
                refine ⟨8053689227224585044668309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5369126151483056696445539 8053689227224585044668309)
                ·
                  refine ⟨377516682526152423968827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8053689227224585044668309 377516682526152423968827)
                  ·
                    rfl

theorem cell22_3308450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 1, 1, 6].length) (baseStart_3308450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3308450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3308450 prefixEnd_3308450 := by exact prefixLift 3308450
  have htrace : WordTrace (prefixWord ++ tailWord_3308450) baseStart_3308450 baseEnd_3308450 := by
    simpa [prefixWord, tailWord_3308450, baseEnd_3308450] using wordTrace_append hprefix tailTrace_3308450
  have hstable : (prefixWord ++ tailWord_3308450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3308450).length < 2 ^ (prefixWord ++ tailWord_3308450).sum := by decide
  have hdescent : baseEnd_3308450 < baseStart_3308450 := by decide
  rcases family_descends (prefixWord ++ tailWord_3308450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3308568 : List Nat := [2, 1, 2, 3, 2, 2, 1, 3, 6]
def baseStart_3308568 : Nat := 118140960795 + 3308568 * 2 ^ 59
def prefixEnd_3308568 : Nat := 4983230072969 + 3 ^ 40 * 3308568 * 2
def baseEnd_3308568 : Nat := 377530147129981432485373

theorem tailTrace_3308568 : CollatzResearch.WordTrace tailWord_3308568 prefixEnd_3308568 377530147129981432485373 := by
  unfold tailWord_3308568
  simp only [CollatzResearch.WordTrace]
  refine ⟨60336694338815334636455179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80448925785087112848606905 60336694338815334636455179)
  ·
    refine ⟨90505041508223001954682769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60336694338815334636455179 90505041508223001954682769)
    ·
      refine ⟨67878781131167251466012077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90505041508223001954682769 67878781131167251466012077)
      ·
        refine ⟨25454542924187719299754529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67878781131167251466012077 25454542924187719299754529)
        ·
          refine ⟨19090907193140789474815897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25454542924187719299754529 19090907193140789474815897)
          ·
            refine ⟨14318180394855592106111923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19090907193140789474815897 14318180394855592106111923)
            ·
              refine ⟨21477270592283388159167885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14318180394855592106111923 21477270592283388159167885)
              ·
                refine ⟨8053976472106270559687957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21477270592283388159167885 8053976472106270559687957)
                ·
                  refine ⟨377530147129981432485373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8053976472106270559687957 377530147129981432485373)
                  ·
                    rfl

theorem cell22_3308568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 3, 6].length) (baseStart_3308568 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3308568 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3308568 prefixEnd_3308568 := by exact prefixLift 3308568
  have htrace : WordTrace (prefixWord ++ tailWord_3308568) baseStart_3308568 baseEnd_3308568 := by
    simpa [prefixWord, tailWord_3308568, baseEnd_3308568] using wordTrace_append hprefix tailTrace_3308568
  have hstable : (prefixWord ++ tailWord_3308568).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3308568).length < 2 ^ (prefixWord ++ tailWord_3308568).sum := by decide
  have hdescent : baseEnd_3308568 < baseStart_3308568 := by decide
  rcases family_descends (prefixWord ++ tailWord_3308568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3308600 : List Nat := [2, 1, 2, 1, 5, 1, 1, 2, 4, 3]
def baseStart_3308600 : Nat := 118140960795 + 3308600 * 2 ^ 59
def prefixEnd_3308600 : Nat := 4983230072969 + 3 ^ 40 * 3308600 * 2
def baseEnd_3308600 : Nat := 1132601395643906880656021

theorem tailTrace_3308600 : CollatzResearch.WordTrace tailWord_3308600 prefixEnd_3308600 1132601395643906880656021 := by
  unfold tailWord_3308600
  simp only [CollatzResearch.WordTrace]
  refine ⟨60337277906757369369037627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80449703875676492492050169 60337277906757369369037627)
  ·
    refine ⟨90505916860136054053556441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60337277906757369369037627 90505916860136054053556441)
    ·
      refine ⟨67879437645102040540167331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90505916860136054053556441 67879437645102040540167331)
      ·
        refine ⟨101819156467653060810250997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67879437645102040540167331 101819156467653060810250997)
        ·
          refine ⟨9545545918842474450961031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 101819156467653060810250997 9545545918842474450961031)
          ·
            refine ⟨14318318878263711676441547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9545545918842474450961031 14318318878263711676441547)
            ·
              refine ⟨21477478317395567514662321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14318318878263711676441547 21477478317395567514662321)
              ·
                refine ⟨16108108738046675635996741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21477478317395567514662321 16108108738046675635996741)
                ·
                  refine ⟨3020270388383751681749389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16108108738046675635996741 3020270388383751681749389)
                  ·
                    refine ⟨1132601395643906880656021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3020270388383751681749389 1132601395643906880656021)
                    ·
                      rfl

theorem cell22_3308600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 2, 4, 3].length) (baseStart_3308600 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3308600 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3308600 prefixEnd_3308600 := by exact prefixLift 3308600
  have htrace : WordTrace (prefixWord ++ tailWord_3308600) baseStart_3308600 baseEnd_3308600 := by
    simpa [prefixWord, tailWord_3308600, baseEnd_3308600] using wordTrace_append hprefix tailTrace_3308600
  have hstable : (prefixWord ++ tailWord_3308600).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3308600).length < 2 ^ (prefixWord ++ tailWord_3308600).sum := by decide
  have hdescent : baseEnd_3308600 < baseStart_3308600 := by decide
  rcases family_descends (prefixWord ++ tailWord_3308600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3308615 : List Nat := [1, 1, 4, 1, 3, 3, 1, 2, 2, 4]
def baseStart_3308615 : Nat := 118140960795 + 3308615 * 2 ^ 59
def prefixEnd_3308615 : Nat := 4983230072969 + 3 ^ 40 * 3308615 * 2
def baseEnd_3308615 : Nat := 1132606530450451841530975

theorem tailTrace_3308615 : CollatzResearch.WordTrace tailWord_3308615 prefixEnd_3308615 1132606530450451841530975 := by
  unfold tailWord_3308615
  simp only [CollatzResearch.WordTrace]
  refine ⟨120675102908460396299871299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80450068605640264199914199 120675102908460396299871299)
  ·
    refine ⟨181012654362690594449806949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120675102908460396299871299 181012654362690594449806949)
    ·
      refine ⟨33939872693004486459338803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 181012654362690594449806949 33939872693004486459338803)
      ·
        refine ⟨50909809039506729689008205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33939872693004486459338803 50909809039506729689008205)
        ·
          refine ⟨19091178389815023633378077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50909809039506729689008205 19091178389815023633378077)
          ·
            refine ⟨7159191896180633862516779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19091178389815023633378077 7159191896180633862516779)
            ·
              refine ⟨10738787844270950793775169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7159191896180633862516779 10738787844270950793775169)
              ·
                refine ⟨8054090883203213095331377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10738787844270950793775169 8054090883203213095331377)
                ·
                  refine ⟨6040568162402409821498533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8054090883203213095331377 6040568162402409821498533)
                  ·
                    refine ⟨1132606530450451841530975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6040568162402409821498533 1132606530450451841530975)
                    ·
                      rfl

theorem cell22_3308615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 1, 2, 2, 4].length) (baseStart_3308615 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3308615 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3308615 prefixEnd_3308615 := by exact prefixLift 3308615
  have htrace : WordTrace (prefixWord ++ tailWord_3308615) baseStart_3308615 baseEnd_3308615 := by
    simpa [prefixWord, tailWord_3308615, baseEnd_3308615] using wordTrace_append hprefix tailTrace_3308615
  have hstable : (prefixWord ++ tailWord_3308615).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3308615).length < 2 ^ (prefixWord ++ tailWord_3308615).sum := by decide
  have hdescent : baseEnd_3308615 < baseStart_3308615 := by decide
  rcases family_descends (prefixWord ++ tailWord_3308615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3308645 : List Nat := [1, 3, 1, 3, 2, 1, 2, 1, 5, 3]
def baseStart_3308645 : Nat := 118140960795 + 3308645 * 2 ^ 59
def prefixEnd_3308645 : Nat := 4983230072969 + 3 ^ 40 * 3308645 * 2
def baseEnd_3308645 : Nat := 1132616800063541763280883

theorem tailTrace_3308645 : CollatzResearch.WordTrace tailWord_3308645 prefixEnd_3308645 1132616800063541763280883 := by
  unfold tailWord_3308645
  simp only [CollatzResearch.WordTrace]
  refine ⟨120676197098351711423463389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80450798065567807615642259 120676197098351711423463389)
  ·
    refine ⟨45253573911881891783798771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120676197098351711423463389 45253573911881891783798771)
    ·
      refine ⟨67880360867822837675698157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45253573911881891783798771 67880360867822837675698157)
      ·
        refine ⟨25455135325433564128386809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67880360867822837675698157 25455135325433564128386809)
        ·
          refine ⟨19091351494075173096290107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25455135325433564128386809 19091351494075173096290107)
          ·
            refine ⟨28637027241112759644435161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19091351494075173096290107 28637027241112759644435161)
            ·
              refine ⟨21477770430834569733326371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28637027241112759644435161 21477770430834569733326371)
              ·
                refine ⟨32216655646251854599989557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21477770430834569733326371 32216655646251854599989557)
                ·
                  refine ⟨3020311466836111368749021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32216655646251854599989557 3020311466836111368749021)
                  ·
                    refine ⟨1132616800063541763280883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3020311466836111368749021 1132616800063541763280883)
                    ·
                      rfl

theorem cell22_3308645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 1, 5, 3].length) (baseStart_3308645 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3308645 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3308645 prefixEnd_3308645 := by exact prefixLift 3308645
  have htrace : WordTrace (prefixWord ++ tailWord_3308645) baseStart_3308645 baseEnd_3308645 := by
    simpa [prefixWord, tailWord_3308645, baseEnd_3308645] using wordTrace_append hprefix tailTrace_3308645
  have hstable : (prefixWord ++ tailWord_3308645).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3308645).length < 2 ^ (prefixWord ++ tailWord_3308645).sum := by decide
  have hdescent : baseEnd_3308645 < baseStart_3308645 := by decide
  rcases family_descends (prefixWord ++ tailWord_3308645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3308670 : List Nat := [4, 2, 4, 1, 1, 2, 2, 2, 4]
def baseStart_3308670 : Nat := 118140960795 + 3308670 * 2 ^ 59
def prefixEnd_3308670 : Nat := 4983230072969 + 3 ^ 40 * 3308670 * 2
def baseEnd_3308670 : Nat := 377541786024816677135269

theorem tailTrace_3308670 : CollatzResearch.WordTrace tailWord_3308670 prefixEnd_3308670 377541786024816677135269 := by
  unfold tailWord_3308670
  simp only [CollatzResearch.WordTrace]
  refine ⟨15084638615407642586640433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80451405948840760462082309 15084638615407642586640433)
  ·
    refine ⟨11313478961555731939980325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15084638615407642586640433 11313478961555731939980325)
    ·
      refine ⟨2121277305291699738746311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11313478961555731939980325 2121277305291699738746311)
      ·
        refine ⟨3181915957937549608119467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2121277305291699738746311 3181915957937549608119467)
        ·
          refine ⟨4772873936906324412179201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3181915957937549608119467 4772873936906324412179201)
          ·
            refine ⟨3579655452679743309134401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4772873936906324412179201 3579655452679743309134401)
            ·
              refine ⟨2684741589509807481850801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3579655452679743309134401 2684741589509807481850801)
              ·
                refine ⟨2013556192132355611388101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2684741589509807481850801 2013556192132355611388101)
                ·
                  refine ⟨377541786024816677135269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2013556192132355611388101 377541786024816677135269)
                  ·
                    rfl

theorem cell22_3308670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 2, 2, 4].length) (baseStart_3308670 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3308670 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3308670 prefixEnd_3308670 := by exact prefixLift 3308670
  have htrace : WordTrace (prefixWord ++ tailWord_3308670) baseStart_3308670 baseEnd_3308670 := by
    simpa [prefixWord, tailWord_3308670, baseEnd_3308670] using wordTrace_append hprefix tailTrace_3308670
  have hstable : (prefixWord ++ tailWord_3308670).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3308670).length < 2 ^ (prefixWord ++ tailWord_3308670).sum := by decide
  have hdescent : baseEnd_3308670 < baseStart_3308670 := by decide
  rcases family_descends (prefixWord ++ tailWord_3308670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3308675 : List Nat := [1, 1, 1, 3, 3, 2, 4, 2, 5]
def baseStart_3308675 : Nat := 118140960795 + 3308675 * 2 ^ 59
def prefixEnd_3308675 : Nat := 4983230072969 + 3 ^ 40 * 3308675 * 2
def baseEnd_3308675 : Nat := 377542356558877228343597

theorem tailTrace_3308675 : CollatzResearch.WordTrace tailWord_3308675 prefixEnd_3308675 377542356558877228343597 := by
  unfold tailWord_3308675
  simp only [CollatzResearch.WordTrace]
  refine ⟨120677291288243026547055479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80451527525495351031370319 120677291288243026547055479)
  ·
    refine ⟨181015936932364539820583219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120677291288243026547055479 181015936932364539820583219)
    ·
      refine ⟨271523905398546809730874829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181015936932364539820583219 271523905398546809730874829)
      ·
        refine ⟨101821464524455053649078061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 271523905398546809730874829 101821464524455053649078061)
        ·
          refine ⟨38183049196670645118404273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101821464524455053649078061 38183049196670645118404273)
          ·
            refine ⟨28637286897502983838803205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38183049196670645118404273 28637286897502983838803205)
            ·
              refine ⟨5369491293281809469775601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28637286897502983838803205 5369491293281809469775601)
              ·
                refine ⟨4027118469961357102331701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5369491293281809469775601 4027118469961357102331701)
                ·
                  refine ⟨377542356558877228343597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4027118469961357102331701 377542356558877228343597)
                  ·
                    rfl

theorem cell22_3308675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 4, 2, 5].length) (baseStart_3308675 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3308675 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3308675 prefixEnd_3308675 := by exact prefixLift 3308675
  have htrace : WordTrace (prefixWord ++ tailWord_3308675) baseStart_3308675 baseEnd_3308675 := by
    simpa [prefixWord, tailWord_3308675, baseEnd_3308675] using wordTrace_append hprefix tailTrace_3308675
  have hstable : (prefixWord ++ tailWord_3308675).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3308675).length < 2 ^ (prefixWord ++ tailWord_3308675).sum := by decide
  have hdescent : baseEnd_3308675 < baseStart_3308675 := by decide
  rcases family_descends (prefixWord ++ tailWord_3308675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3308690 : List Nat := [3, 2, 3, 1, 1, 2, 1, 1, 1, 7]
def baseStart_3308690 : Nat := 118140960795 + 3308690 * 2 ^ 59
def prefixEnd_3308690 : Nat := 4983230072969 + 3 ^ 40 * 3308690 * 2
def baseEnd_3308690 : Nat := 1132632204483176645905745

theorem tailTrace_3308690 : CollatzResearch.WordTrace tailWord_3308690 prefixEnd_3308690 1132632204483176645905745 := by
  unfold tailWord_3308690
  simp only [CollatzResearch.WordTrace]
  refine ⟨30169459595797171027212881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80451892255459122739234349 30169459595797171027212881)
  ·
    refine ⟨22627094696847878270409661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30169459595797171027212881 22627094696847878270409661)
    ·
      refine ⟨8485160511317954351403623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22627094696847878270409661 8485160511317954351403623)
      ·
        refine ⟨12727740766976931527105435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8485160511317954351403623 12727740766976931527105435)
        ·
          refine ⟨19091611150465397290658153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12727740766976931527105435 19091611150465397290658153)
          ·
            refine ⟨14318708362849047967993615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19091611150465397290658153 14318708362849047967993615)
            ·
              refine ⟨21478062544273571951990423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14318708362849047967993615 21478062544273571951990423)
              ·
                refine ⟨32217093816410357927985635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21478062544273571951990423 32217093816410357927985635)
                ·
                  refine ⟨48325640724615536891978453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32217093816410357927985635 48325640724615536891978453)
                  ·
                    refine ⟨1132632204483176645905745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48325640724615536891978453 1132632204483176645905745)
                    ·
                      rfl

theorem cell22_3308690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 1, 1, 7].length) (baseStart_3308690 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3308690 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3308690 prefixEnd_3308690 := by exact prefixLift 3308690
  have htrace : WordTrace (prefixWord ++ tailWord_3308690) baseStart_3308690 baseEnd_3308690 := by
    simpa [prefixWord, tailWord_3308690, baseEnd_3308690] using wordTrace_append hprefix tailTrace_3308690
  have hstable : (prefixWord ++ tailWord_3308690).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3308690).length < 2 ^ (prefixWord ++ tailWord_3308690).sum := by decide
  have hdescent : baseEnd_3308690 < baseStart_3308690 := by decide
  rcases family_descends (prefixWord ++ tailWord_3308690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3308705 : List Nat := [1, 2, 3, 3, 1, 1, 1, 3, 3, 4]
def baseStart_3308705 : Nat := 118140960795 + 3308705 * 2 ^ 59
def prefixEnd_3308705 : Nat := 4983230072969 + 3 ^ 40 * 3308705 * 2
def baseEnd_3308705 : Nat := 1132637339289721606780699

theorem tailTrace_3308705 : CollatzResearch.WordTrace tailWord_3308705 prefixEnd_3308705 1132637339289721606780699 := by
  unfold tailWord_3308705
  simp only [CollatzResearch.WordTrace]
  refine ⟨120678385478134341670647569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80452256985422894447098379 120678385478134341670647569)
  ·
    refine ⟨90508789108600756252985677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120678385478134341670647569 90508789108600756252985677)
    ·
      refine ⟨33940795915725283594869629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90508789108600756252985677 33940795915725283594869629)
      ·
        refine ⟨12727798468396981348076111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33940795915725283594869629 12727798468396981348076111)
        ·
          refine ⟨19091697702595472022114167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12727798468396981348076111 19091697702595472022114167)
          ·
            refine ⟨28637546553893208033171251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19091697702595472022114167 28637546553893208033171251)
            ·
              refine ⟨42956319830839812049756877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28637546553893208033171251 42956319830839812049756877)
              ·
                refine ⟨16108619936564929518658829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42956319830839812049756877 16108619936564929518658829)
                ·
                  refine ⟨6040732476211848569497061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16108619936564929518658829 6040732476211848569497061)
                  ·
                    refine ⟨1132637339289721606780699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6040732476211848569497061 1132637339289721606780699)
                    ·
                      rfl

theorem cell22_3308705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 3, 3, 4].length) (baseStart_3308705 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3308705 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3308705 prefixEnd_3308705 := by exact prefixLift 3308705
  have htrace : WordTrace (prefixWord ++ tailWord_3308705) baseStart_3308705 baseEnd_3308705 := by
    simpa [prefixWord, tailWord_3308705, baseEnd_3308705] using wordTrace_append hprefix tailTrace_3308705
  have hstable : (prefixWord ++ tailWord_3308705).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3308705).length < 2 ^ (prefixWord ++ tailWord_3308705).sum := by decide
  have hdescent : baseEnd_3308705 < baseStart_3308705 := by decide
  rcases family_descends (prefixWord ++ tailWord_3308705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3308722 : List Nat := [3, 2, 1, 1, 1, 5, 1, 3, 1, 4]
def baseStart_3308722 : Nat := 118140960795 + 3308722 * 2 ^ 59
def prefixEnd_3308722 : Nat := 4983230072969 + 3 ^ 40 * 3308722 * 2
def baseEnd_3308722 : Nat := 1132643158737139229105647

theorem tailTrace_3308722 : CollatzResearch.WordTrace tailWord_3308722 prefixEnd_3308722 1132643158737139229105647 := by
  unfold tailWord_3308722
  simp only [CollatzResearch.WordTrace]
  refine ⟨30169751379768188393504105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80452670346048502382677613 30169751379768188393504105)
  ·
    refine ⟨22627313534826141295128079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30169751379768188393504105 22627313534826141295128079)
    ·
      refine ⟨33940970302239211942692119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22627313534826141295128079 33940970302239211942692119)
      ·
        refine ⟨50911455453358817914038179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33940970302239211942692119 50911455453358817914038179)
        ·
          refine ⟨76367183180038226871057269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50911455453358817914038179 76367183180038226871057269)
          ·
            refine ⟨7159423423128583769161619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 76367183180038226871057269 7159423423128583769161619)
            ·
              refine ⟨10739135134692875653742429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7159423423128583769161619 10739135134692875653742429)
              ·
                refine ⟨4027175675509828370153411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10739135134692875653742429 4027175675509828370153411)
                ·
                  refine ⟨6040763513264742555230117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4027175675509828370153411 6040763513264742555230117)
                  ·
                    refine ⟨1132643158737139229105647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6040763513264742555230117 1132643158737139229105647)
                    ·
                      rfl

theorem cell22_3308722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 1, 3, 1, 4].length) (baseStart_3308722 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3308722 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3308722 prefixEnd_3308722 := by exact prefixLift 3308722
  have htrace : WordTrace (prefixWord ++ tailWord_3308722) baseStart_3308722 baseEnd_3308722 := by
    simpa [prefixWord, tailWord_3308722, baseEnd_3308722] using wordTrace_append hprefix tailTrace_3308722
  have hstable : (prefixWord ++ tailWord_3308722).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3308722).length < 2 ^ (prefixWord ++ tailWord_3308722).sum := by decide
  have hdescent : baseEnd_3308722 < baseStart_3308722 := by decide
  rcases family_descends (prefixWord ++ tailWord_3308722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3308737 : List Nat := [1, 2, 6, 1, 1, 1, 1, 3, 6]
def baseStart_3308737 : Nat := 118140960795 + 3308737 * 2 ^ 59
def prefixEnd_3308737 : Nat := 4983230072969 + 3 ^ 40 * 3308737 * 2
def baseEnd_3308737 : Nat := 377549431181228063326867

theorem tailTrace_3308737 : CollatzResearch.WordTrace tailWord_3308737 prefixEnd_3308737 377549431181228063326867 := by
  unfold tailWord_3308737
  simp only [CollatzResearch.WordTrace]
  refine ⟨120679552614018411135812465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80453035076012274090541643 120679552614018411135812465)
  ·
    refine ⟨90509664460513808351859349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120679552614018411135812465 90509664460513808351859349)
    ·
      refine ⟨4242640521586584766493407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 90509664460513808351859349 4242640521586584766493407)
      ·
        refine ⟨6363960782379877149740111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4242640521586584766493407 6363960782379877149740111)
        ·
          refine ⟨9545941173569815724610167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6363960782379877149740111 9545941173569815724610167)
          ·
            refine ⟨14318911760354723586915251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9545941173569815724610167 14318911760354723586915251)
            ·
              refine ⟨21478367640532085380372877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14318911760354723586915251 21478367640532085380372877)
              ·
                refine ⟨8054387865199532017639829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21478367640532085380372877 8054387865199532017639829)
                ·
                  refine ⟨377549431181228063326867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8054387865199532017639829 377549431181228063326867)
                  ·
                    rfl

theorem cell22_3308737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 3, 6].length) (baseStart_3308737 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3308737 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3308737 prefixEnd_3308737 := by exact prefixLift 3308737
  have htrace : WordTrace (prefixWord ++ tailWord_3308737) baseStart_3308737 baseEnd_3308737 := by
    simpa [prefixWord, tailWord_3308737, baseEnd_3308737] using wordTrace_append hprefix tailTrace_3308737
  have hstable : (prefixWord ++ tailWord_3308737).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3308737).length < 2 ^ (prefixWord ++ tailWord_3308737).sum := by decide
  have hdescent : baseEnd_3308737 < baseStart_3308737 := by decide
  rcases family_descends (prefixWord ++ tailWord_3308737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3308756 : List Nat := [2, 4, 1, 4, 1, 1, 2, 2, 1, 4]
def baseStart_3308756 : Nat := 118140960795 + 3308756 * 2 ^ 59
def prefixEnd_3308756 : Nat := 4983230072969 + 3 ^ 40 * 3308756 * 2
def baseEnd_3308756 : Nat := 1132654797631974473755543

theorem tailTrace_3308756 : CollatzResearch.WordTrace tailWord_3308756 prefixEnd_3308756 1132654797631974473755543 := by
  unfold tailWord_3308756
  simp only [CollatzResearch.WordTrace]
  refine ⟨60340122800474788690377061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80453497067299718253836081 60340122800474788690377061)
  ·
    refine ⟨11313773025089022879445699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60340122800474788690377061 11313773025089022879445699)
    ·
      refine ⟨16970659537633534319168549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11313773025089022879445699 16970659537633534319168549)
      ·
        refine ⟨3181998663306287684844103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16970659537633534319168549 3181998663306287684844103)
        ·
          refine ⟨4772997994959431527266155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3181998663306287684844103 4772997994959431527266155)
          ·
            refine ⟨7159496992439147290899233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4772997994959431527266155 7159496992439147290899233)
            ·
              refine ⟨5369622744329360468174425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7159496992439147290899233 5369622744329360468174425)
              ·
                refine ⟨4027217058247020351130819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5369622744329360468174425 4027217058247020351130819)
                ·
                  refine ⟨6040825587370530526696229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4027217058247020351130819 6040825587370530526696229)
                  ·
                    refine ⟨1132654797631974473755543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6040825587370530526696229 1132654797631974473755543)
                    ·
                      rfl

theorem cell22_3308756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 2, 2, 1, 4].length) (baseStart_3308756 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3308756 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3308756 prefixEnd_3308756 := by exact prefixLift 3308756
  have htrace : WordTrace (prefixWord ++ tailWord_3308756) baseStart_3308756 baseEnd_3308756 := by
    simpa [prefixWord, tailWord_3308756, baseEnd_3308756] using wordTrace_append hprefix tailTrace_3308756
  have hstable : (prefixWord ++ tailWord_3308756).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3308756).length < 2 ^ (prefixWord ++ tailWord_3308756).sum := by decide
  have hdescent : baseEnd_3308756 < baseStart_3308756 := by decide
  rcases family_descends (prefixWord ++ tailWord_3308756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3308788 : List Nat := [2, 6, 1, 2, 1, 2, 1, 1, 6]
def baseStart_3308788 : Nat := 118140960795 + 3308788 * 2 ^ 59
def prefixEnd_3308788 : Nat := 4983230072969 + 3 ^ 40 * 3308788 * 2
def baseEnd_3308788 : Nat := 377555250628645685651815

theorem tailTrace_3308788 : CollatzResearch.WordTrace tailWord_3308788 prefixEnd_3308788 377555250628645685651815 := by
  unfold tailWord_3308788
  simp only [CollatzResearch.WordTrace]
  refine ⟨60340706368416823422959509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80454275157889097897279345 60340706368416823422959509)
  ·
    refine ⟨2828470611019538597951227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 60340706368416823422959509 2828470611019538597951227)
    ·
      refine ⟨4242705916529307896926841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2828470611019538597951227 4242705916529307896926841)
      ·
        refine ⟨3182029437396980922695131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4242705916529307896926841 3182029437396980922695131)
        ·
          refine ⟨4773044156095471384042697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3182029437396980922695131 4773044156095471384042697)
          ·
            refine ⟨3579783117071603538032023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4773044156095471384042697 3579783117071603538032023)
            ·
              refine ⟨5369674675607405307048035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3579783117071603538032023 5369674675607405307048035)
              ·
                refine ⟨8054512013411107960572053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5369674675607405307048035 8054512013411107960572053)
                ·
                  refine ⟨377555250628645685651815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8054512013411107960572053 377555250628645685651815)
                  ·
                    rfl

theorem cell22_3308788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 1, 1, 6].length) (baseStart_3308788 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3308788 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3308788 prefixEnd_3308788 := by exact prefixLift 3308788
  have htrace : WordTrace (prefixWord ++ tailWord_3308788) baseStart_3308788 baseEnd_3308788 := by
    simpa [prefixWord, tailWord_3308788, baseEnd_3308788] using wordTrace_append hprefix tailTrace_3308788
  have hstable : (prefixWord ++ tailWord_3308788).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3308788).length < 2 ^ (prefixWord ++ tailWord_3308788).sum := by decide
  have hdescent : baseEnd_3308788 < baseStart_3308788 := by decide
  rcases family_descends (prefixWord ++ tailWord_3308788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3308887 : List Nat := [1, 1, 3, 2, 3, 2, 2, 2, 1, 5]
def baseStart_3308887 : Nat := 118140960795 + 3308887 * 2 ^ 59
def prefixEnd_3308887 : Nat := 4983230072969 + 3 ^ 40 * 3308887 * 2
def baseEnd_3308887 : Nat := 1132699641609133798730141

theorem tailTrace_3308887 : CollatzResearch.WordTrace tailWord_3308887 prefixEnd_3308887 1132699641609133798730141 := by
  unfold tailWord_3308887
  simp only [CollatzResearch.WordTrace]
  refine ⟨120685023563474986753772915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80456682375649991169181943 120685023563474986753772915)
  ·
    refine ⟨181027535345212480130659373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120685023563474986753772915 181027535345212480130659373)
    ·
      refine ⟨67885325754454680048997265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 181027535345212480130659373 67885325754454680048997265)
      ·
        refine ⟨50913994315841010036747949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67885325754454680048997265 50913994315841010036747949)
        ·
          refine ⟨19092747868440378763780481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50913994315841010036747949 19092747868440378763780481)
          ·
            refine ⟨14319560901330284072835361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19092747868440378763780481 14319560901330284072835361)
            ·
              refine ⟨10739670675997713054626521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14319560901330284072835361 10739670675997713054626521)
              ·
                refine ⟨8054753006998284790969891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10739670675997713054626521 8054753006998284790969891)
                ·
                  refine ⟨12082129510497427186454837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8054753006998284790969891 12082129510497427186454837)
                  ·
                    refine ⟨1132699641609133798730141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12082129510497427186454837 1132699641609133798730141)
                    ·
                      rfl

theorem cell22_3308887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 2, 2, 1, 5].length) (baseStart_3308887 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3308887 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3308887 prefixEnd_3308887 := by exact prefixLift 3308887
  have htrace : WordTrace (prefixWord ++ tailWord_3308887) baseStart_3308887 baseEnd_3308887 := by
    simpa [prefixWord, tailWord_3308887, baseEnd_3308887] using wordTrace_append hprefix tailTrace_3308887
  have hstable : (prefixWord ++ tailWord_3308887).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3308887).length < 2 ^ (prefixWord ++ tailWord_3308887).sum := by decide
  have hdescent : baseEnd_3308887 < baseStart_3308887 := by decide
  rcases family_descends (prefixWord ++ tailWord_3308887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3308915 : List Nat := [1, 1, 1, 2, 2, 1, 2, 1, 4, 7]
def baseStart_3308915 : Nat := 118140960795 + 3308915 * 2 ^ 59
def prefixEnd_3308915 : Nat := 4983230072969 + 3 ^ 40 * 3308915 * 2
def baseEnd_3308915 : Nat := 1132709226581351059030055

theorem tailTrace_3308915 : CollatzResearch.WordTrace tailWord_3308915 prefixEnd_3308915 1132709226581351059030055 := by
  unfold tailWord_3308915
  simp only [CollatzResearch.WordTrace]
  refine ⟨120686044807373547535792199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80457363204915698357194799 120686044807373547535792199)
  ·
    refine ⟨181029067211060321303688299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120686044807373547535792199 181029067211060321303688299)
    ·
      refine ⟨271543600816590481955532449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181029067211060321303688299 271543600816590481955532449)
      ·
        refine ⟨203657700612442861466649337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 271543600816590481955532449 203657700612442861466649337)
        ·
          refine ⟨152743275459332146099987003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 203657700612442861466649337 152743275459332146099987003)
          ·
            refine ⟨229114913188998219149980505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152743275459332146099987003 229114913188998219149980505)
            ·
              refine ⟨171836184891748664362485379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 229114913188998219149980505 171836184891748664362485379)
              ·
                refine ⟨257754277337622996543728069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 171836184891748664362485379 257754277337622996543728069)
                ·
                  refine ⟨48328927000804311851949013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 257754277337622996543728069 48328927000804311851949013)
                  ·
                    refine ⟨1132709226581351059030055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48328927000804311851949013 1132709226581351059030055)
                    ·
                      rfl

theorem cell22_3308915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 4, 7].length) (baseStart_3308915 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3308915 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3308915 prefixEnd_3308915 := by exact prefixLift 3308915
  have htrace : WordTrace (prefixWord ++ tailWord_3308915) baseStart_3308915 baseEnd_3308915 := by
    simpa [prefixWord, tailWord_3308915, baseEnd_3308915] using wordTrace_append hprefix tailTrace_3308915
  have hstable : (prefixWord ++ tailWord_3308915).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3308915).length < 2 ^ (prefixWord ++ tailWord_3308915).sum := by decide
  have hdescent : baseEnd_3308915 < baseStart_3308915 := by decide
  rcases family_descends (prefixWord ++ tailWord_3308915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3308977 : List Nat := [1, 2, 2, 4, 1, 1, 2, 1, 1, 7]
def baseStart_3308977 : Nat := 118140960795 + 3308977 * 2 ^ 59
def prefixEnd_3308977 : Nat := 4983230072969 + 3 ^ 40 * 3308977 * 2
def baseEnd_3308977 : Nat := 1132730450448403563979865

theorem tailTrace_3308977 : CollatzResearch.WordTrace tailWord_3308977 prefixEnd_3308977 1132730450448403563979865 := by
  unfold tailWord_3308977
  simp only [CollatzResearch.WordTrace]
  refine ⟨120688306133148932124549185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80458870755432621416366123 120688306133148932124549185)
  ·
    refine ⟨90516229599861699093411889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120688306133148932124549185 90516229599861699093411889)
    ·
      refine ⟨67887172199896274320058917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90516229599861699093411889 67887172199896274320058917)
      ·
        refine ⟨12728844787480551435011047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67887172199896274320058917 12728844787480551435011047)
        ·
          refine ⟨19093267181220827152516571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12728844787480551435011047 19093267181220827152516571)
          ·
            refine ⟨28639900771831240728774857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19093267181220827152516571 28639900771831240728774857)
            ·
              refine ⟨21479925578873430546581143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28639900771831240728774857 21479925578873430546581143)
              ·
                refine ⟨32219888368310145819871715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21479925578873430546581143 32219888368310145819871715)
                ·
                  refine ⟨48329832552465218729807573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32219888368310145819871715 48329832552465218729807573)
                  ·
                    refine ⟨1132730450448403563979865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48329832552465218729807573 1132730450448403563979865)
                    ·
                      rfl

theorem cell22_3308977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 1, 1, 7].length) (baseStart_3308977 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3308977 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3308977 prefixEnd_3308977 := by exact prefixLift 3308977
  have htrace : WordTrace (prefixWord ++ tailWord_3308977) baseStart_3308977 baseEnd_3308977 := by
    simpa [prefixWord, tailWord_3308977, baseEnd_3308977] using wordTrace_append hprefix tailTrace_3308977
  have hstable : (prefixWord ++ tailWord_3308977).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3308977).length < 2 ^ (prefixWord ++ tailWord_3308977).sum := by decide
  have hdescent : baseEnd_3308977 < baseStart_3308977 := by decide
  rcases family_descends (prefixWord ++ tailWord_3308977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3309052 : List Nat := [2, 2, 2, 1, 2, 1, 2, 10]
def baseStart_3309052 : Nat := 118140960795 + 3309052 * 2 ^ 59
def prefixEnd_3309052 : Nat := 4983230072969 + 3 ^ 40 * 3309052 * 2
def baseEnd_3309052 : Nat := 125861791609014263150515

theorem tailTrace_3309052 : CollatzResearch.WordTrace tailWord_3309052 prefixEnd_3309052 125861791609014263150515 := by
  unfold tailWord_3309052
  simp only [CollatzResearch.WordTrace]
  refine ⟨60345520803938609966764705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80460694405251479955686273 60345520803938609966764705)
  ·
    refine ⟨45259140602953957475073529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60345520803938609966764705 45259140602953957475073529)
    ·
      refine ⟨33944355452215468106305147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45259140602953957475073529 33944355452215468106305147)
      ·
        refine ⟨50916533178323202159457721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33944355452215468106305147 50916533178323202159457721)
        ·
          refine ⟨38187399883742401619593291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50916533178323202159457721 38187399883742401619593291)
          ·
            refine ⟨57281099825613602429389937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38187399883742401619593291 57281099825613602429389937)
            ·
              refine ⟨42960824869210201822042453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57281099825613602429389937 42960824869210201822042453)
              ·
                refine ⟨125861791609014263150515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 42960824869210201822042453 125861791609014263150515)
                ·
                  rfl

theorem cell22_3309052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 10].length) (baseStart_3309052 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3309052 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3309052 prefixEnd_3309052 := by exact prefixLift 3309052
  have htrace : WordTrace (prefixWord ++ tailWord_3309052) baseStart_3309052 baseEnd_3309052 := by
    simpa [prefixWord, tailWord_3309052, baseEnd_3309052] using wordTrace_append hprefix tailTrace_3309052
  have hstable : (prefixWord ++ tailWord_3309052).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3309052).length < 2 ^ (prefixWord ++ tailWord_3309052).sum := by decide
  have hdescent : baseEnd_3309052 < baseStart_3309052 := by decide
  rcases family_descends (prefixWord ++ tailWord_3309052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
