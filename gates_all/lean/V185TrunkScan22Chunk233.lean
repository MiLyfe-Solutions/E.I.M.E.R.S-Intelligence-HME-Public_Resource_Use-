import V185TrunkScan22Chunk232

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_2078271 : List Nat := [1, 1, 2, 2, 3, 3, 3, 1, 1, 5]
def baseStart_2078271 : Nat := 118140960795 + 2078271 * 2 ^ 59
def prefixEnd_2078271 : Nat := 4983230072969 + 3 ^ 40 * 2078271 * 2
def baseEnd_2078271 : Nat := 711434635533562325903141

theorem tailTrace_2078271 : CollatzResearch.WordTrace tailWord_2078271 prefixEnd_2078271 711434635533562325903141 := by
  unfold tailWord_2078271
  simp only [CollatzResearch.WordTrace]
  refine ⟨75800770653786582273658667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50533847102524388182439111 75800770653786582273658667)
  ·
    refine ⟨113701155980679873410488001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75800770653786582273658667 113701155980679873410488001)
    ·
      refine ⟨85275866985509905057866001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113701155980679873410488001 85275866985509905057866001)
      ·
        refine ⟨63956900239132428793399501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85275866985509905057866001 63956900239132428793399501)
        ·
          refine ⟨23983837589674660797524813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63956900239132428793399501 23983837589674660797524813)
          ·
            refine ⟨8993939096127997799071805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23983837589674660797524813 8993939096127997799071805)
            ·
              refine ⟨3372727161047999174651927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8993939096127997799071805 3372727161047999174651927)
              ·
                refine ⟨5059090741571998761977891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3372727161047999174651927 5059090741571998761977891)
                ·
                  refine ⟨7588636112357998142966837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5059090741571998761977891 7588636112357998142966837)
                  ·
                    refine ⟨711434635533562325903141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7588636112357998142966837 711434635533562325903141)
                    ·
                      rfl

theorem cell22_2078271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 3, 1, 1, 5].length) (baseStart_2078271 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2078271 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2078271 prefixEnd_2078271 := by exact prefixLift 2078271
  have htrace : WordTrace (prefixWord ++ tailWord_2078271) baseStart_2078271 baseEnd_2078271 := by
    simpa [prefixWord, tailWord_2078271, baseEnd_2078271] using wordTrace_append hprefix tailTrace_2078271
  have hstable : (prefixWord ++ tailWord_2078271).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2078271).length < 2 ^ (prefixWord ++ tailWord_2078271).sum := by decide
  have hdescent : baseEnd_2078271 < baseStart_2078271 := by decide
  rcases family_descends (prefixWord ++ tailWord_2078271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2078286 : List Nat := [4, 1, 1, 1, 1, 2, 1, 5, 2, 4]
def baseStart_2078286 : Nat := 118140960795 + 2078286 * 2 ^ 59
def prefixEnd_2078286 : Nat := 4983230072969 + 3 ^ 40 * 2078286 * 2
def baseEnd_2078286 : Nat := 711439770340107286778095

theorem tailTrace_2078286 : CollatzResearch.WordTrace tailWord_2078286 prefixEnd_2078286 711439770340107286778095 := by
  unfold tailWord_2078286
  simp only [CollatzResearch.WordTrace]
  refine ⟨9475164718591529979431839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50534211832488159890303141 9475164718591529979431839)
  ·
    refine ⟨14212747077887294969147759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9475164718591529979431839 14212747077887294969147759)
    ·
      refine ⟨21319120616830942453721639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14212747077887294969147759 21319120616830942453721639)
      ·
        refine ⟨31978680925246413680582459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21319120616830942453721639 31978680925246413680582459)
        ·
          refine ⟨47968021387869620520873689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31978680925246413680582459 47968021387869620520873689)
          ·
            refine ⟨35976016040902215390655267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47968021387869620520873689 35976016040902215390655267)
            ·
              refine ⟨53964024061353323085982901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35976016040902215390655267 53964024061353323085982901)
              ·
                refine ⟨5059127255751874039310897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53964024061353323085982901 5059127255751874039310897)
                ·
                  refine ⟨3794345441813905529483173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5059127255751874039310897 3794345441813905529483173)
                  ·
                    refine ⟨711439770340107286778095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3794345441813905529483173 711439770340107286778095)
                    ·
                      rfl

theorem cell22_2078286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 5, 2, 4].length) (baseStart_2078286 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2078286 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2078286 prefixEnd_2078286 := by exact prefixLift 2078286
  have htrace : WordTrace (prefixWord ++ tailWord_2078286) baseStart_2078286 baseEnd_2078286 := by
    simpa [prefixWord, tailWord_2078286, baseEnd_2078286] using wordTrace_append hprefix tailTrace_2078286
  have hstable : (prefixWord ++ tailWord_2078286).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2078286).length < 2 ^ (prefixWord ++ tailWord_2078286).sum := by decide
  have hdescent : baseEnd_2078286 < baseStart_2078286 := by decide
  rcases family_descends (prefixWord ++ tailWord_2078286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2078290 : List Nat := [3, 2, 2, 1, 2, 4, 1, 3, 4]
def baseStart_2078290 : Nat := 118140960795 + 2078290 * 2 ^ 59
def prefixEnd_2078290 : Nat := 4983230072969 + 3 ^ 40 * 2078290 * 2
def baseEnd_2078290 : Nat := 237147046540617536559361

theorem tailTrace_2078290 : CollatzResearch.WordTrace tailWord_2078290 prefixEnd_2078290 237147046540617536559361 := by
  unfold tailWord_2078290
  simp only [CollatzResearch.WordTrace]
  refine ⟨18950365910179437129650081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50534309093811832345733549 18950365910179437129650081)
  ·
    refine ⟨14212774432634577847237561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18950365910179437129650081 14212774432634577847237561)
    ·
      refine ⟨10659580824475933385428171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14212774432634577847237561 10659580824475933385428171)
      ·
        refine ⟨15989371236713900078142257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10659580824475933385428171 15989371236713900078142257)
        ·
          refine ⟨11992028427535425058606693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15989371236713900078142257 11992028427535425058606693)
          ·
            refine ⟨2248505330162892198488755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11992028427535425058606693 2248505330162892198488755)
            ·
              refine ⟨3372757995244338297733133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2248505330162892198488755 3372757995244338297733133)
              ·
                refine ⟨1264784248216626861649925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3372757995244338297733133 1264784248216626861649925)
                ·
                  refine ⟨237147046540617536559361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1264784248216626861649925 237147046540617536559361)
                  ·
                    rfl

theorem cell22_2078290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 1, 3, 4].length) (baseStart_2078290 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2078290 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2078290 prefixEnd_2078290 := by exact prefixLift 2078290
  have htrace : WordTrace (prefixWord ++ tailWord_2078290) baseStart_2078290 baseEnd_2078290 := by
    simpa [prefixWord, tailWord_2078290, baseEnd_2078290] using wordTrace_append hprefix tailTrace_2078290
  have hstable : (prefixWord ++ tailWord_2078290).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2078290).length < 2 ^ (prefixWord ++ tailWord_2078290).sum := by decide
  have hdescent : baseEnd_2078290 < baseStart_2078290 := by decide
  rcases family_descends (prefixWord ++ tailWord_2078290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2078318 : List Nat := [4, 1, 2, 2, 3, 1, 2, 7]
def baseStart_2078318 : Nat := 118140960795 + 2078318 * 2 ^ 59
def prefixEnd_2078318 : Nat := 4983230072969 + 3 ^ 40 * 2078318 * 2
def baseEnd_2078318 : Nat := 79050080510452207775333

theorem tailTrace_2078318 : CollatzResearch.WordTrace tailWord_2078318 prefixEnd_2078318 79050080510452207775333 := by
  unfold tailWord_2078318
  simp only [CollatzResearch.WordTrace]
  refine ⟨9475310610577038662577451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50534989923077539533746405 9475310610577038662577451)
  ·
    refine ⟨14212965915865557993866177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9475310610577038662577451 14212965915865557993866177)
    ·
      refine ⟨10659724436899168495399633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14212965915865557993866177 10659724436899168495399633)
      ·
        refine ⟨7994793327674376371549725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10659724436899168495399633 7994793327674376371549725)
        ·
          refine ⟨2998047497877891139331147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7994793327674376371549725 2998047497877891139331147)
          ·
            refine ⟨4497071246816836708996721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2998047497877891139331147 4497071246816836708996721)
            ·
              refine ⟨3372803435112627531747541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4497071246816836708996721 3372803435112627531747541)
              ·
                refine ⟨79050080510452207775333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3372803435112627531747541 79050080510452207775333)
                ·
                  rfl

theorem cell22_2078318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 2, 7].length) (baseStart_2078318 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2078318 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2078318 prefixEnd_2078318 := by exact prefixLift 2078318
  have htrace : WordTrace (prefixWord ++ tailWord_2078318) baseStart_2078318 baseEnd_2078318 := by
    simpa [prefixWord, tailWord_2078318, baseEnd_2078318] using wordTrace_append hprefix tailTrace_2078318
  have hstable : (prefixWord ++ tailWord_2078318).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2078318).length < 2 ^ (prefixWord ++ tailWord_2078318).sum := by decide
  have hdescent : baseEnd_2078318 < baseStart_2078318 := by decide
  rcases family_descends (prefixWord ++ tailWord_2078318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2078322 : List Nat := [3, 2, 1, 2, 3, 3, 2, 1, 2, 3]
def baseStart_2078322 : Nat := 118140960795 + 2078322 * 2 ^ 59
def prefixEnd_2078322 : Nat := 4983230072969 + 3 ^ 40 * 2078322 * 2
def baseEnd_2078322 : Nat := 711452093875815192877985

theorem tailTrace_2078322 : CollatzResearch.WordTrace tailWord_2078322 prefixEnd_2078322 711452093875815192877985 := by
  unfold tailWord_2078322
  simp only [CollatzResearch.WordTrace]
  refine ⟨18950657694150454495941305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50535087184401211989176813 18950657694150454495941305)
  ·
    refine ⟨14212993270612840871955979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18950657694150454495941305 14212993270612840871955979)
    ·
      refine ⟨21319489905919261307933969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14212993270612840871955979 21319489905919261307933969)
      ·
        refine ⟨15989617429439445980950477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21319489905919261307933969 15989617429439445980950477)
        ·
          refine ⟨5996106536039792242856429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15989617429439445980950477 5996106536039792242856429)
          ·
            refine ⟨2248539951014922091071161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5996106536039792242856429 2248539951014922091071161)
            ·
              refine ⟨1686404963261191568303371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2248539951014922091071161 1686404963261191568303371)
              ·
                refine ⟨2529607444891787352455057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1686404963261191568303371 2529607444891787352455057)
                ·
                  refine ⟨1897205583668840514341293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2529607444891787352455057 1897205583668840514341293)
                  ·
                    refine ⟨711452093875815192877985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1897205583668840514341293 711452093875815192877985)
                    ·
                      rfl

theorem cell22_2078322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 2, 1, 2, 3].length) (baseStart_2078322 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2078322 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2078322 prefixEnd_2078322 := by exact prefixLift 2078322
  have htrace : WordTrace (prefixWord ++ tailWord_2078322) baseStart_2078322 baseEnd_2078322 := by
    simpa [prefixWord, tailWord_2078322, baseEnd_2078322] using wordTrace_append hprefix tailTrace_2078322
  have hstable : (prefixWord ++ tailWord_2078322).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2078322).length < 2 ^ (prefixWord ++ tailWord_2078322).sum := by decide
  have hdescent : baseEnd_2078322 < baseStart_2078322 := by decide
  rcases family_descends (prefixWord ++ tailWord_2078322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2078391 : List Nat := [1, 1, 3, 1, 5, 1, 1, 1, 8]
def baseStart_2078391 : Nat := 118140960795 + 2078391 * 2 ^ 59
def prefixEnd_2078391 : Nat := 4983230072969 + 3 ^ 40 * 2078391 * 2
def baseEnd_2078391 : Nat := 237158571328640670967591

theorem tailTrace_2078391 : CollatzResearch.WordTrace tailWord_2078391 prefixEnd_2078391 237158571328640670967591 := by
  unfold tailWord_2078391
  simp only [CollatzResearch.WordTrace]
  refine ⟨75805147413351842768027027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50536764942234561845351351 75805147413351842768027027)
  ·
    refine ⟨113707721120027764152040541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75805147413351842768027027 113707721120027764152040541)
    ·
      refine ⟨42640395420010411557015203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113707721120027764152040541 42640395420010411557015203)
      ·
        refine ⟨63960593130015617335522805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42640395420010411557015203 63960593130015617335522805)
        ·
          refine ⟨5996305605938964125205263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 63960593130015617335522805 5996305605938964125205263)
          ·
            refine ⟨8994458408908446187807895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5996305605938964125205263 8994458408908446187807895)
            ·
              refine ⟨13491687613362669281711843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8994458408908446187807895 13491687613362669281711843)
              ·
                refine ⟨20237531420044003922567765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13491687613362669281711843 20237531420044003922567765)
                ·
                  refine ⟨237158571328640670967591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20237531420044003922567765 237158571328640670967591)
                  ·
                    rfl

theorem cell22_2078391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 1, 8].length) (baseStart_2078391 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2078391 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2078391 prefixEnd_2078391 := by exact prefixLift 2078391
  have htrace : WordTrace (prefixWord ++ tailWord_2078391) baseStart_2078391 baseEnd_2078391 := by
    simpa [prefixWord, tailWord_2078391, baseEnd_2078391] using wordTrace_append hprefix tailTrace_2078391
  have hstable : (prefixWord ++ tailWord_2078391).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2078391).length < 2 ^ (prefixWord ++ tailWord_2078391).sum := by decide
  have hdescent : baseEnd_2078391 < baseStart_2078391 := by decide
  rcases family_descends (prefixWord ++ tailWord_2078391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2078410 : List Nat := [3, 1, 2, 1, 5, 1, 1, 3, 1, 4]
def baseStart_2078410 : Nat := 118140960795 + 2078410 * 2 ^ 59
def prefixEnd_2078410 : Nat := 4983230072969 + 3 ^ 40 * 2078410 * 2
def baseEnd_2078410 : Nat := 711482218074212296677715

theorem tailTrace_2078410 : CollatzResearch.WordTrace tailWord_2078410 prefixEnd_2078410 711482218074212296677715 := by
  unfold tailWord_2078410
  simp only [CollatzResearch.WordTrace]
  refine ⟨18951460100070752253242171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50537226933522006008645789 18951460100070752253242171)
  ·
    refine ⟨28427190150106128379863257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18951460100070752253242171 28427190150106128379863257)
    ·
      refine ⟨21320392612579596284897443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28427190150106128379863257 21320392612579596284897443)
      ·
        refine ⟨31980588918869394427346165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21320392612579596284897443 31980588918869394427346165)
        ·
          refine ⟨2998180211144005727563703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31980588918869394427346165 2998180211144005727563703)
          ·
            refine ⟨4497270316716008591345555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2998180211144005727563703 4497270316716008591345555)
            ·
              refine ⟨6745905475074012887018333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4497270316716008591345555 6745905475074012887018333)
              ·
                refine ⟨2529714553152754832631875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6745905475074012887018333 2529714553152754832631875)
                ·
                  refine ⟨3794571829729132248947813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2529714553152754832631875 3794571829729132248947813)
                  ·
                    refine ⟨711482218074212296677715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3794571829729132248947813 711482218074212296677715)
                    ·
                      rfl

theorem cell22_2078410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 1, 3, 1, 4].length) (baseStart_2078410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2078410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2078410 prefixEnd_2078410 := by exact prefixLift 2078410
  have htrace : WordTrace (prefixWord ++ tailWord_2078410) baseStart_2078410 baseEnd_2078410 := by
    simpa [prefixWord, tailWord_2078410, baseEnd_2078410] using wordTrace_append hprefix tailTrace_2078410
  have hstable : (prefixWord ++ tailWord_2078410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2078410).length < 2 ^ (prefixWord ++ tailWord_2078410).sum := by decide
  have hdescent : baseEnd_2078410 < baseStart_2078410 := by decide
  rcases family_descends (prefixWord ++ tailWord_2078410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2078423 : List Nat := [1, 1, 3, 2, 1, 3, 3, 1, 4, 3]
def baseStart_2078423 : Nat := 118140960795 + 2078423 * 2 ^ 59
def prefixEnd_2078423 : Nat := 4983230072969 + 3 ^ 40 * 2078423 * 2
def baseEnd_2078423 : Nat := 711486668239884596102675

theorem tailTrace_2078423 : CollatzResearch.WordTrace tailWord_2078423 prefixEnd_2078423 711486668239884596102675 := by
  unfold tailWord_2078423
  simp only [CollatzResearch.WordTrace]
  refine ⟨75806314549235912233191923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50537543032823941488794615 75806314549235912233191923)
  ·
    refine ⟨113709471823853868349787885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75806314549235912233191923 113709471823853868349787885)
    ·
      refine ⟨42641051933945200631170457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113709471823853868349787885 42641051933945200631170457)
      ·
        refine ⟨31980788950458900473377843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42641051933945200631170457 31980788950458900473377843)
        ·
          refine ⟨47971183425688350710066765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31980788950458900473377843 47971183425688350710066765)
          ·
            refine ⟨17989193784633131516275037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47971183425688350710066765 17989193784633131516275037)
            ·
              refine ⟨6745947669237424318603139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17989193784633131516275037 6745947669237424318603139)
              ·
                refine ⟨10118921503856136477904709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6745947669237424318603139 10118921503856136477904709)
                ·
                  refine ⟨1897297781973025589607133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10118921503856136477904709 1897297781973025589607133)
                  ·
                    refine ⟨711486668239884596102675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1897297781973025589607133 711486668239884596102675)
                    ·
                      rfl

theorem cell22_2078423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3, 1, 4, 3].length) (baseStart_2078423 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2078423 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2078423 prefixEnd_2078423 := by exact prefixLift 2078423
  have htrace : WordTrace (prefixWord ++ tailWord_2078423) baseStart_2078423 baseEnd_2078423 := by
    simpa [prefixWord, tailWord_2078423, baseEnd_2078423] using wordTrace_append hprefix tailTrace_2078423
  have hstable : (prefixWord ++ tailWord_2078423).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2078423).length < 2 ^ (prefixWord ++ tailWord_2078423).sum := by decide
  have hdescent : baseEnd_2078423 < baseStart_2078423 := by decide
  rcases family_descends (prefixWord ++ tailWord_2078423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2078436 : List Nat := [2, 3, 1, 1, 1, 3, 2, 9]
def baseStart_2078436 : Nat := 118140960795 + 2078436 * 2 ^ 59
def prefixEnd_2078436 : Nat := 4983230072969 + 3 ^ 40 * 2078436 * 2
def baseEnd_2078436 : Nat := 79054568711728543947515

theorem tailTrace_2078436 : CollatzResearch.WordTrace tailWord_2078436 prefixEnd_2078436 79054568711728543947515 := by
  unfold tailWord_2078436
  simp only [CollatzResearch.WordTrace]
  refine ⟨37903394349094407726707581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50537859132125876968943441 37903394349094407726707581)
  ·
    refine ⟨14213772880910402897515343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37903394349094407726707581 14213772880910402897515343)
    ·
      refine ⟨21320659321365604346273015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14213772880910402897515343 21320659321365604346273015)
      ·
        refine ⟨31980988982048406519409523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21320659321365604346273015 31980988982048406519409523)
        ·
          refine ⟨47971483473072609779114285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31980988982048406519409523 47971483473072609779114285)
          ·
            refine ⟨17989306302402228667167857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47971483473072609779114285 17989306302402228667167857)
            ·
              refine ⟨13491979726801671500375893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17989306302402228667167857 13491979726801671500375893)
              ·
                refine ⟨79054568711728543947515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 13491979726801671500375893 79054568711728543947515)
                ·
                  rfl

theorem cell22_2078436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 9].length) (baseStart_2078436 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2078436 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2078436 prefixEnd_2078436 := by exact prefixLift 2078436
  have htrace : WordTrace (prefixWord ++ tailWord_2078436) baseStart_2078436 baseEnd_2078436 := by
    simpa [prefixWord, tailWord_2078436, baseEnd_2078436] using wordTrace_append hprefix tailTrace_2078436
  have hstable : (prefixWord ++ tailWord_2078436).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2078436).length < 2 ^ (prefixWord ++ tailWord_2078436).sum := by decide
  have hdescent : baseEnd_2078436 < baseStart_2078436 := by decide
  rcases family_descends (prefixWord ++ tailWord_2078436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2078440 : List Nat := [2, 1, 4, 1, 3, 3, 1, 1, 1, 5]
def baseStart_2078440 : Nat := 118140960795 + 2078440 * 2 ^ 59
def prefixEnd_2078440 : Nat := 4983230072969 + 3 ^ 40 * 2078440 * 2
def baseEnd_2078440 : Nat := 711492487687302218427623

theorem tailTrace_2078440 : CollatzResearch.WordTrace tailWord_2078440 prefixEnd_2078440 711492487687302218427623 := by
  unfold tailWord_2078440
  simp only [CollatzResearch.WordTrace]
  refine ⟨37903467295087162068280387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50537956393449549424373849 37903467295087162068280387)
  ·
    refine ⟨56855200942630743102420581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37903467295087162068280387 56855200942630743102420581)
    ·
      refine ⟨10660350176743264331703859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56855200942630743102420581 10660350176743264331703859)
      ·
        refine ⟨15990525265114896497555789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10660350176743264331703859 15990525265114896497555789)
        ·
          refine ⟨5996446974418086186583421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15990525265114896497555789 5996446974418086186583421)
          ·
            refine ⟨2248667615406782319968783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5996446974418086186583421 2248667615406782319968783)
            ·
              refine ⟨3373001423110173479953175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2248667615406782319968783 3373001423110173479953175)
              ·
                refine ⟨5059502134665260219929763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3373001423110173479953175 5059502134665260219929763)
                ·
                  refine ⟨7589253201997890329894645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5059502134665260219929763 7589253201997890329894645)
                  ·
                    refine ⟨711492487687302218427623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7589253201997890329894645 711492487687302218427623)
                    ·
                      rfl

theorem cell22_2078440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 1, 1, 1, 5].length) (baseStart_2078440 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2078440 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2078440 prefixEnd_2078440 := by exact prefixLift 2078440
  have htrace : WordTrace (prefixWord ++ tailWord_2078440) baseStart_2078440 baseEnd_2078440 := by
    simpa [prefixWord, tailWord_2078440, baseEnd_2078440] using wordTrace_append hprefix tailTrace_2078440
  have hstable : (prefixWord ++ tailWord_2078440).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2078440).length < 2 ^ (prefixWord ++ tailWord_2078440).sum := by decide
  have hdescent : baseEnd_2078440 < baseStart_2078440 := by decide
  rcases family_descends (prefixWord ++ tailWord_2078440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2078485 : List Nat := [1, 3, 2, 1, 2, 3, 3, 1, 3, 3]
def baseStart_2078485 : Nat := 118140960795 + 2078485 * 2 ^ 59
def prefixEnd_2078485 : Nat := 4983230072969 + 3 ^ 40 * 2078485 * 2
def baseEnd_2078485 : Nat := 711507892106937101052485

theorem tailTrace_2078485 : CollatzResearch.WordTrace tailWord_2078485 prefixEnd_2078485 711507892106937101052485 := by
  unfold tailWord_2078485
  simp only [CollatzResearch.WordTrace]
  refine ⟨75808575875011296821948909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50539050583340864547965939 75808575875011296821948909)
  ·
    refine ⟨28428215953129236308230841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75808575875011296821948909 28428215953129236308230841)
    ·
      refine ⟨21321161964846927231173131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28428215953129236308230841 21321161964846927231173131)
      ·
        refine ⟨31981742947270390846759697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21321161964846927231173131 31981742947270390846759697)
        ·
          refine ⟨23986307210452793135069773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31981742947270390846759697 23986307210452793135069773)
          ·
            refine ⟨8994865203919797425651165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23986307210452793135069773 8994865203919797425651165)
            ·
              refine ⟨3373074451469924034619187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8994865203919797425651165 3373074451469924034619187)
              ·
                refine ⟨5059611677204886051928781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3373074451469924034619187 5059611677204886051928781)
                ·
                  refine ⟨1897354378951832269473293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5059611677204886051928781 1897354378951832269473293)
                  ·
                    refine ⟨711507892106937101052485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1897354378951832269473293 711507892106937101052485)
                    ·
                      rfl

theorem cell22_2078485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 3, 1, 3, 3].length) (baseStart_2078485 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2078485 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2078485 prefixEnd_2078485 := by exact prefixLift 2078485
  have htrace : WordTrace (prefixWord ++ tailWord_2078485) baseStart_2078485 baseEnd_2078485 := by
    simpa [prefixWord, tailWord_2078485, baseEnd_2078485] using wordTrace_append hprefix tailTrace_2078485
  have hstable : (prefixWord ++ tailWord_2078485).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2078485).length < 2 ^ (prefixWord ++ tailWord_2078485).sum := by decide
  have hdescent : baseEnd_2078485 < baseStart_2078485 := by decide
  rcases family_descends (prefixWord ++ tailWord_2078485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2078511 : List Nat := [1, 1, 2, 1, 2, 1, 2, 2, 2, 8]
def baseStart_2078511 : Nat := 118140960795 + 2078511 * 2 ^ 59
def prefixEnd_2078511 : Nat := 4983230072969 + 3 ^ 40 * 2078511 * 2
def baseEnd_2078511 : Nat := 711516792438281699902405

theorem tailTrace_2078511 : CollatzResearch.WordTrace tailWord_2078511 prefixEnd_2078511 711516792438281699902405 := by
  unfold tailWord_2078511
  simp only [CollatzResearch.WordTrace]
  refine ⟨75809524172917103262395387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50539682781944735508263591 75809524172917103262395387)
  ·
    refine ⟨113714286259375654893593081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75809524172917103262395387 113714286259375654893593081)
    ·
      refine ⟨85285714694531741170194811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113714286259375654893593081 85285714694531741170194811)
      ·
        refine ⟨127928572041797611755292217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85285714694531741170194811 127928572041797611755292217)
        ·
          refine ⟨95946429031348208816469163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127928572041797611755292217 95946429031348208816469163)
          ·
            refine ⟨143919643547022313224703745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95946429031348208816469163 143919643547022313224703745)
            ·
              refine ⟨107939732660266734918527809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 143919643547022313224703745 107939732660266734918527809)
              ·
                refine ⟨80954799495200051188895857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107939732660266734918527809 80954799495200051188895857)
                ·
                  refine ⟨60716099621400038391671893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80954799495200051188895857 60716099621400038391671893)
                  ·
                    refine ⟨711516792438281699902405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 60716099621400038391671893 711516792438281699902405)
                    ·
                      rfl

theorem cell22_2078511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 2, 2, 8].length) (baseStart_2078511 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2078511 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2078511 prefixEnd_2078511 := by exact prefixLift 2078511
  have htrace : WordTrace (prefixWord ++ tailWord_2078511) baseStart_2078511 baseEnd_2078511 := by
    simpa [prefixWord, tailWord_2078511, baseEnd_2078511] using wordTrace_append hprefix tailTrace_2078511
  have hstable : (prefixWord ++ tailWord_2078511).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2078511).length < 2 ^ (prefixWord ++ tailWord_2078511).sum := by decide
  have hdescent : baseEnd_2078511 < baseStart_2078511 := by decide
  rcases family_descends (prefixWord ++ tailWord_2078511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2078654 : List Nat := [4, 2, 1, 1, 1, 5, 1, 1, 3, 3]
def baseStart_2078654 : Nat := 118140960795 + 2078654 * 2 ^ 59
def prefixEnd_2078654 : Nat := 4983230072969 + 3 ^ 40 * 2078654 * 2
def baseEnd_2078654 : Nat := 711565744260676993576967

theorem tailTrace_2078654 : CollatzResearch.WordTrace tailWord_2078654 prefixEnd_2078654 711565744260676993576967 := by
  unfold tailWord_2078654
  simp only [CollatzResearch.WordTrace]
  refine ⟨9476842476424879835606377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50543159874266025789900677 9476842476424879835606377)
  ·
    refine ⟨7107631857318659876704783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9476842476424879835606377 7107631857318659876704783)
    ·
      refine ⟨10661447785977989815057175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7107631857318659876704783 10661447785977989815057175)
      ·
        refine ⟨15992171678966984722585763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10661447785977989815057175 15992171678966984722585763)
        ·
          refine ⟨23988257518450477083878645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15992171678966984722585763 23988257518450477083878645)
          ·
            refine ⟨2248899142354732226613623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23988257518450477083878645 2248899142354732226613623)
            ·
              refine ⟨3373348713532098339920435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2248899142354732226613623 3373348713532098339920435)
              ·
                refine ⟨5060023070298147509880653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3373348713532098339920435 5060023070298147509880653)
                ·
                  refine ⟨1897508651361805316205245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5060023070298147509880653 1897508651361805316205245)
                  ·
                    refine ⟨711565744260676993576967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1897508651361805316205245 711565744260676993576967)
                    ·
                      rfl

theorem cell22_2078654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 1, 1, 3, 3].length) (baseStart_2078654 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2078654 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2078654 prefixEnd_2078654 := by exact prefixLift 2078654
  have htrace : WordTrace (prefixWord ++ tailWord_2078654) baseStart_2078654 baseEnd_2078654 := by
    simpa [prefixWord, tailWord_2078654, baseEnd_2078654] using wordTrace_append hprefix tailTrace_2078654
  have hstable : (prefixWord ++ tailWord_2078654).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2078654).length < 2 ^ (prefixWord ++ tailWord_2078654).sum := by decide
  have hdescent : baseEnd_2078654 < baseStart_2078654 := by decide
  rcases family_descends (prefixWord ++ tailWord_2078654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2078663 : List Nat := [1, 1, 4, 1, 1, 2, 1, 1, 2, 8]
def baseStart_2078663 : Nat := 118140960795 + 2078663 * 2 ^ 59
def prefixEnd_2078663 : Nat := 4983230072969 + 3 ^ 40 * 2078663 * 2
def baseEnd_2078663 : Nat := 711568825144603970101939

theorem tailTrace_2078663 : CollatzResearch.WordTrace tailWord_2078663 prefixEnd_2078663 711568825144603970101939 := by
  unfold tailWord_2078663
  simp only [CollatzResearch.WordTrace]
  refine ⟨75815068068366433221928643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50543378712244288814619095 75815068068366433221928643)
  ·
    refine ⟨113722602102549649832892965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75815068068366433221928643 113722602102549649832892965)
    ·
      refine ⟨21322987894228059343667431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 113722602102549649832892965 21322987894228059343667431)
      ·
        refine ⟨31984481841342089015501147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21322987894228059343667431 31984481841342089015501147)
        ·
          refine ⟨47976722762013133523251721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31984481841342089015501147 47976722762013133523251721)
          ·
            refine ⟨35982542071509850142438791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47976722762013133523251721 35982542071509850142438791)
            ·
              refine ⟨53973813107264775213658187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35982542071509850142438791 53973813107264775213658187)
              ·
                refine ⟨80960719660897162820487281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53973813107264775213658187 80960719660897162820487281)
                ·
                  refine ⟨60720539745672872115365461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80960719660897162820487281 60720539745672872115365461)
                  ·
                    refine ⟨711568825144603970101939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 60720539745672872115365461 711568825144603970101939)
                    ·
                      rfl

theorem cell22_2078663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 1, 2, 8].length) (baseStart_2078663 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2078663 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2078663 prefixEnd_2078663 := by exact prefixLift 2078663
  have htrace : WordTrace (prefixWord ++ tailWord_2078663) baseStart_2078663 baseEnd_2078663 := by
    simpa [prefixWord, tailWord_2078663, baseEnd_2078663] using wordTrace_append hprefix tailTrace_2078663
  have hstable : (prefixWord ++ tailWord_2078663).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2078663).length < 2 ^ (prefixWord ++ tailWord_2078663).sum := by decide
  have hdescent : baseEnd_2078663 < baseStart_2078663 := by decide
  rcases family_descends (prefixWord ++ tailWord_2078663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2078680 : List Nat := [2, 1, 2, 2, 2, 2, 3, 1, 3, 4]
def baseStart_2078680 : Nat := 118140960795 + 2078680 * 2 ^ 59
def prefixEnd_2078680 : Nat := 4983230072969 + 3 ^ 40 * 2078680 * 2
def baseEnd_2078680 : Nat := 711574644592021592426887

theorem tailTrace_2078680 : CollatzResearch.WordTrace tailWord_2078680 prefixEnd_2078680 711574644592021592426887 := by
  unfold tailWord_2078680
  simp only [CollatzResearch.WordTrace]
  refine ⟨37907844054652422562648747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50543792072869896750198329 37907844054652422562648747)
  ·
    refine ⟨56861766081978633843973121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37907844054652422562648747 56861766081978633843973121)
    ·
      refine ⟨42646324561483975382979841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56861766081978633843973121 42646324561483975382979841)
      ·
        refine ⟨31984743421112981537234881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42646324561483975382979841 31984743421112981537234881)
        ·
          refine ⟨23988557565834736152926161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31984743421112981537234881 23988557565834736152926161)
          ·
            refine ⟨17991418174376052114694621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23988557565834736152926161 17991418174376052114694621)
            ·
              refine ⟨6746781815391019543010483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17991418174376052114694621 6746781815391019543010483)
              ·
                refine ⟨10120172723086529314515725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6746781815391019543010483 10120172723086529314515725)
                ·
                  refine ⟨3795064771157448492943397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10120172723086529314515725 3795064771157448492943397)
                  ·
                    refine ⟨711574644592021592426887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3795064771157448492943397 711574644592021592426887)
                    ·
                      rfl

theorem cell22_2078680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3, 1, 3, 4].length) (baseStart_2078680 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2078680 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2078680 prefixEnd_2078680 := by exact prefixLift 2078680
  have htrace : WordTrace (prefixWord ++ tailWord_2078680) baseStart_2078680 baseEnd_2078680 := by
    simpa [prefixWord, tailWord_2078680, baseEnd_2078680] using wordTrace_append hprefix tailTrace_2078680
  have hstable : (prefixWord ++ tailWord_2078680).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2078680).length < 2 ^ (prefixWord ++ tailWord_2078680).sum := by decide
  have hdescent : baseEnd_2078680 < baseStart_2078680 := by decide
  rcases family_descends (prefixWord ++ tailWord_2078680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2078727 : List Nat := [1, 1, 4, 3, 1, 3, 2, 1, 1, 5]
def baseStart_2078727 : Nat := 118140960795 + 2078727 * 2 ^ 59
def prefixEnd_2078727 : Nat := 4983230072969 + 3 ^ 40 * 2078727 * 2
def baseEnd_2078727 : Nat := 711590733652529136501743

theorem tailTrace_2078727 : CollatzResearch.WordTrace tailWord_2078727 prefixEnd_2078727 711590733652529136501743 := by
  unfold tailWord_2078727
  simp only [CollatzResearch.WordTrace]
  refine ⟨75817402340134572152258435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50544934893423048101505623 75817402340134572152258435)
  ·
    refine ⟨113726103510201858228387653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75817402340134572152258435 113726103510201858228387653)
    ·
      refine ⟨21323644408162848417822685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 113726103510201858228387653 21323644408162848417822685)
      ·
        refine ⟨7996366653061068156683507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21323644408162848417822685 7996366653061068156683507)
        ·
          refine ⟨11994549979591602235025261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7996366653061068156683507 11994549979591602235025261)
          ·
            refine ⟨4497956242346850838134473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11994549979591602235025261 4497956242346850838134473)
            ·
              refine ⟨3373467181760138128600855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4497956242346850838134473 3373467181760138128600855)
              ·
                refine ⟨5060200772640207192901283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3373467181760138128600855 5060200772640207192901283)
                ·
                  refine ⟨7590301158960310789351925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5060200772640207192901283 7590301158960310789351925)
                  ·
                    refine ⟨711590733652529136501743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7590301158960310789351925 711590733652529136501743)
                    ·
                      rfl

theorem cell22_2078727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 2, 1, 1, 5].length) (baseStart_2078727 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2078727 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2078727 prefixEnd_2078727 := by exact prefixLift 2078727
  have htrace : WordTrace (prefixWord ++ tailWord_2078727) baseStart_2078727 baseEnd_2078727 := by
    simpa [prefixWord, tailWord_2078727, baseEnd_2078727] using wordTrace_append hprefix tailTrace_2078727
  have hstable : (prefixWord ++ tailWord_2078727).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2078727).length < 2 ^ (prefixWord ++ tailWord_2078727).sum := by decide
  have hdescent : baseEnd_2078727 < baseStart_2078727 := by decide
  rcases family_descends (prefixWord ++ tailWord_2078727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2078849 : List Nat := [1, 2, 4, 2, 3, 1, 1, 1, 3, 4]
def baseStart_2078849 : Nat := 118140960795 + 2078849 * 2 ^ 59
def prefixEnd_2078849 : Nat := 4983230072969 + 3 ^ 40 * 2078849 * 2
def baseEnd_2078849 : Nat := 711632496745761484951369

theorem tailTrace_2078849 : CollatzResearch.WordTrace tailWord_2078849 prefixEnd_2078849 711632496745761484951369 := by
  unfold tailWord_2078849
  simp only [CollatzResearch.WordTrace]
  refine ⟨75821852045692586988199601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50547901363795057992133067 75821852045692586988199601)
  ·
    refine ⟨56866389034269440241149701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75821852045692586988199601 56866389034269440241149701)
    ·
      refine ⟨10662447943925520045215569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56866389034269440241149701 10662447943925520045215569)
      ·
        refine ⟨7996835957944140033911677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10662447943925520045215569 7996835957944140033911677)
        ·
          refine ⟨2998813484229052512716879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7996835957944140033911677 2998813484229052512716879)
          ·
            refine ⟨4498220226343578769075319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2998813484229052512716879 4498220226343578769075319)
            ·
              refine ⟨6747330339515368153612979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4498220226343578769075319 6747330339515368153612979)
              ·
                refine ⟨10120995509273052230419469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6747330339515368153612979 10120995509273052230419469)
                ·
                  refine ⟨3795373315977394586407301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10120995509273052230419469 3795373315977394586407301)
                  ·
                    refine ⟨711632496745761484951369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3795373315977394586407301 711632496745761484951369)
                    ·
                      rfl

theorem cell22_2078849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 1, 1, 3, 4].length) (baseStart_2078849 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2078849 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2078849 prefixEnd_2078849 := by exact prefixLift 2078849
  have htrace : WordTrace (prefixWord ++ tailWord_2078849) baseStart_2078849 baseEnd_2078849 := by
    simpa [prefixWord, tailWord_2078849, baseEnd_2078849] using wordTrace_append hprefix tailTrace_2078849
  have hstable : (prefixWord ++ tailWord_2078849).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2078849).length < 2 ^ (prefixWord ++ tailWord_2078849).sum := by decide
  have hdescent : baseEnd_2078849 < baseStart_2078849 := by decide
  rcases family_descends (prefixWord ++ tailWord_2078849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2078866 : List Nat := [3, 2, 3, 1, 1, 1, 5, 1, 1, 4]
def baseStart_2078866 : Nat := 118140960795 + 2078866 * 2 ^ 59
def prefixEnd_2078866 : Nat := 4983230072969 + 3 ^ 40 * 2078866 * 2
def baseEnd_2078866 : Nat := 711638316193179107276317

theorem tailTrace_2078866 : CollatzResearch.WordTrace tailWord_2078866 prefixEnd_2078866 711638316193179107276317 := by
  unfold tailWord_2078866
  simp only [CollatzResearch.WordTrace]
  refine ⟨18955618021657749722892113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50548314724420665927712301 18955618021657749722892113)
  ·
    refine ⟨14216713516243312292169085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18955618021657749722892113 14216713516243312292169085)
    ·
      refine ⟨5331267568591242109563407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14216713516243312292169085 5331267568591242109563407)
      ·
        refine ⟨7996901352886863164345111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5331267568591242109563407 7996901352886863164345111)
        ·
          refine ⟨11995352029330294746517667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7996901352886863164345111 11995352029330294746517667)
          ·
            refine ⟨17993028043995442119776501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11995352029330294746517667 17993028043995442119776501)
            ·
              refine ⟨1686846379124572698729047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17993028043995442119776501 1686846379124572698729047)
              ·
                refine ⟨2530269568686859048093571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1686846379124572698729047 2530269568686859048093571)
                ·
                  refine ⟨3795404353030288572140357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2530269568686859048093571 3795404353030288572140357)
                  ·
                    refine ⟨711638316193179107276317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3795404353030288572140357 711638316193179107276317)
                    ·
                      rfl

theorem cell22_2078866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 5, 1, 1, 4].length) (baseStart_2078866 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2078866 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2078866 prefixEnd_2078866 := by exact prefixLift 2078866
  have htrace : WordTrace (prefixWord ++ tailWord_2078866) baseStart_2078866 baseEnd_2078866 := by
    simpa [prefixWord, tailWord_2078866, baseEnd_2078866] using wordTrace_append hprefix tailTrace_2078866
  have hstable : (prefixWord ++ tailWord_2078866).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2078866).length < 2 ^ (prefixWord ++ tailWord_2078866).sum := by decide
  have hdescent : baseEnd_2078866 < baseStart_2078866 := by decide
  rcases family_descends (prefixWord ++ tailWord_2078866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2078881 : List Nat := [1, 2, 3, 3, 1, 2, 4, 2, 4]
def baseStart_2078881 : Nat := 118140960795 + 2078881 * 2 ^ 59
def prefixEnd_2078881 : Nat := 4983230072969 + 3 ^ 40 * 2078881 * 2
def baseEnd_2078881 : Nat := 237214483666574689383757

theorem tailTrace_2078881 : CollatzResearch.WordTrace tailWord_2078881 prefixEnd_2078881 237214483666574689383757 := by
  unfold tailWord_2078881
  simp only [CollatzResearch.WordTrace]
  refine ⟨75823019181576656453364497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50548679454384437635576331 75823019181576656453364497)
  ·
    refine ⟨56867264386182492340023373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75823019181576656453364497 56867264386182492340023373)
    ·
      refine ⟨21325224144818434627508765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56867264386182492340023373 21325224144818434627508765)
      ·
        refine ⟨7996959054306912985315787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21325224144818434627508765 7996959054306912985315787)
        ·
          refine ⟨11995438581460369477973681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7996959054306912985315787 11995438581460369477973681)
          ·
            refine ⟨8996578936095277108480261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11995438581460369477973681 8996578936095277108480261)
            ·
              refine ⟨1686858550517864457840049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8996578936095277108480261 1686858550517864457840049)
              ·
                refine ⟨1265143912888398343380037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1686858550517864457840049 1265143912888398343380037)
                ·
                  refine ⟨237214483666574689383757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1265143912888398343380037 237214483666574689383757)
                  ·
                    rfl

theorem cell22_2078881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 4, 2, 4].length) (baseStart_2078881 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2078881 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2078881 prefixEnd_2078881 := by exact prefixLift 2078881
  have htrace : WordTrace (prefixWord ++ tailWord_2078881) baseStart_2078881 baseEnd_2078881 := by
    simpa [prefixWord, tailWord_2078881, baseEnd_2078881] using wordTrace_append hprefix tailTrace_2078881
  have hstable : (prefixWord ++ tailWord_2078881).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2078881).length < 2 ^ (prefixWord ++ tailWord_2078881).sum := by decide
  have hdescent : baseEnd_2078881 < baseStart_2078881 := by decide
  rcases family_descends (prefixWord ++ tailWord_2078881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2078941 : List Nat := [1, 4, 3, 2, 1, 1, 1, 3, 3, 3]
def baseStart_2078941 : Nat := 118140960795 + 2078941 * 2 ^ 59
def prefixEnd_2078941 : Nat := 4983230072969 + 3 ^ 40 * 2078941 * 2
def baseEnd_2078941 : Nat := 711663990225903911651087

theorem tailTrace_2078941 : CollatzResearch.WordTrace tailWord_2078941 prefixEnd_2078941 711663990225903911651087 := by
  unfold tailWord_2078941
  simp only [CollatzResearch.WordTrace]
  refine ⟨75825207561359286700548677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50550138374239524467032451 75825207561359286700548677)
  ·
    refine ⟨14217226417754866256352877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75825207561359286700548677 14217226417754866256352877)
    ·
      refine ⟨5331459906658074846132329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14217226417754866256352877 5331459906658074846132329)
      ·
        refine ⟨3998594929993556134599247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5331459906658074846132329 3998594929993556134599247)
        ·
          refine ⟨5997892394990334201898871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3998594929993556134599247 5997892394990334201898871)
          ·
            refine ⟨8996838592485501302848307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5997892394990334201898871 8996838592485501302848307)
            ·
              refine ⟨13495257888728251954272461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8996838592485501302848307 13495257888728251954272461)
              ·
                refine ⟨5060721708273094482852173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13495257888728251954272461 5060721708273094482852173)
                ·
                  refine ⟨1897770640602410431069565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5060721708273094482852173 1897770640602410431069565)
                  ·
                    refine ⟨711663990225903911651087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1897770640602410431069565 711663990225903911651087)
                    ·
                      rfl

theorem cell22_2078941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 3, 3, 3].length) (baseStart_2078941 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2078941 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2078941 prefixEnd_2078941 := by exact prefixLift 2078941
  have htrace : WordTrace (prefixWord ++ tailWord_2078941) baseStart_2078941 baseEnd_2078941 := by
    simpa [prefixWord, tailWord_2078941, baseEnd_2078941] using wordTrace_append hprefix tailTrace_2078941
  have hstable : (prefixWord ++ tailWord_2078941).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2078941).length < 2 ^ (prefixWord ++ tailWord_2078941).sum := by decide
  have hdescent : baseEnd_2078941 < baseStart_2078941 := by decide
  rcases family_descends (prefixWord ++ tailWord_2078941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2078999 : List Nat := [1, 1, 3, 4, 1, 2, 3, 1, 6]
def baseStart_2078999 : Nat := 118140960795 + 2078999 * 2 ^ 59
def prefixEnd_2078999 : Nat := 4983230072969 + 3 ^ 40 * 2078999 * 2
def baseEnd_2078999 : Nat := 237227948270403697900303

theorem tailTrace_2078999 : CollatzResearch.WordTrace tailWord_2078999 prefixEnd_2078999 237227948270403697900303 := by
  unfold tailWord_2078999
  simp only [CollatzResearch.WordTrace]
  refine ⟨75827322995149162606160051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50551548663432775070773367 75827322995149162606160051)
  ·
    refine ⟨113740984492723743909240077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75827322995149162606160051 113740984492723743909240077)
    ·
      refine ⟨42652869184771403965965029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113740984492723743909240077 42652869184771403965965029)
      ·
        refine ⟨7997412972144638243618443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42652869184771403965965029 7997412972144638243618443)
        ·
          refine ⟨11996119458216957365427665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7997412972144638243618443 11996119458216957365427665)
          ·
            refine ⟨8997089593662718024070749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11996119458216957365427665 8997089593662718024070749)
            ·
              refine ⟨3373908597623519259026531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8997089593662718024070749 3373908597623519259026531)
              ·
                refine ⟨5060862896435278888539797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3373908597623519259026531 5060862896435278888539797)
                ·
                  refine ⟨237227948270403697900303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5060862896435278888539797 237227948270403697900303)
                  ·
                    rfl

theorem cell22_2078999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 3, 1, 6].length) (baseStart_2078999 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2078999 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2078999 prefixEnd_2078999 := by exact prefixLift 2078999
  have htrace : WordTrace (prefixWord ++ tailWord_2078999) baseStart_2078999 baseEnd_2078999 := by
    simpa [prefixWord, tailWord_2078999, baseEnd_2078999] using wordTrace_append hprefix tailTrace_2078999
  have hstable : (prefixWord ++ tailWord_2078999).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2078999).length < 2 ^ (prefixWord ++ tailWord_2078999).sum := by decide
  have hdescent : baseEnd_2078999 < baseStart_2078999 := by decide
  rcases family_descends (prefixWord ++ tailWord_2078999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2079005 : List Nat := [1, 4, 2, 3, 3, 1, 2, 1, 5]
def baseStart_2079005 : Nat := 118140960795 + 2079005 * 2 ^ 59
def prefixEnd_2079005 : Nat := 4983230072969 + 3 ^ 40 * 2079005 * 2
def baseEnd_2079005 : Nat := 237228632911276359350297

theorem tailTrace_2079005 : CollatzResearch.WordTrace tailWord_2079005 prefixEnd_2079005 237228632911276359350297 := by
  unfold tailWord_2079005
  simp only [CollatzResearch.WordTrace]
  refine ⟨75827541833127425630878469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50551694555418283753918979 75827541833127425630878469)
  ·
    refine ⟨14217664093711392305789713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75827541833127425630878469 14217664093711392305789713)
    ·
      refine ⟨10663248070283544229342285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14217664093711392305789713 10663248070283544229342285)
      ·
        refine ⟨3998718026356329086003357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10663248070283544229342285 3998718026356329086003357)
        ·
          refine ⟨1499519259883623407251259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3998718026356329086003357 1499519259883623407251259)
          ·
            refine ⟨2249278889825435110876889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1499519259883623407251259 2249278889825435110876889)
            ·
              refine ⟨1686959167369076333157667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2249278889825435110876889 1686959167369076333157667)
              ·
                refine ⟨2530438751053614499736501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1686959167369076333157667 2530438751053614499736501)
                ·
                  refine ⟨237228632911276359350297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2530438751053614499736501 237228632911276359350297)
                  ·
                    rfl

theorem cell22_2079005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 2, 1, 5].length) (baseStart_2079005 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2079005 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2079005 prefixEnd_2079005 := by exact prefixLift 2079005
  have htrace : WordTrace (prefixWord ++ tailWord_2079005) baseStart_2079005 baseEnd_2079005 := by
    simpa [prefixWord, tailWord_2079005, baseEnd_2079005] using wordTrace_append hprefix tailTrace_2079005
  have hstable : (prefixWord ++ tailWord_2079005).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2079005).length < 2 ^ (prefixWord ++ tailWord_2079005).sum := by decide
  have hdescent : baseEnd_2079005 < baseStart_2079005 := by decide
  rcases family_descends (prefixWord ++ tailWord_2079005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2079027 : List Nat := [1, 1, 1, 2, 5, 1, 1, 10]
def baseStart_2079027 : Nat := 118140960795 + 2079027 * 2 ^ 59
def prefixEnd_2079027 : Nat := 4983230072969 + 3 ^ 40 * 2079027 * 2
def baseEnd_2079027 : Nat := 79077047753714261555647

theorem tailTrace_2079027 : CollatzResearch.WordTrace tailWord_2079027 prefixEnd_2079027 79077047753714261555647 := by
  unfold tailWord_2079027
  simp only [CollatzResearch.WordTrace]
  refine ⟨75828344239047723388179335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50552229492698482258786223 75828344239047723388179335)
  ·
    refine ⟨113742516358571585082269003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75828344239047723388179335 113742516358571585082269003)
    ·
      refine ⟨170613774537857377623403505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113742516358571585082269003 170613774537857377623403505)
      ·
        refine ⟨127960330903393033217552629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170613774537857377623403505 127960330903393033217552629)
        ·
          refine ⟨11996281022193096864145559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 127960330903393033217552629 11996281022193096864145559)
          ·
            refine ⟨17994421533289645296218339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11996281022193096864145559 17994421533289645296218339)
            ·
              refine ⟨26991632299934467944327509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17994421533289645296218339 26991632299934467944327509)
              ·
                refine ⟨79077047753714261555647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 26991632299934467944327509 79077047753714261555647)
                ·
                  rfl

theorem cell22_2079027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 10].length) (baseStart_2079027 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2079027 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2079027 prefixEnd_2079027 := by exact prefixLift 2079027
  have htrace : WordTrace (prefixWord ++ tailWord_2079027) baseStart_2079027 baseEnd_2079027 := by
    simpa [prefixWord, tailWord_2079027, baseEnd_2079027] using wordTrace_append hprefix tailTrace_2079027
  have hstable : (prefixWord ++ tailWord_2079027).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2079027).length < 2 ^ (prefixWord ++ tailWord_2079027).sum := by decide
  have hdescent : baseEnd_2079027 < baseStart_2079027 := by decide
  rcases family_descends (prefixWord ++ tailWord_2079027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2079044 : List Nat := [2, 3, 4, 1, 12]
def baseStart_2079044 : Nat := 118140960795 + 2079044 * 2 ^ 59
def prefixEnd_2079044 : Nat := 4983230072969 + 3 ^ 40 * 2079044 * 2
def baseEnd_2079044 : Nat := 2928803494777143935497

theorem tailTrace_2079044 : CollatzResearch.WordTrace tailWord_2079044 prefixEnd_2079044 2928803494777143935497 := by
  unfold tailWord_2079044
  simp only [CollatzResearch.WordTrace]
  refine ⟨37914482139993067645774093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50552642853324090194365457 37914482139993067645774093)
  ·
    refine ⟨14217930802497400367165285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37914482139993067645774093 14217930802497400367165285)
    ·
      refine ⟨2665862025468262568843491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14217930802497400367165285 2665862025468262568843491)
      ·
        refine ⟨3998793038202393853265237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2665862025468262568843491 3998793038202393853265237)
        ·
          refine ⟨2928803494777143935497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 3998793038202393853265237 2928803494777143935497)
          ·
            rfl

theorem cell22_2079044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 12].length) (baseStart_2079044 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2079044 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2079044 prefixEnd_2079044 := by exact prefixLift 2079044
  have htrace : WordTrace (prefixWord ++ tailWord_2079044) baseStart_2079044 baseEnd_2079044 := by
    simpa [prefixWord, tailWord_2079044, baseEnd_2079044] using wordTrace_append hprefix tailTrace_2079044
  have hstable : (prefixWord ++ tailWord_2079044).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2079044).length < 2 ^ (prefixWord ++ tailWord_2079044).sum := by decide
  have hdescent : baseEnd_2079044 < baseStart_2079044 := by decide
  rcases family_descends (prefixWord ++ tailWord_2079044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2079061 : List Nat := [1, 3, 2, 2, 4, 2, 1, 7]
def baseStart_2079061 : Nat := 118140960795 + 2079061 * 2 ^ 59
def prefixEnd_2079061 : Nat := 4983230072969 + 3 ^ 40 * 2079061 * 2
def baseEnd_2079061 : Nat := 79078340964251510961191

theorem tailTrace_2079061 : CollatzResearch.WordTrace tailWord_2079061 prefixEnd_2079061 79078340964251510961191 := by
  unfold tailWord_2079061
  simp only [CollatzResearch.WordTrace]
  refine ⟨75829584320924547194917037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50553056213949698129944691 75829584320924547194917037)
  ·
    refine ⟨28436094120346705198093889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75829584320924547194917037 28436094120346705198093889)
    ·
      refine ⟨21327070590260028898570417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28436094120346705198093889 21327070590260028898570417)
      ·
        refine ⟨15995302942695021673927813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21327070590260028898570417 15995302942695021673927813)
        ·
          refine ⟨2999119301755316563861465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15995302942695021673927813 2999119301755316563861465)
          ·
            refine ⟨2249339476316487422896099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2999119301755316563861465 2249339476316487422896099)
            ·
              refine ⟨3374009214474731134344149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2249339476316487422896099 3374009214474731134344149)
              ·
                refine ⟨79078340964251510961191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3374009214474731134344149 79078340964251510961191)
                ·
                  rfl

theorem cell22_2079061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 1, 7].length) (baseStart_2079061 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2079061 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2079061 prefixEnd_2079061 := by exact prefixLift 2079061
  have htrace : WordTrace (prefixWord ++ tailWord_2079061) baseStart_2079061 baseEnd_2079061 := by
    simpa [prefixWord, tailWord_2079061, baseEnd_2079061] using wordTrace_append hprefix tailTrace_2079061
  have hstable : (prefixWord ++ tailWord_2079061).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2079061).length < 2 ^ (prefixWord ++ tailWord_2079061).sum := by decide
  have hdescent : baseEnd_2079061 < baseStart_2079061 := by decide
  rcases family_descends (prefixWord ++ tailWord_2079061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2079076 : List Nat := [2, 3, 1, 1, 3, 1, 3, 2, 3, 3]
def baseStart_2079076 : Nat := 118140960795 + 2079076 * 2 ^ 59
def prefixEnd_2079076 : Nat := 4983230072969 + 3 ^ 40 * 2079076 * 2
def baseEnd_2079076 : Nat := 711710203484808559525673

theorem tailTrace_2079076 : CollatzResearch.WordTrace tailWord_2079076 prefixEnd_2079076 711710203484808559525673 := by
  unfold tailWord_2079076
  simp only [CollatzResearch.WordTrace]
  refine ⟨37915065707935102378356541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50553420943913469837808721 37915065707935102378356541)
  ·
    refine ⟨14218149640475663391883703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37915065707935102378356541 14218149640475663391883703)
    ·
      refine ⟨21327224460713495087825555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14218149640475663391883703 21327224460713495087825555)
      ·
        refine ⟨31990836691070242631738333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21327224460713495087825555 31990836691070242631738333)
        ·
          refine ⟨11996563759151340986901875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31990836691070242631738333 11996563759151340986901875)
          ·
            refine ⟨17994845638727011480352813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11996563759151340986901875 17994845638727011480352813)
            ·
              refine ⟨6748067114522629305132305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17994845638727011480352813 6748067114522629305132305)
              ·
                refine ⟨5061050335891971978849229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6748067114522629305132305 5061050335891971978849229)
                ·
                  refine ⟨1897893875959489492068461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5061050335891971978849229 1897893875959489492068461)
                  ·
                    refine ⟨711710203484808559525673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1897893875959489492068461 711710203484808559525673)
                    ·
                      rfl

theorem cell22_2079076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 3, 2, 3, 3].length) (baseStart_2079076 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2079076 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2079076 prefixEnd_2079076 := by exact prefixLift 2079076
  have htrace : WordTrace (prefixWord ++ tailWord_2079076) baseStart_2079076 baseEnd_2079076 := by
    simpa [prefixWord, tailWord_2079076, baseEnd_2079076] using wordTrace_append hprefix tailTrace_2079076
  have hstable : (prefixWord ++ tailWord_2079076).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2079076).length < 2 ^ (prefixWord ++ tailWord_2079076).sum := by decide
  have hdescent : baseEnd_2079076 < baseStart_2079076 := by decide
  rcases family_descends (prefixWord ++ tailWord_2079076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2079136 : List Nat := [2, 1, 1, 4, 1, 3, 1, 4, 1, 4]
def baseStart_2079136 : Nat := 118140960795 + 2079136 * 2 ^ 59
def prefixEnd_2079136 : Nat := 4983230072969 + 3 ^ 40 * 2079136 * 2
def baseEnd_2079136 : Nat := 711730742710988403025489

theorem tailTrace_2079136 : CollatzResearch.WordTrace tailWord_2079136 prefixEnd_2079136 711730742710988403025489 := by
  unfold tailWord_2079136
  simp only [CollatzResearch.WordTrace]
  refine ⟨37916159897826417501948631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50554879863768556669264841 37916159897826417501948631)
  ·
    refine ⟨56874239846739626252922947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37916159897826417501948631 56874239846739626252922947)
    ·
      refine ⟨85311359770109439379384421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56874239846739626252922947 85311359770109439379384421)
      ·
        refine ⟨15995879956895519883634579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85311359770109439379384421 15995879956895519883634579)
        ·
          refine ⟨23993819935343279825451869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15995879956895519883634579 23993819935343279825451869)
          ·
            refine ⟨8997682475753729934544451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23993819935343279825451869 8997682475753729934544451)
            ·
              refine ⟨13496523713630594901816677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8997682475753729934544451 13496523713630594901816677)
              ·
                refine ⟨2530598196305736544090627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13496523713630594901816677 2530598196305736544090627)
                ·
                  refine ⟨3795897294458604816135941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2530598196305736544090627 3795897294458604816135941)
                  ·
                    refine ⟨711730742710988403025489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3795897294458604816135941 711730742710988403025489)
                    ·
                      rfl

theorem cell22_2079136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 4, 1, 4].length) (baseStart_2079136 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2079136 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2079136 prefixEnd_2079136 := by exact prefixLift 2079136
  have htrace : WordTrace (prefixWord ++ tailWord_2079136) baseStart_2079136 baseEnd_2079136 := by
    simpa [prefixWord, tailWord_2079136, baseEnd_2079136] using wordTrace_append hprefix tailTrace_2079136
  have hstable : (prefixWord ++ tailWord_2079136).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2079136).length < 2 ^ (prefixWord ++ tailWord_2079136).sum := by decide
  have hdescent : baseEnd_2079136 < baseStart_2079136 := by decide
  rcases family_descends (prefixWord ++ tailWord_2079136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2079363 : List Nat := [1, 1, 1, 3, 3, 1, 2, 4, 3, 3]
def baseStart_2079363 : Nat := 118140960795 + 2079363 * 2 ^ 59
def prefixEnd_2079363 : Nat := 4983230072969 + 3 ^ 40 * 2079363 * 2
def baseEnd_2079363 : Nat := 711808449450035477599793

theorem tailTrace_2079363 : CollatzResearch.WordTrace tailWord_2079363 prefixEnd_2079363 711808449450035477599793 := by
  unfold tailWord_2079363
  simp only [CollatzResearch.WordTrace]
  refine ⟨75840599165830452772410743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50560399443886968514940495 75840599165830452772410743)
  ·
    refine ⟨113760898748745679158616115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75840599165830452772410743 113760898748745679158616115)
    ·
      refine ⟨170641348123118518737924173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113760898748745679158616115 170641348123118518737924173)
      ·
        refine ⟨63990505546169444526721565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 170641348123118518737924173 63990505546169444526721565)
        ·
          refine ⟨23996439579813541697520587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63990505546169444526721565 23996439579813541697520587)
          ·
            refine ⟨35994659369720312546280881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23996439579813541697520587 35994659369720312546280881)
            ·
              refine ⟨26995994527290234409710661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35994659369720312546280881 26995994527290234409710661)
              ·
                refine ⟨5061748973866918951820749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26995994527290234409710661 5061748973866918951820749)
                ·
                  refine ⟨1898155865200094606932781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5061748973866918951820749 1898155865200094606932781)
                  ·
                    refine ⟨711808449450035477599793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1898155865200094606932781 711808449450035477599793)
                    ·
                      rfl

theorem cell22_2079363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 4, 3, 3].length) (baseStart_2079363 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2079363 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2079363 prefixEnd_2079363 := by exact prefixLift 2079363
  have htrace : WordTrace (prefixWord ++ tailWord_2079363) baseStart_2079363 baseEnd_2079363 := by
    simpa [prefixWord, tailWord_2079363, baseEnd_2079363] using wordTrace_append hprefix tailTrace_2079363
  have hstable : (prefixWord ++ tailWord_2079363).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2079363).length < 2 ^ (prefixWord ++ tailWord_2079363).sum := by decide
  have hdescent : baseEnd_2079363 < baseStart_2079363 := by decide
  rcases family_descends (prefixWord ++ tailWord_2079363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2079414 : List Nat := [5, 1, 3, 1, 2, 1, 1, 2, 3, 3]
def baseStart_2079414 : Nat := 118140960795 + 2079414 * 2 ^ 59
def prefixEnd_2079414 : Nat := 4983230072969 + 3 ^ 40 * 2079414 * 2
def baseEnd_2079414 : Nat := 711825907792288344574637

theorem tailTrace_2079414 : CollatzResearch.WordTrace tailWord_2079414 prefixEnd_2079414 711825907792288344574637 := by
  unfold tailWord_2079414
  simp only [CollatzResearch.WordTrace]
  refine ⟨4740153705540355530157331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 50561639525763792321678197 4740153705540355530157331)
  ·
    refine ⟨7110230558310533295235997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4740153705540355530157331 7110230558310533295235997)
    ·
      refine ⟨2666336459366449985713499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7110230558310533295235997 2666336459366449985713499)
      ·
        refine ⟨3999504689049674978570249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2666336459366449985713499 3999504689049674978570249)
        ·
          refine ⟨2999628516787256233927687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3999504689049674978570249 2999628516787256233927687)
          ·
            refine ⟨4499442775180884350891531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2999628516787256233927687 4499442775180884350891531)
            ·
              refine ⟨6749164162771326526337297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4499442775180884350891531 6749164162771326526337297)
              ·
                refine ⟨5061873122078494894752973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6749164162771326526337297 5061873122078494894752973)
                ·
                  refine ⟨1898202420779435585532365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5061873122078494894752973 1898202420779435585532365)
                  ·
                    refine ⟨711825907792288344574637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1898202420779435585532365 711825907792288344574637)
                    ·
                      rfl

theorem cell22_2079414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 1, 2, 3, 3].length) (baseStart_2079414 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2079414 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2079414 prefixEnd_2079414 := by exact prefixLift 2079414
  have htrace : WordTrace (prefixWord ++ tailWord_2079414) baseStart_2079414 baseEnd_2079414 := by
    simpa [prefixWord, tailWord_2079414, baseEnd_2079414] using wordTrace_append hprefix tailTrace_2079414
  have hstable : (prefixWord ++ tailWord_2079414).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2079414).length < 2 ^ (prefixWord ++ tailWord_2079414).sum := by decide
  have hdescent : baseEnd_2079414 < baseStart_2079414 := by decide
  rcases family_descends (prefixWord ++ tailWord_2079414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2079423 : List Nat := [1, 1, 2, 2, 2, 4, 2, 1, 3, 4]
def baseStart_2079423 : Nat := 118140960795 + 2079423 * 2 ^ 59
def prefixEnd_2079423 : Nat := 4983230072969 + 3 ^ 40 * 2079423 * 2
def baseEnd_2079423 : Nat := 711828988676215321099609

theorem tailTrace_2079423 : CollatzResearch.WordTrace tailWord_2079423 prefixEnd_2079423 711828988676215321099609 := by
  unfold tailWord_2079423
  simp only [CollatzResearch.WordTrace]
  refine ⟨75842787545613083019594923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50561858363742055346396615 75842787545613083019594923)
  ·
    refine ⟨113764181318419624529392385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75842787545613083019594923 113764181318419624529392385)
    ·
      refine ⟨85323135988814718397044289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113764181318419624529392385 85323135988814718397044289)
      ·
        refine ⟨63992351991611038797783217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85323135988814718397044289 63992351991611038797783217)
        ·
          refine ⟨47994263993708279098337413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63992351991611038797783217 47994263993708279098337413)
          ·
            refine ⟨8998924498820302330938265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47994263993708279098337413 8998924498820302330938265)
            ·
              refine ⟨6749193374115226748203699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8998924498820302330938265 6749193374115226748203699)
              ·
                refine ⟨10123790061172840122305549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6749193374115226748203699 10123790061172840122305549)
                ·
                  refine ⟨3796421272939815045864581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10123790061172840122305549 3796421272939815045864581)
                  ·
                    refine ⟨711828988676215321099609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3796421272939815045864581 711828988676215321099609)
                    ·
                      rfl

theorem cell22_2079423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 2, 1, 3, 4].length) (baseStart_2079423 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2079423 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2079423 prefixEnd_2079423 := by exact prefixLift 2079423
  have htrace : WordTrace (prefixWord ++ tailWord_2079423) baseStart_2079423 baseEnd_2079423 := by
    simpa [prefixWord, tailWord_2079423, baseEnd_2079423] using wordTrace_append hprefix tailTrace_2079423
  have hstable : (prefixWord ++ tailWord_2079423).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2079423).length < 2 ^ (prefixWord ++ tailWord_2079423).sum := by decide
  have hdescent : baseEnd_2079423 < baseStart_2079423 := by decide
  rcases family_descends (prefixWord ++ tailWord_2079423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2079444 : List Nat := [2, 4, 1, 3, 3, 1, 1, 2, 5]
def baseStart_2079444 : Nat := 118140960795 + 2079444 * 2 ^ 59
def prefixEnd_2079444 : Nat := 4983230072969 + 3 ^ 40 * 2079444 * 2
def baseEnd_2079444 : Nat := 237278725801792755441515

theorem tailTrace_2079444 : CollatzResearch.WordTrace tailWord_2079444 prefixEnd_2079444 237278725801792755441515 := by
  unfold tailWord_2079444
  simp only [CollatzResearch.WordTrace]
  refine ⟨37921776739268501803054693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50562368985691335737406257 37921776739268501803054693)
  ·
    refine ⟨7110333138612844088072755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37921776739268501803054693 7110333138612844088072755)
    ·
      refine ⟨10665499707919266132109133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7110333138612844088072755 10665499707919266132109133)
      ·
        refine ⟨3999562390469724799540925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10665499707919266132109133 3999562390469724799540925)
        ·
          refine ⟨1499835896426146799827847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3999562390469724799540925 1499835896426146799827847)
          ·
            refine ⟨2249753844639220199741771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1499835896426146799827847 2249753844639220199741771)
            ·
              refine ⟨3374630766958830299612657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2249753844639220199741771 3374630766958830299612657)
              ·
                refine ⟨2530973075219122724709493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3374630766958830299612657 2530973075219122724709493)
                ·
                  refine ⟨237278725801792755441515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2530973075219122724709493 237278725801792755441515)
                  ·
                    rfl

theorem cell22_2079444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 1, 2, 5].length) (baseStart_2079444 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2079444 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2079444 prefixEnd_2079444 := by exact prefixLift 2079444
  have htrace : WordTrace (prefixWord ++ tailWord_2079444) baseStart_2079444 baseEnd_2079444 := by
    simpa [prefixWord, tailWord_2079444, baseEnd_2079444] using wordTrace_append hprefix tailTrace_2079444
  have hstable : (prefixWord ++ tailWord_2079444).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2079444).length < 2 ^ (prefixWord ++ tailWord_2079444).sum := by decide
  have hdescent : baseEnd_2079444 < baseStart_2079444 := by decide
  rcases family_descends (prefixWord ++ tailWord_2079444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2079451 : List Nat := [1, 1, 1, 1, 1, 1, 1, 3, 2, 10]
def baseStart_2079451 : Nat := 118140960795 + 2079451 * 2 ^ 59
def prefixEnd_2079451 : Nat := 4983230072969 + 3 ^ 40 * 2079451 * 2
def baseEnd_2079451 : Nat := 711838573648432581399523

theorem tailTrace_2079451 : CollatzResearch.WordTrace tailWord_2079451 prefixEnd_2079451 711838573648432581399523 := by
  unfold tailWord_2079451
  simp only [CollatzResearch.WordTrace]
  refine ⟨75843808789511643801614207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50562539193007762534409471 75843808789511643801614207)
  ·
    refine ⟨113765713184267465702421311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75843808789511643801614207 113765713184267465702421311)
    ·
      refine ⟨170648569776401198553631967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113765713184267465702421311 170648569776401198553631967)
      ·
        refine ⟨255972854664601797830447951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170648569776401198553631967 255972854664601797830447951)
        ·
          refine ⟨383959281996902696745671927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255972854664601797830447951 383959281996902696745671927)
          ·
            refine ⟨575938922995354045118507891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 383959281996902696745671927 575938922995354045118507891)
            ·
              refine ⟨863908384493031067677761837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 575938922995354045118507891 863908384493031067677761837)
              ·
                refine ⟨323965644184886650379160689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 863908384493031067677761837 323965644184886650379160689)
                ·
                  refine ⟨242974233138664987784370517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 323965644184886650379160689 242974233138664987784370517)
                  ·
                    refine ⟨711838573648432581399523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 242974233138664987784370517 711838573648432581399523)
                    ·
                      rfl

theorem cell22_2079451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 10].length) (baseStart_2079451 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2079451 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2079451 prefixEnd_2079451 := by exact prefixLift 2079451
  have htrace : WordTrace (prefixWord ++ tailWord_2079451) baseStart_2079451 baseEnd_2079451 := by
    simpa [prefixWord, tailWord_2079451, baseEnd_2079451] using wordTrace_append hprefix tailTrace_2079451
  have hstable : (prefixWord ++ tailWord_2079451).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2079451).length < 2 ^ (prefixWord ++ tailWord_2079451).sum := by decide
  have hdescent : baseEnd_2079451 < baseStart_2079451 := by decide
  rcases family_descends (prefixWord ++ tailWord_2079451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2079455 : List Nat := [1, 1, 2, 3, 2, 3, 2, 4, 4]
def baseStart_2079455 : Nat := 118140960795 + 2079455 * 2 ^ 59
def prefixEnd_2079455 : Nat := 4983230072969 + 3 ^ 40 * 2079455 * 2
def baseEnd_2079455 : Nat := 237279980976725968099837

theorem tailTrace_2079455 : CollatzResearch.WordTrace tailWord_2079455 prefixEnd_2079455 237279980976725968099837 := by
  unfold tailWord_2079455
  simp only [CollatzResearch.WordTrace]
  refine ⟨75843954681497152484759819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50562636454331434989839879 75843954681497152484759819)
  ·
    refine ⟨113765932022245728727139729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75843954681497152484759819 113765932022245728727139729)
    ·
      refine ⟨85324449016684296545354797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113765932022245728727139729 85324449016684296545354797)
      ·
        refine ⟨31996668381256611204508049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85324449016684296545354797 31996668381256611204508049)
        ·
          refine ⟨23997501285942458403381037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31996668381256611204508049 23997501285942458403381037)
          ·
            refine ⟨8999062982228421901267889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23997501285942458403381037 8999062982228421901267889)
            ·
              refine ⟨6749297236671316425950917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8999062982228421901267889 6749297236671316425950917)
              ·
                refine ⟨1265493231875871829865797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6749297236671316425950917 1265493231875871829865797)
                ·
                  refine ⟨237279980976725968099837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1265493231875871829865797 237279980976725968099837)
                  ·
                    rfl

theorem cell22_2079455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 2, 4, 4].length) (baseStart_2079455 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2079455 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2079455 prefixEnd_2079455 := by exact prefixLift 2079455
  have htrace : WordTrace (prefixWord ++ tailWord_2079455) baseStart_2079455 baseEnd_2079455 := by
    simpa [prefixWord, tailWord_2079455, baseEnd_2079455] using wordTrace_append hprefix tailTrace_2079455
  have hstable : (prefixWord ++ tailWord_2079455).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2079455).length < 2 ^ (prefixWord ++ tailWord_2079455).sum := by decide
  have hdescent : baseEnd_2079455 < baseStart_2079455 := by decide
  rcases family_descends (prefixWord ++ tailWord_2079455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2079470 : List Nat := [4, 1, 2, 1, 1, 3, 3, 1, 1, 5]
def baseStart_2079470 : Nat := 118140960795 + 2079470 * 2 ^ 59
def prefixEnd_2079470 : Nat := 4983230072969 + 3 ^ 40 * 2079470 * 2
def baseEnd_2079470 : Nat := 711845077736722865174465

theorem tailTrace_2079470 : CollatzResearch.WordTrace tailWord_2079470 prefixEnd_2079470 711845077736722865174465 := by
  unfold tailWord_2079470
  simp only [CollatzResearch.WordTrace]
  refine ⟨9480562722055351255819483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50563001184295206697703909 9480562722055351255819483)
  ·
    refine ⟨14220844083083026883729225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9480562722055351255819483 14220844083083026883729225)
    ·
      refine ⟨10665633062312270162796919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14220844083083026883729225 10665633062312270162796919)
      ·
        refine ⟨15998449593468405244195379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10665633062312270162796919 15998449593468405244195379)
        ·
          refine ⟨23997674390202607866293069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15998449593468405244195379 23997674390202607866293069)
          ·
            refine ⟨8999127896325977949859901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23997674390202607866293069 8999127896325977949859901)
            ·
              refine ⟨3374672961122241731197463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8999127896325977949859901 3374672961122241731197463)
              ·
                refine ⟨5062009441683362596796195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3374672961122241731197463 5062009441683362596796195)
                ·
                  refine ⟨7593014162525043895194293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5062009441683362596796195 7593014162525043895194293)
                  ·
                    refine ⟨711845077736722865174465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7593014162525043895194293 711845077736722865174465)
                    ·
                      rfl

theorem cell22_2079470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 3, 1, 1, 5].length) (baseStart_2079470 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2079470 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2079470 prefixEnd_2079470 := by exact prefixLift 2079470
  have htrace : WordTrace (prefixWord ++ tailWord_2079470) baseStart_2079470 baseEnd_2079470 := by
    simpa [prefixWord, tailWord_2079470, baseEnd_2079470] using wordTrace_append hprefix tailTrace_2079470
  have hstable : (prefixWord ++ tailWord_2079470).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2079470).length < 2 ^ (prefixWord ++ tailWord_2079470).sum := by decide
  have hdescent : baseEnd_2079470 < baseStart_2079470 := by decide
  rcases family_descends (prefixWord ++ tailWord_2079470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2079506 : List Nat := [3, 2, 4, 1, 2, 1, 3, 2, 4]
def baseStart_2079506 : Nat := 118140960795 + 2079506 * 2 ^ 59
def prefixEnd_2079506 : Nat := 4983230072969 + 3 ^ 40 * 2079506 * 2
def baseEnd_2079506 : Nat := 237285800424143590424785

theorem tailTrace_2079506 : CollatzResearch.WordTrace tailWord_2079506 prefixEnd_2079506 237285800424143590424785 := by
  unfold tailWord_2079506
  simp only [CollatzResearch.WordTrace]
  refine ⟨18961453701078097048716593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50563876536208258796577581 18961453701078097048716593)
  ·
    refine ⟨14221090275808572786537445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18961453701078097048716593 14221090275808572786537445)
    ·
      refine ⟨2666454426714107397475771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14221090275808572786537445 2666454426714107397475771)
      ·
        refine ⟨3999681640071161096213657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2666454426714107397475771 3999681640071161096213657)
        ·
          refine ⟨2999761230053370822160243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3999681640071161096213657 2999761230053370822160243)
          ·
            refine ⟨4499641845080056233240365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2999761230053370822160243 4499641845080056233240365)
            ·
              refine ⟨1687365691905021087465137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4499641845080056233240365 1687365691905021087465137)
              ·
                refine ⟨1265524268928765815598853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1687365691905021087465137 1265524268928765815598853)
                ·
                  refine ⟨237285800424143590424785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1265524268928765815598853 237285800424143590424785)
                  ·
                    rfl

theorem cell22_2079506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 3, 2, 4].length) (baseStart_2079506 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2079506 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2079506 prefixEnd_2079506 := by exact prefixLift 2079506
  have htrace : WordTrace (prefixWord ++ tailWord_2079506) baseStart_2079506 baseEnd_2079506 := by
    simpa [prefixWord, tailWord_2079506, baseEnd_2079506] using wordTrace_append hprefix tailTrace_2079506
  have hstable : (prefixWord ++ tailWord_2079506).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2079506).length < 2 ^ (prefixWord ++ tailWord_2079506).sum := by decide
  have hdescent : baseEnd_2079506 < baseStart_2079506 := by decide
  rcases family_descends (prefixWord ++ tailWord_2079506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2079517 : List Nat := [1, 4, 2, 4, 1, 1, 2, 7]
def baseStart_2079517 : Nat := 118140960795 + 2079517 * 2 ^ 59
def prefixEnd_2079517 : Nat := 4983230072969 + 3 ^ 40 * 2079517 * 2
def baseEnd_2079517 : Nat := 79095685199692267694369

theorem tailTrace_2079517 : CollatzResearch.WordTrace tailWord_2079517 prefixEnd_2079517 79095685199692267694369 := by
  unfold tailWord_2079517
  simp only [CollatzResearch.WordTrace]
  refine ⟨75846216007272537073516805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50564144004848358049011203 75846216007272537073516805)
  ·
    refine ⟨14221165501363600701284401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75846216007272537073516805 14221165501363600701284401)
    ·
      refine ⟨10665874126022700525963301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14221165501363600701284401 10665874126022700525963301)
      ·
        refine ⟨1999851398629256348618119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10665874126022700525963301 1999851398629256348618119)
        ·
          refine ⟨2999777097943884522927179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1999851398629256348618119 2999777097943884522927179)
          ·
            refine ⟨4499665646915826784390769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2999777097943884522927179 4499665646915826784390769)
            ·
              refine ⟨3374749235186870088293077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4499665646915826784390769 3374749235186870088293077)
              ·
                refine ⟨79095685199692267694369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3374749235186870088293077 79095685199692267694369)
                ·
                  rfl

theorem cell22_2079517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 2, 7].length) (baseStart_2079517 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2079517 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2079517 prefixEnd_2079517 := by exact prefixLift 2079517
  have htrace : WordTrace (prefixWord ++ tailWord_2079517) baseStart_2079517 baseEnd_2079517 := by
    simpa [prefixWord, tailWord_2079517, baseEnd_2079517] using wordTrace_append hprefix tailTrace_2079517
  have hstable : (prefixWord ++ tailWord_2079517).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2079517).length < 2 ^ (prefixWord ++ tailWord_2079517).sum := by decide
  have hdescent : baseEnd_2079517 < baseStart_2079517 := by decide
  rcases family_descends (prefixWord ++ tailWord_2079517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2079575 : List Nat := [1, 1, 3, 2, 4, 1, 1, 2, 3, 4]
def baseStart_2079575 : Nat := 118140960795 + 2079575 * 2 ^ 59
def prefixEnd_2079575 : Nat := 4983230072969 + 3 ^ 40 * 2079575 * 2
def baseEnd_2079575 : Nat := 711881021382537591299143

theorem tailTrace_2079575 : CollatzResearch.WordTrace tailWord_2079575 prefixEnd_2079575 711881021382537591299143 := by
  unfold tailWord_2079575
  simp only [CollatzResearch.WordTrace]
  refine ⟨75848331441062412979128179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50565554294041608652752119 75848331441062412979128179)
  ·
    refine ⟨113772497161593619468692269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75848331441062412979128179 113772497161593619468692269)
    ·
      refine ⟨42664686435597607300759601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113772497161593619468692269 42664686435597607300759601)
      ·
        refine ⟨31998514826698205475569701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42664686435597607300759601 31998514826698205475569701)
        ·
          refine ⟨5999721530005913526669319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31998514826698205475569701 5999721530005913526669319)
          ·
            refine ⟨8999582295008870290003979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5999721530005913526669319 8999582295008870290003979)
            ·
              refine ⟨13499373442513305435005969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8999582295008870290003979 13499373442513305435005969)
              ·
                refine ⟨10124530081884979076254477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13499373442513305435005969 10124530081884979076254477)
                ·
                  refine ⟨3796698780706867153595429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10124530081884979076254477 3796698780706867153595429)
                  ·
                    refine ⟨711881021382537591299143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3796698780706867153595429 711881021382537591299143)
                    ·
                      rfl

theorem cell22_2079575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 2, 3, 4].length) (baseStart_2079575 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2079575 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2079575 prefixEnd_2079575 := by exact prefixLift 2079575
  have htrace : WordTrace (prefixWord ++ tailWord_2079575) baseStart_2079575 baseEnd_2079575 := by
    simpa [prefixWord, tailWord_2079575, baseEnd_2079575] using wordTrace_append hprefix tailTrace_2079575
  have hstable : (prefixWord ++ tailWord_2079575).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2079575).length < 2 ^ (prefixWord ++ tailWord_2079575).sum := by decide
  have hdescent : baseEnd_2079575 < baseStart_2079575 := by decide
  rcases family_descends (prefixWord ++ tailWord_2079575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2079609 : List Nat := [1, 2, 1, 3, 2, 5, 2, 1, 1, 4]
def baseStart_2079609 : Nat := 118140960795 + 2079609 * 2 ^ 59
def prefixEnd_2079609 : Nat := 4983230072969 + 3 ^ 40 * 2079609 * 2
def baseEnd_2079609 : Nat := 711892660277372835949039

theorem tailTrace_2079609 : CollatzResearch.WordTrace tailWord_2079609 prefixEnd_2079609 711892660277372835949039 := by
  unfold tailWord_2079609
  simp only [CollatzResearch.WordTrace]
  refine ⟨75849571522939236785865881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50566381015292824523910587 75849571522939236785865881)
  ·
    refine ⟨56887178642204427589399411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75849571522939236785865881 56887178642204427589399411)
    ·
      refine ⟨85330767963306641384099117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56887178642204427589399411 85330767963306641384099117)
      ·
        refine ⟨31999037986239990519037169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85330767963306641384099117 31999037986239990519037169)
        ·
          refine ⟨23999278489679992889277877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31999037986239990519037169 23999278489679992889277877)
          ·
            refine ⟨2249932358407499333369801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23999278489679992889277877 2249932358407499333369801)
            ·
              refine ⟨1687449268805624500027351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2249932358407499333369801 1687449268805624500027351)
              ·
                refine ⟨2531173903208436750041027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1687449268805624500027351 2531173903208436750041027)
                ·
                  refine ⟨3796760854812655125061541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2531173903208436750041027 3796760854812655125061541)
                  ·
                    refine ⟨711892660277372835949039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3796760854812655125061541 711892660277372835949039)
                    ·
                      rfl

theorem cell22_2079609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 2, 1, 1, 4].length) (baseStart_2079609 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2079609 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2079609 prefixEnd_2079609 := by exact prefixLift 2079609
  have htrace : WordTrace (prefixWord ++ tailWord_2079609) baseStart_2079609 baseEnd_2079609 := by
    simpa [prefixWord, tailWord_2079609, baseEnd_2079609] using wordTrace_append hprefix tailTrace_2079609
  have hstable : (prefixWord ++ tailWord_2079609).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2079609).length < 2 ^ (prefixWord ++ tailWord_2079609).sum := by decide
  have hdescent : baseEnd_2079609 < baseStart_2079609 := by decide
  rcases family_descends (prefixWord ++ tailWord_2079609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2079620 : List Nat := [2, 3, 2, 1, 1, 1, 1, 3, 4, 4]
def baseStart_2079620 : Nat := 118140960795 + 2079620 * 2 ^ 59
def prefixEnd_2079620 : Nat := 4983230072969 + 3 ^ 40 * 2079620 * 2
def baseEnd_2079620 : Nat := 711896425802172473924005

theorem tailTrace_2079620 : CollatzResearch.WordTrace tailWord_2079620 prefixEnd_2079620 711896425802172473924005 := by
  unfold tailWord_2079620
  simp only [CollatzResearch.WordTrace]
  refine ⟨37924986362949692832258157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50566648483932923776344209 37924986362949692832258157)
  ·
    refine ⟨14221869886106134812096809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37924986362949692832258157 14221869886106134812096809)
    ·
      refine ⟨10666402414579601109072607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14221869886106134812096809 10666402414579601109072607)
      ·
        refine ⟨15999603621869401663608911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10666402414579601109072607 15999603621869401663608911)
        ·
          refine ⟨23999405432804102495413367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15999603621869401663608911 23999405432804102495413367)
          ·
            refine ⟨35999108149206153743120051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23999405432804102495413367 35999108149206153743120051)
            ·
              refine ⟨53998662223809230614680077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35999108149206153743120051 53998662223809230614680077)
              ·
                refine ⟨20249498333928461480505029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53998662223809230614680077 20249498333928461480505029)
                ·
                  refine ⟨3796780937611586527594693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20249498333928461480505029 3796780937611586527594693)
                  ·
                    refine ⟨711896425802172473924005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3796780937611586527594693 711896425802172473924005)
                    ·
                      rfl

theorem cell22_2079620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 3, 4, 4].length) (baseStart_2079620 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2079620 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2079620 prefixEnd_2079620 := by exact prefixLift 2079620
  have htrace : WordTrace (prefixWord ++ tailWord_2079620) baseStart_2079620 baseEnd_2079620 := by
    simpa [prefixWord, tailWord_2079620, baseEnd_2079620] using wordTrace_append hprefix tailTrace_2079620
  have hstable : (prefixWord ++ tailWord_2079620).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2079620).length < 2 ^ (prefixWord ++ tailWord_2079620).sum := by decide
  have hdescent : baseEnd_2079620 < baseStart_2079620 := by decide
  rcases family_descends (prefixWord ++ tailWord_2079620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2079639 : List Nat := [1, 1, 3, 3, 1, 2, 5, 1, 2, 3]
def baseStart_2079639 : Nat := 118140960795 + 2079639 * 2 ^ 59
def prefixEnd_2079639 : Nat := 4983230072969 + 3 ^ 40 * 2079639 * 2
def baseEnd_2079639 : Nat := 711902929890462757698947

theorem tailTrace_2079639 : CollatzResearch.WordTrace tailWord_2079639 prefixEnd_2079639 711902929890462757698947 := by
  unfold tailWord_2079639
  simp only [CollatzResearch.WordTrace]
  refine ⟨75850665712830551909457971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50567110475220367939638647 75850665712830551909457971)
  ·
    refine ⟨113775998569245827864186957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75850665712830551909457971 113775998569245827864186957)
    ·
      refine ⟨42665999463467185449070109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113775998569245827864186957 42665999463467185449070109)
      ·
        refine ⟨15999749798800194543401291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42665999463467185449070109 15999749798800194543401291)
        ·
          refine ⟨23999624698200291815101937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15999749798800194543401291 23999624698200291815101937)
          ·
            refine ⟨17999718523650218861326453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23999624698200291815101937 17999718523650218861326453)
            ·
              refine ⟨1687473611592208018249355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17999718523650218861326453 1687473611592208018249355)
              ·
                refine ⟨2531210417388312027374033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1687473611592208018249355 2531210417388312027374033)
                ·
                  refine ⟨1898407813041234020530525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2531210417388312027374033 1898407813041234020530525)
                  ·
                    refine ⟨711902929890462757698947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1898407813041234020530525 711902929890462757698947)
                    ·
                      rfl

theorem cell22_2079639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 5, 1, 2, 3].length) (baseStart_2079639 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2079639 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2079639 prefixEnd_2079639 := by exact prefixLift 2079639
  have htrace : WordTrace (prefixWord ++ tailWord_2079639) baseStart_2079639 baseEnd_2079639 := by
    simpa [prefixWord, tailWord_2079639, baseEnd_2079639] using wordTrace_append hprefix tailTrace_2079639
  have hstable : (prefixWord ++ tailWord_2079639).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2079639).length < 2 ^ (prefixWord ++ tailWord_2079639).sum := by decide
  have hdescent : baseEnd_2079639 < baseStart_2079639 := by decide
  rcases family_descends (prefixWord ++ tailWord_2079639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2079680 : List Nat := [2, 1, 1, 2, 3, 3, 2, 1, 7]
def baseStart_2079680 : Nat := 118140960795 + 2079680 * 2 ^ 59
def prefixEnd_2079680 : Nat := 4983230072969 + 3 ^ 40 * 2079680 * 2
def baseEnd_2079680 : Nat := 237305655009450772474607

theorem tailTrace_2079680 : CollatzResearch.WordTrace tailWord_2079680 prefixEnd_2079680 237305655009450772474607 := by
  unfold tailWord_2079680
  simp only [CollatzResearch.WordTrace]
  refine ⟨37926080552841007955850247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50568107403788010607800329 37926080552841007955850247)
  ·
    refine ⟨56889120829261511933775371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37926080552841007955850247 56889120829261511933775371)
    ·
      refine ⟨85333681243892267900663057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56889120829261511933775371 85333681243892267900663057)
      ·
        refine ⟨64000260932919200925497293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85333681243892267900663057 64000260932919200925497293)
        ·
          refine ⟨24000097849844700347061485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64000260932919200925497293 24000097849844700347061485)
          ·
            refine ⟨9000036693691762630148057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24000097849844700347061485 9000036693691762630148057)
            ·
              refine ⟨6750027520268821972611043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9000036693691762630148057 6750027520268821972611043)
              ·
                refine ⟨10125041280403232958916565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6750027520268821972611043 10125041280403232958916565)
                ·
                  refine ⟨237305655009450772474607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10125041280403232958916565 237305655009450772474607)
                  ·
                    rfl

theorem cell22_2079680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 2, 1, 7].length) (baseStart_2079680 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2079680 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2079680 prefixEnd_2079680 := by exact prefixLift 2079680
  have htrace : WordTrace (prefixWord ++ tailWord_2079680) baseStart_2079680 baseEnd_2079680 := by
    simpa [prefixWord, tailWord_2079680, baseEnd_2079680] using wordTrace_append hprefix tailTrace_2079680
  have hstable : (prefixWord ++ tailWord_2079680).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2079680).length < 2 ^ (prefixWord ++ tailWord_2079680).sum := by decide
  have hdescent : baseEnd_2079680 < baseStart_2079680 := by decide
  rcases family_descends (prefixWord ++ tailWord_2079680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2079746 : List Nat := [3, 4, 1, 3, 1, 1, 1, 1, 2, 5]
def baseStart_2079746 : Nat := 118140960795 + 2079746 * 2 ^ 59
def prefixEnd_2079746 : Nat := 4983230072969 + 3 ^ 40 * 2079746 * 2
def baseEnd_2079746 : Nat := 711939558177150145273619

theorem tailTrace_2079746 : CollatzResearch.WordTrace tailWord_2079746 prefixEnd_2079746 711939558177150145273619 := by
  unfold tailWord_2079746
  simp only [CollatzResearch.WordTrace]
  refine ⟨18963642080860727295900773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50569712215628606122402061 18963642080860727295900773)
  ·
    refine ⟨3555682890161386367981395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18963642080860727295900773 3555682890161386367981395)
    ·
      refine ⟨5333524335242079551972093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3555682890161386367981395 5333524335242079551972093)
      ·
        refine ⟨2000071625715779831989535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5333524335242079551972093 2000071625715779831989535)
        ·
          refine ⟨3000107438573669747984303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2000071625715779831989535 3000107438573669747984303)
          ·
            refine ⟨4500161157860504621976455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3000107438573669747984303 4500161157860504621976455)
            ·
              refine ⟨6750241736790756932964683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4500161157860504621976455 6750241736790756932964683)
              ·
                refine ⟨10125362605186135399447025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6750241736790756932964683 10125362605186135399447025)
                ·
                  refine ⟨7594021953889601549585269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10125362605186135399447025 7594021953889601549585269)
                  ·
                    refine ⟨711939558177150145273619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7594021953889601549585269 711939558177150145273619)
                    ·
                      rfl

theorem cell22_2079746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 1, 1, 2, 5].length) (baseStart_2079746 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2079746 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2079746 prefixEnd_2079746 := by exact prefixLift 2079746
  have htrace : WordTrace (prefixWord ++ tailWord_2079746) baseStart_2079746 baseEnd_2079746 := by
    simpa [prefixWord, tailWord_2079746, baseEnd_2079746] using wordTrace_append hprefix tailTrace_2079746
  have hstable : (prefixWord ++ tailWord_2079746).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2079746).length < 2 ^ (prefixWord ++ tailWord_2079746).sum := by decide
  have hdescent : baseEnd_2079746 < baseStart_2079746 := by decide
  rcases family_descends (prefixWord ++ tailWord_2079746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2079821 : List Nat := [1, 6, 1, 1, 1, 4, 2, 6]
def baseStart_2079821 : Nat := 118140960795 + 2079821 * 2 ^ 59
def prefixEnd_2079821 : Nat := 4983230072969 + 3 ^ 40 * 2079821 * 2
def baseEnd_2079821 : Nat := 79107248023319438849821

theorem tailTrace_2079821 : CollatzResearch.WordTrace tailWord_2079821 prefixEnd_2079821 79107248023319438849821 := by
  unfold tailWord_2079821
  simp only [CollatzResearch.WordTrace]
  refine ⟨75857303798171196992583317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50571535865447464661722211 75857303798171196992583317)
  ·
    refine ⟨3555811115539274859027343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 75857303798171196992583317 3555811115539274859027343)
    ·
      refine ⟨5333716673308912288541015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3555811115539274859027343 5333716673308912288541015)
      ·
        refine ⟨8000575009963368432811523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5333716673308912288541015 8000575009963368432811523)
        ·
          refine ⟨12000862514945052649217285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8000575009963368432811523 12000862514945052649217285)
          ·
            refine ⟨2250161721552197371728241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12000862514945052649217285 2250161721552197371728241)
            ·
              refine ⟨1687621291164148028796181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2250161721552197371728241 1687621291164148028796181)
              ·
                refine ⟨79107248023319438849821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1687621291164148028796181 79107248023319438849821)
                ·
                  rfl

theorem cell22_2079821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 2, 6].length) (baseStart_2079821 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2079821 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2079821 prefixEnd_2079821 := by exact prefixLift 2079821
  have htrace : WordTrace (prefixWord ++ tailWord_2079821) baseStart_2079821 baseEnd_2079821 := by
    simpa [prefixWord, tailWord_2079821, baseEnd_2079821] using wordTrace_append hprefix tailTrace_2079821
  have hstable : (prefixWord ++ tailWord_2079821).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2079821).length < 2 ^ (prefixWord ++ tailWord_2079821).sum := by decide
  have hdescent : baseEnd_2079821 < baseStart_2079821 := by decide
  rcases family_descends (prefixWord ++ tailWord_2079821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2079956 : List Nat := [2, 4, 1, 4, 1, 1, 9]
def baseStart_2079956 : Nat := 118140960795 + 2079956 * 2 ^ 59
def prefixEnd_2079956 : Nat := 4983230072969 + 3 ^ 40 * 2079956 * 2
def baseEnd_2079956 : Nat := 26370794276621466574925

theorem tailTrace_2079956 : CollatzResearch.WordTrace tailWord_2079956 prefixEnd_2079956 26370794276621466574925 := by
  unfold tailWord_2079956
  simp only [CollatzResearch.WordTrace]
  refine ⟨37931113826341057524373861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50574818435121410032498481 37931113826341057524373861)
  ·
    refine ⟨7112083842438948285820099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37931113826341057524373861 7112083842438948285820099)
    ·
      refine ⟨10668125763658422428730149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7112083842438948285820099 10668125763658422428730149)
      ·
        refine ⟨2000273580685954205386903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10668125763658422428730149 2000273580685954205386903)
        ·
          refine ⟨3000410371028931308080355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2000273580685954205386903 3000410371028931308080355)
          ·
            refine ⟨4500615556543396962120533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3000410371028931308080355 4500615556543396962120533)
            ·
              refine ⟨26370794276621466574925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4500615556543396962120533 26370794276621466574925)
              ·
                rfl

theorem cell22_2079956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 9].length) (baseStart_2079956 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2079956 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2079956 prefixEnd_2079956 := by exact prefixLift 2079956
  have htrace : WordTrace (prefixWord ++ tailWord_2079956) baseStart_2079956 baseEnd_2079956 := by
    simpa [prefixWord, tailWord_2079956, baseEnd_2079956] using wordTrace_append hprefix tailTrace_2079956
  have hstable : (prefixWord ++ tailWord_2079956).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2079956).length < 2 ^ (prefixWord ++ tailWord_2079956).sum := by decide
  have hdescent : baseEnd_2079956 < baseStart_2079956 := by decide
  rcases family_descends (prefixWord ++ tailWord_2079956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2079960 : List Nat := [2, 1, 2, 2, 6, 1, 1, 2, 2, 3]
def baseStart_2079960 : Nat := 118140960795 + 2079960 * 2 ^ 59
def prefixEnd_2079960 : Nat := 4983230072969 + 3 ^ 40 * 2079960 * 2
def baseEnd_2079960 : Nat := 712012814750524920422963

theorem tailTrace_2079960 : CollatzResearch.WordTrace tailWord_2079960 prefixEnd_2079960 712012814750524920422963 := by
  unfold tailWord_2079960
  simp only [CollatzResearch.WordTrace]
  refine ⟨37931186772333811865946667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50574915696445082487928889 37931186772333811865946667)
  ·
    refine ⟨56896780158500717798920001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37931186772333811865946667 56896780158500717798920001)
    ·
      refine ⟨42672585118875538349190001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56896780158500717798920001 42672585118875538349190001)
      ·
        refine ⟨32004438839156653761892501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42672585118875538349190001 32004438839156653761892501)
        ·
          refine ⟨1500208070585468145088711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 32004438839156653761892501 1500208070585468145088711)
          ·
            refine ⟨2250312105878202217633067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1500208070585468145088711 2250312105878202217633067)
            ·
              refine ⟨3375468158817303326449601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2250312105878202217633067 3375468158817303326449601)
              ·
                refine ⟨2531601119112977494837201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3375468158817303326449601 2531601119112977494837201)
                ·
                  refine ⟨1898700839334733121127901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2531601119112977494837201 1898700839334733121127901)
                  ·
                    refine ⟨712012814750524920422963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1898700839334733121127901 712012814750524920422963)
                    ·
                      rfl

theorem cell22_2079960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 1, 2, 2, 3].length) (baseStart_2079960 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2079960 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2079960 prefixEnd_2079960 := by exact prefixLift 2079960
  have htrace : WordTrace (prefixWord ++ tailWord_2079960) baseStart_2079960 baseEnd_2079960 := by
    simpa [prefixWord, tailWord_2079960, baseEnd_2079960] using wordTrace_append hprefix tailTrace_2079960
  have hstable : (prefixWord ++ tailWord_2079960).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2079960).length < 2 ^ (prefixWord ++ tailWord_2079960).sum := by decide
  have hdescent : baseEnd_2079960 < baseStart_2079960 := by decide
  rcases family_descends (prefixWord ++ tailWord_2079960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2080044 : List Nat := [2, 2, 1, 1, 1, 3, 1, 5, 1, 5]
def baseStart_2080044 : Nat := 118140960795 + 2080044 * 2 ^ 59
def prefixEnd_2080044 : Nat := 4983230072969 + 3 ^ 40 * 2080044 * 2
def baseEnd_2080044 : Nat := 712041569667176701322705

theorem tailTrace_2080044 : CollatzResearch.WordTrace tailWord_2080044 prefixEnd_2080044 712041569667176701322705 := by
  unfold tailWord_2080044
  simp only [CollatzResearch.WordTrace]
  refine ⟨37932718638181653038975593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50576958184242204051967457 37932718638181653038975593)
  ·
    refine ⟨28449538978636239779231695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37932718638181653038975593 28449538978636239779231695)
    ·
      refine ⟨42674308467954359668847543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28449538978636239779231695 42674308467954359668847543)
      ·
        refine ⟨64011462701931539503271315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42674308467954359668847543 64011462701931539503271315)
        ·
          refine ⟨96017194052897309254906973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64011462701931539503271315 96017194052897309254906973)
          ·
            refine ⟨36006447769836490970590115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96017194052897309254906973 36006447769836490970590115)
            ·
              refine ⟨54009671654754736455885173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36006447769836490970590115 54009671654754736455885173)
              ·
                refine ⟨5063406717633256542739235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 54009671654754736455885173 5063406717633256542739235)
                ·
                  refine ⟨7595110076449884814108853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5063406717633256542739235 7595110076449884814108853)
                  ·
                    refine ⟨712041569667176701322705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7595110076449884814108853 712041569667176701322705)
                    ·
                      rfl

theorem cell22_2080044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 5].length) (baseStart_2080044 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2080044 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2080044 prefixEnd_2080044 := by exact prefixLift 2080044
  have htrace : WordTrace (prefixWord ++ tailWord_2080044) baseStart_2080044 baseEnd_2080044 := by
    simpa [prefixWord, tailWord_2080044, baseEnd_2080044] using wordTrace_append hprefix tailTrace_2080044
  have hstable : (prefixWord ++ tailWord_2080044).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2080044).length < 2 ^ (prefixWord ++ tailWord_2080044).sum := by decide
  have hdescent : baseEnd_2080044 < baseStart_2080044 := by decide
  rcases family_descends (prefixWord ++ tailWord_2080044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2080065 : List Nat := [1, 2, 5, 2, 1, 2, 3, 1, 1, 4]
def baseStart_2080065 : Nat := 118140960795 + 2080065 * 2 ^ 59
def prefixEnd_2080065 : Nat := 4983230072969 + 3 ^ 40 * 2080065 * 2
def baseEnd_2080065 : Nat := 712048758396339646547641

theorem tailTrace_2080065 : CollatzResearch.WordTrace tailWord_2080065 prefixEnd_2080065 712048758396339646547641 := by
  unfold tailWord_2080065
  simp only [CollatzResearch.WordTrace]
  refine ⟨75866203209287226664465649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50577468806191484442977099 75866203209287226664465649)
  ·
    refine ⟨56899652406965419998349237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75866203209287226664465649 56899652406965419998349237)
    ·
      refine ⟨5334342413153008124845241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 56899652406965419998349237 5334342413153008124845241)
      ·
        refine ⟨4000756809864756093633931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5334342413153008124845241 4000756809864756093633931)
        ·
          refine ⟨6001135214797134140450897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4000756809864756093633931 6001135214797134140450897)
          ·
            refine ⟨4500851411097850605338173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6001135214797134140450897 4500851411097850605338173)
            ·
              refine ⟨1687819279161693977001815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4500851411097850605338173 1687819279161693977001815)
              ·
                refine ⟨2531728918742540965502723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1687819279161693977001815 2531728918742540965502723)
                ·
                  refine ⟨3797593378113811448254085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2531728918742540965502723 3797593378113811448254085)
                  ·
                    refine ⟨712048758396339646547641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3797593378113811448254085 712048758396339646547641)
                    ·
                      rfl

theorem cell22_2080065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 3, 1, 1, 4].length) (baseStart_2080065 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2080065 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2080065 prefixEnd_2080065 := by exact prefixLift 2080065
  have htrace : WordTrace (prefixWord ++ tailWord_2080065) baseStart_2080065 baseEnd_2080065 := by
    simpa [prefixWord, tailWord_2080065, baseEnd_2080065] using wordTrace_append hprefix tailTrace_2080065
  have hstable : (prefixWord ++ tailWord_2080065).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2080065).length < 2 ^ (prefixWord ++ tailWord_2080065).sum := by decide
  have hdescent : baseEnd_2080065 < baseStart_2080065 := by decide
  rcases family_descends (prefixWord ++ tailWord_2080065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2080076 : List Nat := [2, 2, 1, 3, 2, 2, 2, 2, 2, 4]
def baseStart_2080076 : Nat := 118140960795 + 2080076 * 2 ^ 59
def prefixEnd_2080076 : Nat := 4983230072969 + 3 ^ 40 * 2080076 * 2
def baseEnd_2080076 : Nat := 712052523921139284522607

theorem tailTrace_2080076 : CollatzResearch.WordTrace tailWord_2080076 prefixEnd_2080076 712052523921139284522607 := by
  unfold tailWord_2080076
  simp only [CollatzResearch.WordTrace]
  refine ⟨37933302206123687771558041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50577736274831583695410721 37933302206123687771558041)
  ·
    refine ⟨28449976654592765828668531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37933302206123687771558041 28449976654592765828668531)
    ·
      refine ⟨42674964981889148743002797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28449976654592765828668531 42674964981889148743002797)
      ·
        refine ⟨16003111868208430778626049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42674964981889148743002797 16003111868208430778626049)
        ·
          refine ⟨12002333901156323083969537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16003111868208430778626049 12002333901156323083969537)
          ·
            refine ⟨9001750425867242312977153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12002333901156323083969537 9001750425867242312977153)
            ·
              refine ⟨6751312819400431734732865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9001750425867242312977153 6751312819400431734732865)
              ·
                refine ⟨5063484614550323801049649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6751312819400431734732865 5063484614550323801049649)
                ·
                  refine ⟨3797613460912742850787237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5063484614550323801049649 3797613460912742850787237)
                  ·
                    refine ⟨712052523921139284522607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3797613460912742850787237 712052523921139284522607)
                    ·
                      rfl

theorem cell22_2080076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 2, 2, 2, 4].length) (baseStart_2080076 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2080076 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2080076 prefixEnd_2080076 := by exact prefixLift 2080076
  have htrace : WordTrace (prefixWord ++ tailWord_2080076) baseStart_2080076 baseEnd_2080076 := by
    simpa [prefixWord, tailWord_2080076, baseEnd_2080076] using wordTrace_append hprefix tailTrace_2080076
  have hstable : (prefixWord ++ tailWord_2080076).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2080076).length < 2 ^ (prefixWord ++ tailWord_2080076).sum := by decide
  have hdescent : baseEnd_2080076 < baseStart_2080076 := by decide
  rcases family_descends (prefixWord ++ tailWord_2080076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2080078 : List Nat := [4, 1, 1, 1, 1, 1, 6, 2, 2, 3]
def baseStart_2080078 : Nat := 118140960795 + 2080078 * 2 ^ 59
def prefixEnd_2080078 : Nat := 4983230072969 + 3 ^ 40 * 2080078 * 2
def baseEnd_2080078 : Nat := 712053208562011945972601

theorem tailTrace_2080078 : CollatzResearch.WordTrace tailWord_2080078 prefixEnd_2080078 712053208562011945972601 := by
  unfold tailWord_2080078
  simp only [CollatzResearch.WordTrace]
  refine ⟨9483334669780016235586111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50577784905493419923125925 9483334669780016235586111)
  ·
    refine ⟨14225002004670024353379167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9483334669780016235586111 14225002004670024353379167)
    ·
      refine ⟨21337503007005036530068751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14225002004670024353379167 21337503007005036530068751)
      ·
        refine ⟨32006254510507554795103127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21337503007005036530068751 32006254510507554795103127)
        ·
          refine ⟨48009381765761332192654691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32006254510507554795103127 48009381765761332192654691)
          ·
            refine ⟨72014072648641998288982037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48009381765761332192654691 72014072648641998288982037)
            ·
              refine ⟨3375659655405093669796033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 72014072648641998288982037 3375659655405093669796033)
              ·
                refine ⟨2531744741553820252347025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3375659655405093669796033 2531744741553820252347025)
                ·
                  refine ⟨1898808556165365189260269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2531744741553820252347025 1898808556165365189260269)
                  ·
                    refine ⟨712053208562011945972601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1898808556165365189260269 712053208562011945972601)
                    ·
                      rfl

theorem cell22_2080078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 6, 2, 2, 3].length) (baseStart_2080078 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2080078 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2080078 prefixEnd_2080078 := by exact prefixLift 2080078
  have htrace : WordTrace (prefixWord ++ tailWord_2080078) baseStart_2080078 baseEnd_2080078 := by
    simpa [prefixWord, tailWord_2080078, baseEnd_2080078] using wordTrace_append hprefix tailTrace_2080078
  have hstable : (prefixWord ++ tailWord_2080078).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2080078).length < 2 ^ (prefixWord ++ tailWord_2080078).sum := by decide
  have hdescent : baseEnd_2080078 < baseStart_2080078 := by decide
  rcases family_descends (prefixWord ++ tailWord_2080078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2080119 : List Nat := [1, 1, 3, 1, 1, 2, 4, 2, 7]
def baseStart_2080119 : Nat := 118140960795 + 2080119 * 2 ^ 59
def prefixEnd_2080119 : Nat := 4983230072969 + 3 ^ 40 * 2080119 * 2
def baseEnd_2080119 : Nat := 237355747899967168565825

theorem tailTrace_2080119 : CollatzResearch.WordTrace tailWord_2080119 prefixEnd_2080119 237355747899967168565825 := by
  unfold tailWord_2080119
  simp only [CollatzResearch.WordTrace]
  refine ⟨75868172751091593886931411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50578781834061062591287607 75868172751091593886931411)
  ·
    refine ⟨113802259126637390830397117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75868172751091593886931411 113802259126637390830397117)
    ·
      refine ⟨42675847172489021561398919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113802259126637390830397117 42675847172489021561398919)
      ·
        refine ⟨64013770758733532342098379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42675847172489021561398919 64013770758733532342098379)
        ·
          refine ⟨96020656138100298513147569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64013770758733532342098379 96020656138100298513147569)
          ·
            refine ⟨72015492103575223884860677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96020656138100298513147569 72015492103575223884860677)
            ·
              refine ⟨13502904769420354478411377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 72015492103575223884860677 13502904769420354478411377)
              ·
                refine ⟨10127178577065265858808533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13502904769420354478411377 10127178577065265858808533)
                ·
                  refine ⟨237355747899967168565825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10127178577065265858808533 237355747899967168565825)
                  ·
                    rfl

theorem cell22_2080119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 2, 7].length) (baseStart_2080119 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2080119 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2080119 prefixEnd_2080119 := by exact prefixLift 2080119
  have htrace : WordTrace (prefixWord ++ tailWord_2080119) baseStart_2080119 baseEnd_2080119 := by
    simpa [prefixWord, tailWord_2080119, baseEnd_2080119] using wordTrace_append hprefix tailTrace_2080119
  have hstable : (prefixWord ++ tailWord_2080119).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2080119).length < 2 ^ (prefixWord ++ tailWord_2080119).sum := by decide
  have hdescent : baseEnd_2080119 < baseStart_2080119 := by decide
  rcases family_descends (prefixWord ++ tailWord_2080119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2080136 : List Nat := [2, 1, 3, 3, 1, 3, 1, 1, 7]
def baseStart_2080136 : Nat := 118140960795 + 2080136 * 2 ^ 59
def prefixEnd_2080136 : Nat := 4983230072969 + 3 ^ 40 * 2080136 * 2
def baseEnd_2080136 : Nat := 237357687715773042674141

theorem tailTrace_2080136 : CollatzResearch.WordTrace tailWord_2080136 prefixEnd_2080136 237357687715773042674141 := by
  unfold tailWord_2080136
  simp only [CollatzResearch.WordTrace]
  refine ⟨37934396396015002895150131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50579195194686670526866841 37934396396015002895150131)
  ·
    refine ⟨56901594594022504342725197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37934396396015002895150131 56901594594022504342725197)
    ·
      refine ⟨21338097972758439128521949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56901594594022504342725197 21338097972758439128521949)
      ·
        refine ⟨8001786739784414673195731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21338097972758439128521949 8001786739784414673195731)
        ·
          refine ⟨12002680109676622009793597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8001786739784414673195731 12002680109676622009793597)
          ·
            refine ⟨4501005041128733253672599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12002680109676622009793597 4501005041128733253672599)
            ·
              refine ⟨6751507561693099880508899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4501005041128733253672599 6751507561693099880508899)
              ·
                refine ⟨10127261342539649820763349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6751507561693099880508899 10127261342539649820763349)
                ·
                  refine ⟨237357687715773042674141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10127261342539649820763349 237357687715773042674141)
                  ·
                    rfl

theorem cell22_2080136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 1, 1, 7].length) (baseStart_2080136 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2080136 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2080136 prefixEnd_2080136 := by exact prefixLift 2080136
  have htrace : WordTrace (prefixWord ++ tailWord_2080136) baseStart_2080136 baseEnd_2080136 := by
    simpa [prefixWord, tailWord_2080136, baseEnd_2080136] using wordTrace_append hprefix tailTrace_2080136
  have hstable : (prefixWord ++ tailWord_2080136).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2080136).length < 2 ^ (prefixWord ++ tailWord_2080136).sum := by decide
  have hdescent : baseEnd_2080136 < baseStart_2080136 := by decide
  rcases family_descends (prefixWord ++ tailWord_2080136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2080153 : List Nat := [1, 2, 1, 2, 1, 6, 3, 1, 5]
def baseStart_2080153 : Nat := 118140960795 + 2080153 * 2 ^ 59
def prefixEnd_2080153 : Nat := 4983230072969 + 3 ^ 40 * 2080153 * 2
def baseEnd_2080153 : Nat := 237359627531578916782457

theorem tailTrace_2080153 : CollatzResearch.WordTrace tailWord_2080153 prefixEnd_2080153 237359627531578916782457 := by
  unfold tailWord_2080153
  simp only [CollatzResearch.WordTrace]
  refine ⟨75869412832968417693669113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50579608555312278462446075 75869412832968417693669113)
  ·
    refine ⟨56902059624726313270251835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75869412832968417693669113 56902059624726313270251835)
    ·
      refine ⟨85353089437089469905377753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56902059624726313270251835 85353089437089469905377753)
      ·
        refine ⟨64014817077817102429033315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85353089437089469905377753 64014817077817102429033315)
        ·
          refine ⟨96022225616725653643549973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64014817077817102429033315 96022225616725653643549973)
          ·
            refine ⟨4501041825784015014541405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 96022225616725653643549973 4501041825784015014541405)
            ·
              refine ⟨1687890684669005630453027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4501041825784015014541405 1687890684669005630453027)
              ·
                refine ⟨2531836027003508445679541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1687890684669005630453027 2531836027003508445679541)
                ·
                  refine ⟨237359627531578916782457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2531836027003508445679541 237359627531578916782457)
                  ·
                    rfl

theorem cell22_2080153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 3, 1, 5].length) (baseStart_2080153 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2080153 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2080153 prefixEnd_2080153 := by exact prefixLift 2080153
  have htrace : WordTrace (prefixWord ++ tailWord_2080153) baseStart_2080153 baseEnd_2080153 := by
    simpa [prefixWord, tailWord_2080153, baseEnd_2080153] using wordTrace_append hprefix tailTrace_2080153
  have hstable : (prefixWord ++ tailWord_2080153).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2080153).length < 2 ^ (prefixWord ++ tailWord_2080153).sum := by decide
  have hdescent : baseEnd_2080153 < baseStart_2080153 := by decide
  rcases family_descends (prefixWord ++ tailWord_2080153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2080245 : List Nat := [1, 3, 5, 1, 1, 1, 2, 2, 2, 4]
def baseStart_2080245 : Nat := 118140960795 + 2080245 * 2 ^ 59
def prefixEnd_2080245 : Nat := 4983230072969 + 3 ^ 40 * 2080245 * 2
def baseEnd_2080245 : Nat := 712110376074879177047089

theorem tailTrace_2080245 : CollatzResearch.WordTrace tailWord_2080245 prefixEnd_2080245 712110376074879177047089 := by
  unfold tailWord_2080245
  simp only [CollatzResearch.WordTrace]
  refine ⟨75872768348635117406018189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50581845565756744937345459 75872768348635117406018189)
  ·
    refine ⟨28452288130738169027256821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75872768348635117406018189 28452288130738169027256821)
    ·
      refine ⟨2667402012256703346305327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 28452288130738169027256821 2667402012256703346305327)
      ·
        refine ⟨4001103018385055019457991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2667402012256703346305327 4001103018385055019457991)
        ·
          refine ⟨6001654527577582529186987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4001103018385055019457991 6001654527577582529186987)
          ·
            refine ⟨9002481791366373793780481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6001654527577582529186987 9002481791366373793780481)
            ·
              refine ⟨6751861343524780345335361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9002481791366373793780481 6751861343524780345335361)
              ·
                refine ⟨5063896007643585259001521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6751861343524780345335361 5063896007643585259001521)
                ·
                  refine ⟨3797922005732688944251141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5063896007643585259001521 3797922005732688944251141)
                  ·
                    refine ⟨712110376074879177047089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3797922005732688944251141 712110376074879177047089)
                    ·
                      rfl

theorem cell22_2080245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_2080245 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2080245 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2080245 prefixEnd_2080245 := by exact prefixLift 2080245
  have htrace : WordTrace (prefixWord ++ tailWord_2080245) baseStart_2080245 baseEnd_2080245 := by
    simpa [prefixWord, tailWord_2080245, baseEnd_2080245] using wordTrace_append hprefix tailTrace_2080245
  have hstable : (prefixWord ++ tailWord_2080245).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2080245).length < 2 ^ (prefixWord ++ tailWord_2080245).sum := by decide
  have hdescent : baseEnd_2080245 < baseStart_2080245 := by decide
  rcases family_descends (prefixWord ++ tailWord_2080245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2080260 : List Nat := [2, 3, 2, 3, 2, 2, 1, 7]
def baseStart_2080260 : Nat := 118140960795 + 2080260 * 2 ^ 59
def prefixEnd_2080260 : Nat := 4983230072969 + 3 ^ 40 * 2080260 * 2
def baseEnd_2080260 : Nat := 79123945653491570880227

theorem tailTrace_2080260 : CollatzResearch.WordTrace tailWord_2080260 prefixEnd_2080260 79123945653491570880227 := by
  unfold tailWord_2080260
  simp only [CollatzResearch.WordTrace]
  refine ⟨37936657721790387483907117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50582210295720516645209489 37936657721790387483907117)
  ·
    refine ⟨14226246645671395306465169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37936657721790387483907117 14226246645671395306465169)
    ·
      refine ⟨10669684984253546479848877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14226246645671395306465169 10669684984253546479848877)
      ·
        refine ⟨4001131869095079929943329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10669684984253546479848877 4001131869095079929943329)
        ·
          refine ⟨3000848901821309947457497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4001131869095079929943329 3000848901821309947457497)
          ·
            refine ⟨2250636676365982460593123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3000848901821309947457497 2250636676365982460593123)
            ·
              refine ⟨3375955014548973690889685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2250636676365982460593123 3375955014548973690889685)
              ·
                refine ⟨79123945653491570880227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3375955014548973690889685 79123945653491570880227)
                ·
                  rfl

theorem cell22_2080260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 1, 7].length) (baseStart_2080260 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2080260 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2080260 prefixEnd_2080260 := by exact prefixLift 2080260
  have htrace : WordTrace (prefixWord ++ tailWord_2080260) baseStart_2080260 baseEnd_2080260 := by
    simpa [prefixWord, tailWord_2080260, baseEnd_2080260] using wordTrace_append hprefix tailTrace_2080260
  have hstable : (prefixWord ++ tailWord_2080260).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2080260).length < 2 ^ (prefixWord ++ tailWord_2080260).sum := by decide
  have hdescent : baseEnd_2080260 < baseStart_2080260 := by decide
  rcases family_descends (prefixWord ++ tailWord_2080260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2080361 : List Nat := [1, 2, 1, 1, 1, 4, 12]
def baseStart_2080361 : Nat := 118140960795 + 2080361 * 2 ^ 59
def prefixEnd_2080361 : Nat := 4983230072969 + 3 ^ 40 * 2080361 * 2
def baseEnd_2080361 : Nat := 26375929083166427449879

theorem tailTrace_2080361 : CollatzResearch.WordTrace tailWord_2080361 prefixEnd_2080361 26375929083166427449879 := by
  unfold tailWord_2080361
  simp only [CollatzResearch.WordTrace]
  refine ⟨75876999216214869217240937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50584666144143246144827291 75876999216214869217240937)
  ·
    refine ⟨56907749412161151912930703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75876999216214869217240937 56907749412161151912930703)
    ·
      refine ⟨85361624118241727869396055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56907749412161151912930703 85361624118241727869396055)
      ·
        refine ⟨128042436177362591804094083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85361624118241727869396055 128042436177362591804094083)
        ·
          refine ⟨192063654266043887706141125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128042436177362591804094083 192063654266043887706141125)
          ·
            refine ⟨36011935174883228944901461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 192063654266043887706141125 36011935174883228944901461)
            ·
              refine ⟨26375929083166427449879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 36011935174883228944901461 26375929083166427449879)
              ·
                rfl

theorem cell22_2080361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 12].length) (baseStart_2080361 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2080361 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2080361 prefixEnd_2080361 := by exact prefixLift 2080361
  have htrace : WordTrace (prefixWord ++ tailWord_2080361) baseStart_2080361 baseEnd_2080361 := by
    simpa [prefixWord, tailWord_2080361, baseEnd_2080361] using wordTrace_append hprefix tailTrace_2080361
  have hstable : (prefixWord ++ tailWord_2080361).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2080361).length < 2 ^ (prefixWord ++ tailWord_2080361).sum := by decide
  have hdescent : baseEnd_2080361 < baseStart_2080361 := by decide
  rcases family_descends (prefixWord ++ tailWord_2080361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2080418 : List Nat := [3, 3, 1, 4, 2, 1, 2, 2, 4]
def baseStart_2080418 : Nat := 118140960795 + 2080418 * 2 ^ 59
def prefixEnd_2080418 : Nat := 4983230072969 + 3 ^ 40 * 2080418 * 2
def baseEnd_2080418 : Nat := 237389865836788130823853

theorem tailTrace_2080418 : CollatzResearch.WordTrace tailWord_2080418 prefixEnd_2080418 237389865836788130823853 := by
  unfold tailWord_2080418
  simp only [CollatzResearch.WordTrace]
  refine ⟨18969769544252091988016477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50586052118005578634710605 18969769544252091988016477)
  ·
    refine ⟨7113663579094534495506179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18969769544252091988016477 7113663579094534495506179)
    ·
      refine ⟨10670495368641801743259269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7113663579094534495506179 10670495368641801743259269)
      ·
        refine ⟨2000717881620337826861113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10670495368641801743259269 2000717881620337826861113)
        ·
          refine ⟨1500538411215253370145835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2000717881620337826861113 1500538411215253370145835)
          ·
            refine ⟨2250807616822880055218753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1500538411215253370145835 2250807616822880055218753)
            ·
              refine ⟨1688105712617160041414065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2250807616822880055218753 1688105712617160041414065)
              ·
                refine ⟨1266079284462870031060549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1688105712617160041414065 1266079284462870031060549)
                ·
                  refine ⟨237389865836788130823853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1266079284462870031060549 237389865836788130823853)
                  ·
                    rfl

theorem cell22_2080418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 2, 2, 4].length) (baseStart_2080418 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2080418 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2080418 prefixEnd_2080418 := by exact prefixLift 2080418
  have htrace : WordTrace (prefixWord ++ tailWord_2080418) baseStart_2080418 baseEnd_2080418 := by
    simpa [prefixWord, tailWord_2080418, baseEnd_2080418] using wordTrace_append hprefix tailTrace_2080418
  have hstable : (prefixWord ++ tailWord_2080418).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2080418).length < 2 ^ (prefixWord ++ tailWord_2080418).sum := by decide
  have hdescent : baseEnd_2080418 < baseStart_2080418 := by decide
  rcases family_descends (prefixWord ++ tailWord_2080418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2080461 : List Nat := [1, 6, 2, 1, 1, 1, 1, 5, 1, 3]
def baseStart_2080461 : Nat := 118140960795 + 2080461 * 2 ^ 59
def prefixEnd_2080461 : Nat := 4983230072969 + 3 ^ 40 * 2080461 * 2
def baseEnd_2080461 : Nat := 712184317289126613646427

theorem tailTrace_2080461 : CollatzResearch.WordTrace tailWord_2080461 prefixEnd_2080461 712184317289126613646427 := by
  unfold tailWord_2080461
  simp only [CollatzResearch.WordTrace]
  refine ⟨75880646515852586295881237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50587097677235057530587491 75880646515852586295881237)
  ·
    refine ⟨3556905305430589982619433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 75880646515852586295881237 3556905305430589982619433)
    ·
      refine ⟨2667678979072942486964575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3556905305430589982619433 2667678979072942486964575)
      ·
        refine ⟨4001518468609413730446863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2667678979072942486964575 4001518468609413730446863)
        ·
          refine ⟨6002277702914120595670295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4001518468609413730446863 6002277702914120595670295)
          ·
            refine ⟨9003416554371180893505443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6002277702914120595670295 9003416554371180893505443)
            ·
              refine ⟨13505124831556771340258165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9003416554371180893505443 13505124831556771340258165)
              ·
                refine ⟨1266105452958447313149203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13505124831556771340258165 1266105452958447313149203)
                ·
                  refine ⟨1899158179437670969723805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1266105452958447313149203 1899158179437670969723805)
                  ·
                    refine ⟨712184317289126613646427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1899158179437670969723805 712184317289126613646427)
                    ·
                      rfl

theorem cell22_2080461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 5, 1, 3].length) (baseStart_2080461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2080461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2080461 prefixEnd_2080461 := by exact prefixLift 2080461
  have htrace : WordTrace (prefixWord ++ tailWord_2080461) baseStart_2080461 baseEnd_2080461 := by
    simpa [prefixWord, tailWord_2080461, baseEnd_2080461] using wordTrace_append hprefix tailTrace_2080461
  have hstable : (prefixWord ++ tailWord_2080461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2080461).length < 2 ^ (prefixWord ++ tailWord_2080461).sum := by decide
  have hdescent : baseEnd_2080461 < baseStart_2080461 := by decide
  rcases family_descends (prefixWord ++ tailWord_2080461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2080485 : List Nat := [1, 3, 1, 4, 1, 1, 4, 1, 6]
def baseStart_2080485 : Nat := 118140960795 + 2080485 * 2 ^ 59
def prefixEnd_2080485 : Nat := 4983230072969 + 3 ^ 40 * 2080485 * 2
def baseEnd_2080485 : Nat := 237397510993199517015451

theorem tailTrace_2080485 : CollatzResearch.WordTrace tailWord_2080485 prefixEnd_2080485 237397510993199517015451 := by
  unfold tailWord_2080485
  simp only [CollatzResearch.WordTrace]
  refine ⟨75881521867765638394754909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50587681245177092263169939 75881521867765638394754909)
  ·
    refine ⟨28455570700412114398033091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75881521867765638394754909 28455570700412114398033091)
    ·
      refine ⟨42683356050618171597049637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28455570700412114398033091 42683356050618171597049637)
      ·
        refine ⟨8003129259490907174446807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42683356050618171597049637 8003129259490907174446807)
        ·
          refine ⟨12004693889236360761670211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8003129259490907174446807 12004693889236360761670211)
          ·
            refine ⟨18007040833854541142505317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12004693889236360761670211 18007040833854541142505317)
            ·
              refine ⟨3376320156347726464219747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18007040833854541142505317 3376320156347726464219747)
              ·
                refine ⟨5064480234521589696329621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3376320156347726464219747 5064480234521589696329621)
                ·
                  refine ⟨237397510993199517015451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5064480234521589696329621 237397510993199517015451)
                  ·
                    rfl

theorem cell22_2080485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 4, 1, 6].length) (baseStart_2080485 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2080485 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2080485 prefixEnd_2080485 := by exact prefixLift 2080485
  have htrace : WordTrace (prefixWord ++ tailWord_2080485) baseStart_2080485 baseEnd_2080485 := by
    simpa [prefixWord, tailWord_2080485, baseEnd_2080485] using wordTrace_append hprefix tailTrace_2080485
  have hstable : (prefixWord ++ tailWord_2080485).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2080485).length < 2 ^ (prefixWord ++ tailWord_2080485).sum := by decide
  have hdescent : baseEnd_2080485 < baseStart_2080485 := by decide
  rcases family_descends (prefixWord ++ tailWord_2080485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2080596 : List Nat := [2, 4, 1, 1, 3, 2, 1, 4, 1, 3]
def baseStart_2080596 : Nat := 118140960795 + 2080596 * 2 ^ 59
def prefixEnd_2080596 : Nat := 4983230072969 + 3 ^ 40 * 2080596 * 2
def baseEnd_2080596 : Nat := 712230530548031261521013

theorem tailTrace_2080596 : CollatzResearch.WordTrace tailWord_2080596 prefixEnd_2080596 712230530548031261521013 := by
  unfold tailWord_2080596
  simp only [CollatzResearch.WordTrace]
  refine ⟨37942785185181752176022821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50590380246909002901363761 37942785185181752176022821)
  ·
    refine ⟨7114272222221578533004279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37942785185181752176022821 7114272222221578533004279)
    ·
      refine ⟨10671408333332367799506419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7114272222221578533004279 10671408333332367799506419)
      ·
        refine ⟨16007112499998551699259629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10671408333332367799506419 16007112499998551699259629)
        ·
          refine ⟨6002667187499456887222361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16007112499998551699259629 6002667187499456887222361)
          ·
            refine ⟨4502000390624592665416771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6002667187499456887222361 4502000390624592665416771)
            ·
              refine ⟨6753000585936888998125157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4502000390624592665416771 6753000585936888998125157)
              ·
                refine ⟨1266187609863166687148467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6753000585936888998125157 1266187609863166687148467)
                ·
                  refine ⟨1899281414794750030722701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1266187609863166687148467 1899281414794750030722701)
                  ·
                    refine ⟨712230530548031261521013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1899281414794750030722701 712230530548031261521013)
                    ·
                      rfl

theorem cell22_2080596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 1, 4, 1, 3].length) (baseStart_2080596 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2080596 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2080596 prefixEnd_2080596 := by exact prefixLift 2080596
  have htrace : WordTrace (prefixWord ++ tailWord_2080596) baseStart_2080596 baseEnd_2080596 := by
    simpa [prefixWord, tailWord_2080596, baseEnd_2080596] using wordTrace_append hprefix tailTrace_2080596
  have hstable : (prefixWord ++ tailWord_2080596).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2080596).length < 2 ^ (prefixWord ++ tailWord_2080596).sum := by decide
  have hdescent : baseEnd_2080596 < baseStart_2080596 := by decide
  rcases family_descends (prefixWord ++ tailWord_2080596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2080620 : List Nat := [2, 2, 1, 1, 4, 2, 1, 1, 8]
def baseStart_2080620 : Nat := 118140960795 + 2080620 * 2 ^ 59
def prefixEnd_2080620 : Nat := 4983230072969 + 3 ^ 40 * 2080620 * 2
def baseEnd_2080620 : Nat := 237412915412834399640313

theorem tailTrace_2080620 : CollatzResearch.WordTrace tailWord_2080620 prefixEnd_2080620 237412915412834399640313 := by
  unfold tailWord_2080620
  simp only [CollatzResearch.WordTrace]
  refine ⟨37943222861138278225459657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50590963814851037633946209 37943222861138278225459657)
  ·
    refine ⟨28457417145853708669094743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37943222861138278225459657 28457417145853708669094743)
    ·
      refine ⟨42686125718780563003642115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28457417145853708669094743 42686125718780563003642115)
      ·
        refine ⟨64029188578170844505463173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42686125718780563003642115 64029188578170844505463173)
        ·
          refine ⟨12005472858407033344774345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64029188578170844505463173 12005472858407033344774345)
          ·
            refine ⟨9004104643805275008580759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12005472858407033344774345 9004104643805275008580759)
            ·
              refine ⟨13506156965707912512871139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9004104643805275008580759 13506156965707912512871139)
              ·
                refine ⟨20259235448561868769306709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13506156965707912512871139 20259235448561868769306709)
                ·
                  refine ⟨237412915412834399640313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20259235448561868769306709 237412915412834399640313)
                  ·
                    rfl

theorem cell22_2080620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 8].length) (baseStart_2080620 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2080620 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2080620 prefixEnd_2080620 := by exact prefixLift 2080620
  have htrace : WordTrace (prefixWord ++ tailWord_2080620) baseStart_2080620 baseEnd_2080620 := by
    simpa [prefixWord, tailWord_2080620, baseEnd_2080620] using wordTrace_append hprefix tailTrace_2080620
  have hstable : (prefixWord ++ tailWord_2080620).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2080620).length < 2 ^ (prefixWord ++ tailWord_2080620).sum := by decide
  have hdescent : baseEnd_2080620 < baseStart_2080620 := by decide
  rcases family_descends (prefixWord ++ tailWord_2080620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2080669 : List Nat := [1, 4, 2, 1, 2, 4, 1, 1, 1, 5]
def baseStart_2080669 : Nat := 118140960795 + 2080669 * 2 ^ 59
def prefixEnd_2080669 : Nat := 4983230072969 + 3 ^ 40 * 2080669 * 2
def baseEnd_2080669 : Nat := 712255519939883404445789

theorem tailTrace_2080669 : CollatzResearch.WordTrace tailWord_2080669 prefixEnd_2080669 712255519939883404445789 := by
  unfold tailWord_2080669
  simp only [CollatzResearch.WordTrace]
  refine ⟨75888232899099037819453061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50592155266066025212968707 75888232899099037819453061)
  ·
    refine ⟨14229043668581069591147449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75888232899099037819453061 14229043668581069591147449)
    ·
      refine ⟨10671782751435802193360587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14229043668581069591147449 10671782751435802193360587)
      ·
        refine ⟨16007674127153703290040881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10671782751435802193360587 16007674127153703290040881)
        ·
          refine ⟨12005755595365277467530661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16007674127153703290040881 12005755595365277467530661)
          ·
            refine ⟨2251079174130989525161999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12005755595365277467530661 2251079174130989525161999)
            ·
              refine ⟨3376618761196484287742999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2251079174130989525161999 3376618761196484287742999)
              ·
                refine ⟨5064928141794726431614499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3376618761196484287742999 5064928141794726431614499)
                ·
                  refine ⟨7597392212692089647421749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5064928141794726431614499 7597392212692089647421749)
                  ·
                    refine ⟨712255519939883404445789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7597392212692089647421749 712255519939883404445789)
                    ·
                      rfl

theorem cell22_2080669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 1, 1, 1, 5].length) (baseStart_2080669 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2080669 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2080669 prefixEnd_2080669 := by exact prefixLift 2080669
  have htrace : WordTrace (prefixWord ++ tailWord_2080669) baseStart_2080669 baseEnd_2080669 := by
    simpa [prefixWord, tailWord_2080669, baseEnd_2080669] using wordTrace_append hprefix tailTrace_2080669
  have hstable : (prefixWord ++ tailWord_2080669).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2080669).length < 2 ^ (prefixWord ++ tailWord_2080669).sum := by decide
  have hdescent : baseEnd_2080669 < baseStart_2080669 := by decide
  rcases family_descends (prefixWord ++ tailWord_2080669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2080695 : List Nat := [1, 1, 3, 1, 3, 1, 1, 2, 1, 8]
def baseStart_2080695 : Nat := 118140960795 + 2080695 * 2 ^ 59
def prefixEnd_2080695 : Nat := 4983230072969 + 3 ^ 40 * 2080695 * 2
def baseEnd_2080695 : Nat := 712264420271228003295709

theorem tailTrace_2080695 : CollatzResearch.WordTrace tailWord_2080695 prefixEnd_2080695 712264420271228003295709 := by
  unfold tailWord_2080695
  simp only [CollatzResearch.WordTrace]
  refine ⟨75889181197004844259899539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50592787464669896173266359 75889181197004844259899539)
  ·
    refine ⟨113833771795507266389849309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75889181197004844259899539 113833771795507266389849309)
    ·
      refine ⟨42687664423315224896193491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113833771795507266389849309 42687664423315224896193491)
      ·
        refine ⟨64031496634972837344290237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42687664423315224896193491 64031496634972837344290237)
        ·
          refine ⟨24011811238114814004108839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64031496634972837344290237 24011811238114814004108839)
          ·
            refine ⟨36017716857172221006163259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24011811238114814004108839 36017716857172221006163259)
            ·
              refine ⟨54026575285758331509244889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36017716857172221006163259 54026575285758331509244889)
              ·
                refine ⟨40519931464318748631933667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54026575285758331509244889 40519931464318748631933667)
                ·
                  refine ⟨60779897196478122947900501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40519931464318748631933667 60779897196478122947900501)
                  ·
                    refine ⟨712264420271228003295709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 60779897196478122947900501 712264420271228003295709)
                    ·
                      rfl

theorem cell22_2080695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 2, 1, 8].length) (baseStart_2080695 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2080695 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2080695 prefixEnd_2080695 := by exact prefixLift 2080695
  have htrace : WordTrace (prefixWord ++ tailWord_2080695) baseStart_2080695 baseEnd_2080695 := by
    simpa [prefixWord, tailWord_2080695, baseEnd_2080695] using wordTrace_append hprefix tailTrace_2080695
  have hstable : (prefixWord ++ tailWord_2080695).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2080695).length < 2 ^ (prefixWord ++ tailWord_2080695).sum := by decide
  have hdescent : baseEnd_2080695 < baseStart_2080695 := by decide
  rcases family_descends (prefixWord ++ tailWord_2080695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2080714 : List Nat := [3, 1, 2, 1, 2, 1, 5, 1, 3, 3]
def baseStart_2080714 : Nat := 118140960795 + 2080714 * 2 ^ 59
def prefixEnd_2080714 : Nat := 4983230072969 + 3 ^ 40 * 2080714 * 2
def baseEnd_2080714 : Nat := 712270924359518287070651

theorem tailTrace_2080714 : CollatzResearch.WordTrace tailWord_2080714 prefixEnd_2080714 712270924359518287070651 := by
  unfold tailWord_2080714
  simp only [CollatzResearch.WordTrace]
  refine ⟨18972468545984002626210299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50593249455957340336560797 18972468545984002626210299)
  ·
    refine ⟨28458702818976003939315449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18972468545984002626210299 28458702818976003939315449)
    ·
      refine ⟨21344027114232002954486587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28458702818976003939315449 21344027114232002954486587)
      ·
        refine ⟨32016040671348004431729881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21344027114232002954486587 32016040671348004431729881)
        ·
          refine ⟨24012030503511003323797411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32016040671348004431729881 24012030503511003323797411)
          ·
            refine ⟨36018045755266504985696117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24012030503511003323797411 36018045755266504985696117)
            ·
              refine ⟨3376691789556234842409011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 36018045755266504985696117 3376691789556234842409011)
              ·
                refine ⟨5065037684334352263613517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3376691789556234842409011 5065037684334352263613517)
                ·
                  refine ⟨1899389131625382098855069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5065037684334352263613517 1899389131625382098855069)
                  ·
                    refine ⟨712270924359518287070651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1899389131625382098855069 712270924359518287070651)
                    ·
                      rfl

theorem cell22_2080714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 5, 1, 3, 3].length) (baseStart_2080714 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2080714 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2080714 prefixEnd_2080714 := by exact prefixLift 2080714
  have htrace : WordTrace (prefixWord ++ tailWord_2080714) baseStart_2080714 baseEnd_2080714 := by
    simpa [prefixWord, tailWord_2080714, baseEnd_2080714] using wordTrace_append hprefix tailTrace_2080714
  have hstable : (prefixWord ++ tailWord_2080714).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2080714).length < 2 ^ (prefixWord ++ tailWord_2080714).sum := by decide
  have hdescent : baseEnd_2080714 < baseStart_2080714 := by decide
  rcases family_descends (prefixWord ++ tailWord_2080714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2080727 : List Nat := [1, 1, 3, 2, 1, 1, 5, 3, 5]
def baseStart_2080727 : Nat := 118140960795 + 2080727 * 2 ^ 59
def prefixEnd_2080727 : Nat := 4983230072969 + 3 ^ 40 * 2080727 * 2
def baseEnd_2080727 : Nat := 237425124841730195498537

theorem tailTrace_2080727 : CollatzResearch.WordTrace tailWord_2080727 prefixEnd_2080727 237425124841730195498537 := by
  unfold tailWord_2080727
  simp only [CollatzResearch.WordTrace]
  refine ⟨75890348332888913725064435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50593565555259275816709623 75890348332888913725064435)
  ·
    refine ⟨113835522499333370587596653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75890348332888913725064435 113835522499333370587596653)
    ·
      refine ⟨42688320937250013970348745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113835522499333370587596653 42688320937250013970348745)
      ·
        refine ⟨32016240702937510477761559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42688320937250013970348745 32016240702937510477761559)
        ·
          refine ⟨48024361054406265716642339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32016240702937510477761559 48024361054406265716642339)
          ·
            refine ⟨72036541581609398574963509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48024361054406265716642339 72036541581609398574963509)
            ·
              refine ⟨6753425773275881116402829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 72036541581609398574963509 6753425773275881116402829)
              ·
                refine ⟨2532534664978455418651061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6753425773275881116402829 2532534664978455418651061)
                ·
                  refine ⟨237425124841730195498537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2532534664978455418651061 237425124841730195498537)
                  ·
                    rfl

theorem cell22_2080727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5, 3, 5].length) (baseStart_2080727 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2080727 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2080727 prefixEnd_2080727 := by exact prefixLift 2080727
  have htrace : WordTrace (prefixWord ++ tailWord_2080727) baseStart_2080727 baseEnd_2080727 := by
    simpa [prefixWord, tailWord_2080727, baseEnd_2080727] using wordTrace_append hprefix tailTrace_2080727
  have hstable : (prefixWord ++ tailWord_2080727).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2080727).length < 2 ^ (prefixWord ++ tailWord_2080727).sum := by decide
  have hdescent : baseEnd_2080727 < baseStart_2080727 := by decide
  rcases family_descends (prefixWord ++ tailWord_2080727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2080787 : List Nat := [1, 1, 1, 2, 1, 4, 3, 3, 1, 5]
def baseStart_2080787 : Nat := 118140960795 + 2080787 * 2 ^ 59
def prefixEnd_2080787 : Nat := 4983230072969 + 3 ^ 40 * 2080787 * 2
def baseEnd_2080787 : Nat := 712295913751370429995427

theorem tailTrace_2080787 : CollatzResearch.WordTrace tailWord_2080787 prefixEnd_2080787 712295913751370429995427 := by
  unfold tailWord_2080787
  simp only [CollatzResearch.WordTrace]
  refine ⟨75892536712671543972248615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50595024475114362648165743 75892536712671543972248615)
  ·
    refine ⟨113838805069007315958372923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75892536712671543972248615 113838805069007315958372923)
    ·
      refine ⟨170758207603510973937559385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113838805069007315958372923 170758207603510973937559385)
      ·
        refine ⟨128068655702633230453169539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170758207603510973937559385 128068655702633230453169539)
        ·
          refine ⟨192102983553949845679754309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128068655702633230453169539 192102983553949845679754309)
          ·
            refine ⟨36019309416365596064953933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 192102983553949845679754309 36019309416365596064953933)
            ·
              refine ⟨13507241031137098524357725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36019309416365596064953933 13507241031137098524357725)
              ·
                refine ⟨5065215386676411946634147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13507241031137098524357725 5065215386676411946634147)
                ·
                  refine ⟨7597823080014617919951221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5065215386676411946634147 7597823080014617919951221)
                  ·
                    refine ⟨712295913751370429995427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7597823080014617919951221 712295913751370429995427)
                    ·
                      rfl

theorem cell22_2080787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 3, 1, 5].length) (baseStart_2080787 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2080787 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2080787 prefixEnd_2080787 := by exact prefixLift 2080787
  have htrace : WordTrace (prefixWord ++ tailWord_2080787) baseStart_2080787 baseEnd_2080787 := by
    simpa [prefixWord, tailWord_2080787, baseEnd_2080787] using wordTrace_append hprefix tailTrace_2080787
  have hstable : (prefixWord ++ tailWord_2080787).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2080787).length < 2 ^ (prefixWord ++ tailWord_2080787).sum := by decide
  have hdescent : baseEnd_2080787 < baseStart_2080787 := by decide
  rcases family_descends (prefixWord ++ tailWord_2080787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2080789 : List Nat := [1, 3, 2, 1, 5, 1, 1, 2, 6]
def baseStart_2080789 : Nat := 118140960795 + 2080789 * 2 ^ 59
def prefixEnd_2080789 : Nat := 4983230072969 + 3 ^ 40 * 2080789 * 2
def baseEnd_2080789 : Nat := 237432199464081030481807

theorem tailTrace_2080789 : CollatzResearch.WordTrace tailWord_2080789 prefixEnd_2080789 237432199464081030481807 := by
  unfold tailWord_2080789
  simp only [CollatzResearch.WordTrace]
  refine ⟨75892609658664298313821421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50595073105776198875880947 75892609658664298313821421)
  ·
    refine ⟨28459728621999111867683033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75892609658664298313821421 28459728621999111867683033)
    ·
      refine ⟨21344796466499333900762275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28459728621999111867683033 21344796466499333900762275)
      ·
        refine ⟨32017194699749000851143413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21344796466499333900762275 32017194699749000851143413)
        ·
          refine ⟨3001612003101468829794695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 32017194699749000851143413 3001612003101468829794695)
          ·
            refine ⟨4502418004652203244692043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3001612003101468829794695 4502418004652203244692043)
            ·
              refine ⟨6753627006978304867038065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4502418004652203244692043 6753627006978304867038065)
              ·
                refine ⟨5065220255233728650278549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6753627006978304867038065 5065220255233728650278549)
                ·
                  refine ⟨237432199464081030481807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5065220255233728650278549 237432199464081030481807)
                  ·
                    rfl

theorem cell22_2080789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 2, 6].length) (baseStart_2080789 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2080789 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2080789 prefixEnd_2080789 := by exact prefixLift 2080789
  have htrace : WordTrace (prefixWord ++ tailWord_2080789) baseStart_2080789 baseEnd_2080789 := by
    simpa [prefixWord, tailWord_2080789, baseEnd_2080789] using wordTrace_append hprefix tailTrace_2080789
  have hstable : (prefixWord ++ tailWord_2080789).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2080789).length < 2 ^ (prefixWord ++ tailWord_2080789).sum := by decide
  have hdescent : baseEnd_2080789 < baseStart_2080789 := by decide
  rcases family_descends (prefixWord ++ tailWord_2080789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2080808 : List Nat := [2, 1, 5, 3, 1, 1, 1, 3, 1, 4]
def baseStart_2080808 : Nat := 118140960795 + 2080808 * 2 ^ 59
def prefixEnd_2080808 : Nat := 4983230072969 + 3 ^ 40 * 2080808 * 2
def baseEnd_2080808 : Nat := 712303102480533375220363

theorem tailTrace_2080808 : CollatzResearch.WordTrace tailWord_2080808 prefixEnd_2080808 712303102480533375220363 := by
  unfold tailWord_2080808
  simp only [CollatzResearch.WordTrace]
  refine ⟨37946651322797732279381539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50595535097063643039175385 37946651322797732279381539)
  ·
    refine ⟨56919976984196598419072309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37946651322797732279381539 56919976984196598419072309)
    ·
      refine ⟨5336247842268431101788029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 56919976984196598419072309 5336247842268431101788029)
      ·
        refine ⟨2001092940850661663170511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5336247842268431101788029 2001092940850661663170511)
        ·
          refine ⟨3001639411275992494755767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2001092940850661663170511 3001639411275992494755767)
          ·
            refine ⟨4502459116913988742133651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3001639411275992494755767 4502459116913988742133651)
            ·
              refine ⟨6753688675370983113200477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4502459116913988742133651 6753688675370983113200477)
              ·
                refine ⟨2532633253264118667450179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6753688675370983113200477 2532633253264118667450179)
                ·
                  refine ⟨3798949879896178001175269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2532633253264118667450179 3798949879896178001175269)
                  ·
                    refine ⟨712303102480533375220363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3798949879896178001175269 712303102480533375220363)
                    ·
                      rfl

theorem cell22_2080808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 1, 3, 1, 4].length) (baseStart_2080808 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2080808 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2080808 prefixEnd_2080808 := by exact prefixLift 2080808
  have htrace : WordTrace (prefixWord ++ tailWord_2080808) baseStart_2080808 baseEnd_2080808 := by
    simpa [prefixWord, tailWord_2080808, baseEnd_2080808] using wordTrace_append hprefix tailTrace_2080808
  have hstable : (prefixWord ++ tailWord_2080808).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2080808).length < 2 ^ (prefixWord ++ tailWord_2080808).sum := by decide
  have hdescent : baseEnd_2080808 < baseStart_2080808 := by decide
  rcases family_descends (prefixWord ++ tailWord_2080808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2080817 : List Nat := [1, 2, 2, 3, 1, 4, 9]
def baseStart_2080817 : Nat := 118140960795 + 2080817 * 2 ^ 59
def prefixEnd_2080817 : Nat := 4983230072969 + 3 ^ 40 * 2080817 * 2
def baseEnd_2080817 : Nat := 26381710494980013027605

theorem tailTrace_2080817 : CollatzResearch.WordTrace tailWord_2080817 prefixEnd_2080817 26381710494980013027605 := by
  unfold tailWord_2080817
  simp only [CollatzResearch.WordTrace]
  refine ⟨75893630902562859095840705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50595753935041906063893803 75893630902562859095840705)
  ·
    refine ⟨56920223176922144321880529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75893630902562859095840705 56920223176922144321880529)
    ·
      refine ⟨42690167382691608241410397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56920223176922144321880529 42690167382691608241410397)
      ·
        refine ⟨16008812768509353090528899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42690167382691608241410397 16008812768509353090528899)
        ·
          refine ⟨24013219152764029635793349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16008812768509353090528899 24013219152764029635793349)
          ·
            refine ⟨4502478591143255556711253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24013219152764029635793349 4502478591143255556711253)
            ·
              refine ⟨26381710494980013027605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4502478591143255556711253 26381710494980013027605)
              ·
                rfl

theorem cell22_2080817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 9].length) (baseStart_2080817 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2080817 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2080817 prefixEnd_2080817 := by exact prefixLift 2080817
  have htrace : WordTrace (prefixWord ++ tailWord_2080817) baseStart_2080817 baseEnd_2080817 := by
    simpa [prefixWord, tailWord_2080817, baseEnd_2080817] using wordTrace_append hprefix tailTrace_2080817
  have hstable : (prefixWord ++ tailWord_2080817).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2080817).length < 2 ^ (prefixWord ++ tailWord_2080817).sum := by decide
  have hdescent : baseEnd_2080817 < baseStart_2080817 := by decide
  rcases family_descends (prefixWord ++ tailWord_2080817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2080821 : List Nat := [1, 3, 3, 1, 1, 1, 5, 2, 2, 3]
def baseStart_2080821 : Nat := 118140960795 + 2080821 * 2 ^ 59
def prefixEnd_2080821 : Nat := 4983230072969 + 3 ^ 40 * 2080821 * 2
def baseEnd_2080821 : Nat := 712307552646205674645323

theorem tailTrace_2080821 : CollatzResearch.WordTrace tailWord_2080821 prefixEnd_2080821 712307552646205674645323 := by
  unfold tailWord_2080821
  simp only [CollatzResearch.WordTrace]
  refine ⟨75893776794548367778986317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50595851196365578519324211 75893776794548367778986317)
  ·
    refine ⟨28460166297955637917119869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75893776794548367778986317 28460166297955637917119869)
    ·
      refine ⟨10672562361733364218919951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28460166297955637917119869 10672562361733364218919951)
      ·
        refine ⟨16008843542600046328379927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10672562361733364218919951 16008843542600046328379927)
        ·
          refine ⟨24013265313900069492569891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16008843542600046328379927 24013265313900069492569891)
          ·
            refine ⟨36019897970850104238854837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24013265313900069492569891 36019897970850104238854837)
            ·
              refine ⟨3376865434767197272392641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 36019897970850104238854837 3376865434767197272392641)
              ·
                refine ⟨2532649076075397954294481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3376865434767197272392641 2532649076075397954294481)
                ·
                  refine ⟨1899486807056548465720861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2532649076075397954294481 1899486807056548465720861)
                  ·
                    refine ⟨712307552646205674645323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1899486807056548465720861 712307552646205674645323)
                    ·
                      rfl

theorem cell22_2080821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 5, 2, 2, 3].length) (baseStart_2080821 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2080821 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2080821 prefixEnd_2080821 := by exact prefixLift 2080821
  have htrace : WordTrace (prefixWord ++ tailWord_2080821) baseStart_2080821 baseEnd_2080821 := by
    simpa [prefixWord, tailWord_2080821, baseEnd_2080821] using wordTrace_append hprefix tailTrace_2080821
  have hstable : (prefixWord ++ tailWord_2080821).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2080821).length < 2 ^ (prefixWord ++ tailWord_2080821).sum := by decide
  have hdescent : baseEnd_2080821 < baseStart_2080821 := by decide
  rcases family_descends (prefixWord ++ tailWord_2080821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2080939 : List Nat := [1, 1, 1, 1, 2, 1, 1, 1, 10, 3]
def baseStart_2080939 : Nat := 118140960795 + 2080939 * 2 ^ 59
def prefixEnd_2080939 : Nat := 4983230072969 + 3 ^ 40 * 2080939 * 2
def baseEnd_2080939 : Nat := 712347946457692700194961

theorem tailTrace_2080939 : CollatzResearch.WordTrace tailWord_2080939 prefixEnd_2080939 712347946457692700194961 := by
  unfold tailWord_2080939
  simp only [CollatzResearch.WordTrace]
  refine ⟨75898080608120873931781871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50598720405413915954521247 75898080608120873931781871)
  ·
    refine ⟨113847120912181310897672807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75898080608120873931781871 113847120912181310897672807)
    ·
      refine ⟨170770681368271966346509211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113847120912181310897672807 170770681368271966346509211)
      ·
        refine ⟨256156022052407949519763817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170770681368271966346509211 256156022052407949519763817)
        ·
          refine ⟨192117016539305962139822863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 256156022052407949519763817 192117016539305962139822863)
          ·
            refine ⟨288175524808958943209734295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192117016539305962139822863 288175524808958943209734295)
            ·
              refine ⟨432263287213438414814601443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 288175524808958943209734295 432263287213438414814601443)
              ·
                refine ⟨648394930820157622221902165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 432263287213438414814601443 648394930820157622221902165)
                ·
                  refine ⟨1899594523887180533853229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 648394930820157622221902165 1899594523887180533853229)
                  ·
                    refine ⟨712347946457692700194961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1899594523887180533853229 712347946457692700194961)
                    ·
                      rfl

theorem cell22_2080939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 10, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 10, 3].length) (baseStart_2080939 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2080939 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2080939 prefixEnd_2080939 := by exact prefixLift 2080939
  have htrace : WordTrace (prefixWord ++ tailWord_2080939) baseStart_2080939 baseEnd_2080939 := by
    simpa [prefixWord, tailWord_2080939, baseEnd_2080939] using wordTrace_append hprefix tailTrace_2080939
  have hstable : (prefixWord ++ tailWord_2080939).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2080939).length < 2 ^ (prefixWord ++ tailWord_2080939).sum := by decide
  have hdescent : baseEnd_2080939 < baseStart_2080939 := by decide
  rcases family_descends (prefixWord ++ tailWord_2080939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2080954 : List Nat := [3, 1, 1, 1, 2, 2, 2, 2, 4, 4]
def baseStart_2080954 : Nat := 118140960795 + 2080954 * 2 ^ 59
def prefixEnd_2080954 : Nat := 4983230072969 + 3 ^ 40 * 2080954 * 2
def baseEnd_2080954 : Nat := 712353081264237661069915

theorem tailTrace_2080954 : CollatzResearch.WordTrace tailWord_2080954 prefixEnd_2080954 712353081264237661069915 := by
  unfold tailWord_2080954
  simp only [CollatzResearch.WordTrace]
  refine ⟨18974656925766632873394479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50599085135377687662385277 18974656925766632873394479)
  ·
    refine ⟨28461985388649949310091719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18974656925766632873394479 28461985388649949310091719)
    ·
      refine ⟨42692978082974923965137579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28461985388649949310091719 42692978082974923965137579)
      ·
        refine ⟨64039467124462385947706369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42692978082974923965137579 64039467124462385947706369)
        ·
          refine ⟨48029600343346789460779777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64039467124462385947706369 48029600343346789460779777)
          ·
            refine ⟨36022200257510092095584833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48029600343346789460779777 36022200257510092095584833)
            ·
              refine ⟨27016650193132569071688625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36022200257510092095584833 27016650193132569071688625)
              ·
                refine ⟨20262487644849426803766469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27016650193132569071688625 20262487644849426803766469)
                ·
                  refine ⟨3799216433409267525706213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20262487644849426803766469 3799216433409267525706213)
                  ·
                    refine ⟨712353081264237661069915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3799216433409267525706213 712353081264237661069915)
                    ·
                      rfl

theorem cell22_2080954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 2, 4, 4].length) (baseStart_2080954 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2080954 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2080954 prefixEnd_2080954 := by exact prefixLift 2080954
  have htrace : WordTrace (prefixWord ++ tailWord_2080954) baseStart_2080954 baseEnd_2080954 := by
    simpa [prefixWord, tailWord_2080954, baseEnd_2080954] using wordTrace_append hprefix tailTrace_2080954
  have hstable : (prefixWord ++ tailWord_2080954).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2080954).length < 2 ^ (prefixWord ++ tailWord_2080954).sum := by decide
  have hdescent : baseEnd_2080954 < baseStart_2080954 := by decide
  rcases family_descends (prefixWord ++ tailWord_2080954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2081029 : List Nat := [1, 3, 1, 1, 2, 1, 2, 2, 4, 5]
def baseStart_2081029 : Nat := 118140960795 + 2081029 * 2 ^ 59
def prefixEnd_2081029 : Nat := 4983230072969 + 3 ^ 40 * 2081029 * 2
def baseEnd_2081029 : Nat := 712378755296962465444685

theorem tailTrace_2081029 : CollatzResearch.WordTrace tailWord_2081029 prefixEnd_2081029 712378755296962465444685 := by
  unfold tailWord_2081029
  simp only [CollatzResearch.WordTrace]
  refine ⟨75901363177794819302558141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50600908785196546201705427 75901363177794819302558141)
  ·
    refine ⟨28463011191673057238459303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75901363177794819302558141 28463011191673057238459303)
    ·
      refine ⟨42694516787509585857688955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28463011191673057238459303 42694516787509585857688955)
      ·
        refine ⟨64041775181264378786533433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42694516787509585857688955 64041775181264378786533433)
        ·
          refine ⟨48031331385948284089900075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64041775181264378786533433 48031331385948284089900075)
          ·
            refine ⟨72046997078922426134850113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48031331385948284089900075 72046997078922426134850113)
            ·
              refine ⟨54035247809191819601137585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72046997078922426134850113 54035247809191819601137585)
              ·
                refine ⟨40526435856893864700853189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54035247809191819601137585 40526435856893864700853189)
                ·
                  refine ⟨7598706723167599631409973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40526435856893864700853189 7598706723167599631409973)
                  ·
                    refine ⟨712378755296962465444685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7598706723167599631409973 712378755296962465444685)
                    ·
                      rfl

theorem cell22_2081029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 2, 4, 5].length) (baseStart_2081029 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2081029 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2081029 prefixEnd_2081029 := by exact prefixLift 2081029
  have htrace : WordTrace (prefixWord ++ tailWord_2081029) baseStart_2081029 baseEnd_2081029 := by
    simpa [prefixWord, tailWord_2081029, baseEnd_2081029] using wordTrace_append hprefix tailTrace_2081029
  have hstable : (prefixWord ++ tailWord_2081029).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2081029).length < 2 ^ (prefixWord ++ tailWord_2081029).sum := by decide
  have hdescent : baseEnd_2081029 < baseStart_2081029 := by decide
  rcases family_descends (prefixWord ++ tailWord_2081029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2081091 : List Nat := [1, 1, 1, 3, 1, 3, 2, 1, 6, 3]
def baseStart_2081091 : Nat := 118140960795 + 2081091 * 2 ^ 59
def prefixEnd_2081091 : Nat := 4983230072969 + 3 ^ 40 * 2081091 * 2
def baseEnd_2081091 : Nat := 712399979164014970394495

theorem tailTrace_2081091 : CollatzResearch.WordTrace tailWord_2081091 prefixEnd_2081091 712399979164014970394495 := by
  unfold tailWord_2081091
  simp only [CollatzResearch.WordTrace]
  refine ⟨75903624503570203891315127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50602416335713469260876751 75903624503570203891315127)
  ·
    refine ⟨113855436755355305836972691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75903624503570203891315127 113855436755355305836972691)
    ·
      refine ⟨170783155133032958755459037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113855436755355305836972691 170783155133032958755459037)
      ·
        refine ⟨64043683174887359533297139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 170783155133032958755459037 64043683174887359533297139)
        ·
          refine ⟨96065524762331039299945709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64043683174887359533297139 96065524762331039299945709)
          ·
            refine ⟨36024571785874139737479641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96065524762331039299945709 36024571785874139737479641)
            ·
              refine ⟨27018428839405604803109731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36024571785874139737479641 27018428839405604803109731)
              ·
                refine ⟨40527643259108407204664597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27018428839405604803109731 40527643259108407204664597)
                ·
                  refine ⟨1899733277770706587718653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 40527643259108407204664597 1899733277770706587718653)
                  ·
                    refine ⟨712399979164014970394495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1899733277770706587718653 712399979164014970394495)
                    ·
                      rfl

theorem cell22_2081091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 1, 6, 3].length) (baseStart_2081091 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2081091 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2081091 prefixEnd_2081091 := by exact prefixLift 2081091
  have htrace : WordTrace (prefixWord ++ tailWord_2081091) baseStart_2081091 baseEnd_2081091 := by
    simpa [prefixWord, tailWord_2081091, baseEnd_2081091] using wordTrace_append hprefix tailTrace_2081091
  have hstable : (prefixWord ++ tailWord_2081091).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2081091).length < 2 ^ (prefixWord ++ tailWord_2081091).sum := by decide
  have hdescent : baseEnd_2081091 < baseStart_2081091 := by decide
  rcases family_descends (prefixWord ++ tailWord_2081091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2081104 : List Nat := [2, 1, 1, 1, 1, 16]
def baseStart_2081104 : Nat := 118140960795 + 2081104 * 2 ^ 59
def prefixEnd_2081104 : Nat := 4983230072969 + 3 ^ 40 * 2081104 * 2
def baseEnd_2081104 : Nat := 8795116411477620615055

theorem tailTrace_2081104 : CollatzResearch.WordTrace tailWord_2081104 prefixEnd_2081104 8795116411477620615055 := by
  unfold tailWord_2081104
  simp only [CollatzResearch.WordTrace]
  refine ⟨37952049326261553555769183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50602732435015404741025577 37952049326261553555769183)
  ·
    refine ⟨56928073989392330333653775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37952049326261553555769183 56928073989392330333653775)
    ·
      refine ⟨85392110984088495500480663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56928073989392330333653775 85392110984088495500480663)
      ·
        refine ⟨128088166476132743250720995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85392110984088495500480663 128088166476132743250720995)
        ·
          refine ⟨192132249714199114876081493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128088166476132743250720995 192132249714199114876081493)
          ·
            refine ⟨8795116411477620615055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 16 192132249714199114876081493 8795116411477620615055)
            ·
              rfl

theorem cell22_2081104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 16].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 16].length) (baseStart_2081104 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2081104 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2081104 prefixEnd_2081104 := by exact prefixLift 2081104
  have htrace : WordTrace (prefixWord ++ tailWord_2081104) baseStart_2081104 baseEnd_2081104 := by
    simpa [prefixWord, tailWord_2081104, baseEnd_2081104] using wordTrace_append hprefix tailTrace_2081104
  have hstable : (prefixWord ++ tailWord_2081104).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2081104).length < 2 ^ (prefixWord ++ tailWord_2081104).sum := by decide
  have hdescent : baseEnd_2081104 < baseStart_2081104 := by decide
  rcases family_descends (prefixWord ++ tailWord_2081104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2081138 : List Nat := [3, 2, 1, 2, 1, 4, 3, 6]
def baseStart_2081138 : Nat := 118140960795 + 2081138 * 2 ^ 59
def prefixEnd_2081138 : Nat := 4983230072969 + 3 ^ 40 * 2081138 * 2
def baseEnd_2081138 : Nat := 79157340913835834941039

theorem tailTrace_2081138 : CollatzResearch.WordTrace tailWord_2081138 prefixEnd_2081138 79157340913835834941039 := by
  unfold tailWord_2081138
  simp only [CollatzResearch.WordTrace]
  refine ⟨18976334683599982729569017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50603559156266620612184045 18976334683599982729569017)
  ·
    refine ⟨14232251012699987047176763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18976334683599982729569017 14232251012699987047176763)
    ·
      refine ⟨21348376519049980570765145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14232251012699987047176763 21348376519049980570765145)
      ·
        refine ⟨16011282389287485428073859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21348376519049980570765145 16011282389287485428073859)
        ·
          refine ⟨24016923583931228142110789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16011282389287485428073859 24016923583931228142110789)
          ·
            refine ⟨4503173171987105276645773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24016923583931228142110789 4503173171987105276645773)
            ·
              refine ⟨1688689939495164478742165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4503173171987105276645773 1688689939495164478742165)
              ·
                refine ⟨79157340913835834941039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1688689939495164478742165 79157340913835834941039)
                ·
                  rfl

theorem cell22_2081138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 3, 6].length) (baseStart_2081138 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2081138 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2081138 prefixEnd_2081138 := by exact prefixLift 2081138
  have htrace : WordTrace (prefixWord ++ tailWord_2081138) baseStart_2081138 baseEnd_2081138 := by
    simpa [prefixWord, tailWord_2081138, baseEnd_2081138] using wordTrace_append hprefix tailTrace_2081138
  have hstable : (prefixWord ++ tailWord_2081138).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2081138).length < 2 ^ (prefixWord ++ tailWord_2081138).sum := by decide
  have hdescent : baseEnd_2081138 < baseStart_2081138 := by decide
  rcases family_descends (prefixWord ++ tailWord_2081138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2081234 : List Nat := [3, 2, 2, 4, 1, 2, 2, 1, 5]
def baseStart_2081234 : Nat := 118140960795 + 2081234 * 2 ^ 59
def prefixEnd_2081234 : Nat := 4983230072969 + 3 ^ 40 * 2081234 * 2
def baseEnd_2081234 : Nat := 237482976995470088023019

theorem tailTrace_2081234 : CollatzResearch.WordTrace tailWord_2081234 prefixEnd_2081234 237482976995470088023019 := by
  unfold tailWord_2081234
  simp only [CollatzResearch.WordTrace]
  refine ⟨18977210035513034828442689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50605893428034759542513837 18977210035513034828442689)
  ·
    refine ⟨14232907526634776121332017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18977210035513034828442689 14232907526634776121332017)
    ·
      refine ⟨10674680644976082090999013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14232907526634776121332017 10674680644976082090999013)
      ·
        refine ⟨2001502620933015392062315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10674680644976082090999013 2001502620933015392062315)
        ·
          refine ⟨3002253931399523088093473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2001502620933015392062315 3002253931399523088093473)
          ·
            refine ⟨2251690448549642316070105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3002253931399523088093473 2251690448549642316070105)
            ·
              refine ⟨1688767836412231737052579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2251690448549642316070105 1688767836412231737052579)
              ·
                refine ⟨2533151754618347605578869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1688767836412231737052579 2533151754618347605578869)
                ·
                  refine ⟨237482976995470088023019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2533151754618347605578869 237482976995470088023019)
                  ·
                    rfl

theorem cell22_2081234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 2, 1, 5].length) (baseStart_2081234 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2081234 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2081234 prefixEnd_2081234 := by exact prefixLift 2081234
  have htrace : WordTrace (prefixWord ++ tailWord_2081234) baseStart_2081234 baseEnd_2081234 := by
    simpa [prefixWord, tailWord_2081234, baseEnd_2081234] using wordTrace_append hprefix tailTrace_2081234
  have hstable : (prefixWord ++ tailWord_2081234).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2081234).length < 2 ^ (prefixWord ++ tailWord_2081234).sum := by decide
  have hdescent : baseEnd_2081234 < baseStart_2081234 := by decide
  rcases family_descends (prefixWord ++ tailWord_2081234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2081271 : List Nat := [1, 1, 3, 1, 1, 1, 1, 2, 4, 7]
def baseStart_2081271 : Nat := 118140960795 + 2081271 * 2 ^ 59
def prefixEnd_2081271 : Nat := 4983230072969 + 3 ^ 40 * 2081271 * 2
def baseEnd_2081271 : Nat := 712461596842554500893943

theorem tailTrace_2081271 : CollatzResearch.WordTrace tailWord_2081271 prefixEnd_2081271 712461596842554500893943 := by
  unfold tailWord_2081271
  simp only [CollatzResearch.WordTrace]
  refine ⟨75910189642918094632867667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50606793095278729755245111 75910189642918094632867667)
  ·
    refine ⟨113865284464377141949301501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75910189642918094632867667 113865284464377141949301501)
    ·
      refine ⟨42699481674141428230988063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113865284464377141949301501 42699481674141428230988063)
      ·
        refine ⟨64049222511212142346482095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42699481674141428230988063 64049222511212142346482095)
        ·
          refine ⟨96073833766818213519723143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64049222511212142346482095 96073833766818213519723143)
          ·
            refine ⟨144110750650227320279584715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96073833766818213519723143 144110750650227320279584715)
            ·
              refine ⟨216166125975340980419377073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144110750650227320279584715 216166125975340980419377073)
              ·
                refine ⟨162124594481505735314532805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 216166125975340980419377073 162124594481505735314532805)
                ·
                  refine ⟨30398361465282325371474901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 162124594481505735314532805 30398361465282325371474901)
                  ·
                    refine ⟨712461596842554500893943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30398361465282325371474901 712461596842554500893943)
                    ·
                      rfl

theorem cell22_2081271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 4, 7].length) (baseStart_2081271 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2081271 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2081271 prefixEnd_2081271 := by exact prefixLift 2081271
  have htrace : WordTrace (prefixWord ++ tailWord_2081271) baseStart_2081271 baseEnd_2081271 := by
    simpa [prefixWord, tailWord_2081271, baseEnd_2081271] using wordTrace_append hprefix tailTrace_2081271
  have hstable : (prefixWord ++ tailWord_2081271).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2081271).length < 2 ^ (prefixWord ++ tailWord_2081271).sum := by decide
  have hdescent : baseEnd_2081271 < baseStart_2081271 := by decide
  rcases family_descends (prefixWord ++ tailWord_2081271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2081333 : List Nat := [1, 3, 3, 1, 1, 2, 1, 1, 4, 5]
def baseStart_2081333 : Nat := 118140960795 + 2081333 * 2 ^ 59
def prefixEnd_2081333 : Nat := 4983230072969 + 3 ^ 40 * 2081333 * 2
def baseEnd_2081333 : Nat := 712482820709607005843753

theorem tailTrace_2081333 : CollatzResearch.WordTrace tailWord_2081333 prefixEnd_2081333 712482820709607005843753 := by
  unfold tailWord_2081333
  simp only [CollatzResearch.WordTrace]
  refine ⟨75912450968693479221624653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50608300645795652814416435 75912450968693479221624653)
  ·
    refine ⟨28467169113260054708109245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75912450968693479221624653 28467169113260054708109245)
    ·
      refine ⟨10675188417472520515540967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28467169113260054708109245 10675188417472520515540967)
      ·
        refine ⟨16012782626208780773311451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10675188417472520515540967 16012782626208780773311451)
        ·
          refine ⟨24019173939313171159967177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16012782626208780773311451 24019173939313171159967177)
          ·
            refine ⟨18014380454484878369975383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24019173939313171159967177 18014380454484878369975383)
            ·
              refine ⟨27021570681727317554963075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18014380454484878369975383 27021570681727317554963075)
              ·
                refine ⟨40532356022590976332444613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27021570681727317554963075 40532356022590976332444613)
                ·
                  refine ⟨7599816754235808062333365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40532356022590976332444613 7599816754235808062333365)
                  ·
                    refine ⟨712482820709607005843753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7599816754235808062333365 712482820709607005843753)
                    ·
                      rfl

theorem cell22_2081333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 1, 4, 5].length) (baseStart_2081333 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2081333 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2081333 prefixEnd_2081333 := by exact prefixLift 2081333
  have htrace : WordTrace (prefixWord ++ tailWord_2081333) baseStart_2081333 baseEnd_2081333 := by
    simpa [prefixWord, tailWord_2081333, baseEnd_2081333] using wordTrace_append hprefix tailTrace_2081333
  have hstable : (prefixWord ++ tailWord_2081333).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2081333).length < 2 ^ (prefixWord ++ tailWord_2081333).sum := by decide
  have hdescent : baseEnd_2081333 < baseStart_2081333 := by decide
  rcases family_descends (prefixWord ++ tailWord_2081333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2081365 : List Nat := [1, 3, 2, 2, 1, 1, 3, 4, 1, 4]
def baseStart_2081365 : Nat := 118140960795 + 2081365 * 2 ^ 59
def prefixEnd_2081365 : Nat := 4983230072969 + 3 ^ 40 * 2081365 * 2
def baseEnd_2081365 : Nat := 712493774963569589043655

theorem tailTrace_2081365 : CollatzResearch.WordTrace tailWord_2081365 prefixEnd_2081365 712493774963569589043655 := by
  unfold tailWord_2081365
  simp only [CollatzResearch.WordTrace]
  refine ⟨75913618104577548686789549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50609078736385032457859699 75913618104577548686789549)
  ·
    refine ⟨28467606789216580757546081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75913618104577548686789549 28467606789216580757546081)
    ·
      refine ⟨21350705091912435568159561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28467606789216580757546081 21350705091912435568159561)
      ·
        refine ⟨16013028818934326676119671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21350705091912435568159561 16013028818934326676119671)
        ·
          refine ⟨24019543228401490014179507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16013028818934326676119671 24019543228401490014179507)
          ·
            refine ⟨36029314842602235021269261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24019543228401490014179507 36029314842602235021269261)
            ·
              refine ⟨13510993065975838132975973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36029314842602235021269261 13510993065975838132975973)
              ·
                refine ⟨2533311199870469649932995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13510993065975838132975973 2533311199870469649932995)
                ·
                  refine ⟨3799966799805704474899493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2533311199870469649932995 3799966799805704474899493)
                  ·
                    refine ⟨712493774963569589043655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3799966799805704474899493 712493774963569589043655)
                    ·
                      rfl

theorem cell22_2081365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 4, 1, 4].length) (baseStart_2081365 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2081365 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2081365 prefixEnd_2081365 := by exact prefixLift 2081365
  have htrace : WordTrace (prefixWord ++ tailWord_2081365) baseStart_2081365 baseEnd_2081365 := by
    simpa [prefixWord, tailWord_2081365, baseEnd_2081365] using wordTrace_append hprefix tailTrace_2081365
  have hstable : (prefixWord ++ tailWord_2081365).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2081365).length < 2 ^ (prefixWord ++ tailWord_2081365).sum := by decide
  have hdescent : baseEnd_2081365 < baseStart_2081365 := by decide
  rcases family_descends (prefixWord ++ tailWord_2081365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2081408 : List Nat := [2, 1, 1, 2, 1, 5, 1, 9]
def baseStart_2081408 : Nat := 118140960795 + 2081408 * 2 ^ 59
def prefixEnd_2081408 : Nat := 4983230072969 + 3 ^ 40 * 2081408 * 2
def baseEnd_2081408 : Nat := 79167610526925756690947

theorem tailTrace_2081408 : CollatzResearch.WordTrace tailWord_2081408 prefixEnd_2081408 79167610526925756690947 := by
  unfold tailWord_2081408
  simp only [CollatzResearch.WordTrace]
  refine ⟨37957593221710883515302439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50610124295614511353736585 37957593221710883515302439)
  ·
    refine ⟨56936389832566325272953659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37957593221710883515302439 56936389832566325272953659)
    ·
      refine ⟨85404584748849487909430489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56936389832566325272953659 85404584748849487909430489)
      ·
        refine ⟨64053438561637115932072867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85404584748849487909430489 64053438561637115932072867)
        ·
          refine ⟨96080157842455673898109301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64053438561637115932072867 96080157842455673898109301)
          ·
            refine ⟨9007514797730219427947747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 96080157842455673898109301 9007514797730219427947747)
            ·
              refine ⟨13511272196595329141921621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9007514797730219427947747 13511272196595329141921621)
              ·
                refine ⟨79167610526925756690947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 13511272196595329141921621 79167610526925756690947)
                ·
                  rfl

theorem cell22_2081408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 9].length) (baseStart_2081408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2081408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2081408 prefixEnd_2081408 := by exact prefixLift 2081408
  have htrace : WordTrace (prefixWord ++ tailWord_2081408) baseStart_2081408 baseEnd_2081408 := by
    simpa [prefixWord, tailWord_2081408, baseEnd_2081408] using wordTrace_append hprefix tailTrace_2081408
  have hstable : (prefixWord ++ tailWord_2081408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2081408).length < 2 ^ (prefixWord ++ tailWord_2081408).sum := by decide
  have hdescent : baseEnd_2081408 < baseStart_2081408 := by decide
  rcases family_descends (prefixWord ++ tailWord_2081408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2081478 : List Nat := [6, 1, 2, 1, 2, 2, 1, 1, 2, 4]
def baseStart_2081478 : Nat := 118140960795 + 2081478 * 2 ^ 59
def prefixEnd_2081478 : Nat := 4983230072969 + 3 ^ 40 * 2081478 * 2
def baseEnd_2081478 : Nat := 712532457172874960968309

theorem tailTrace_2081478 : CollatzResearch.WordTrace tailWord_2081478 prefixEnd_2081478 712532457172874960968309 := by
  unfold tailWord_2081478
  simp only [CollatzResearch.WordTrace]
  refine ⟨2372429361036505280801659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 50611826368778779323768725 2372429361036505280801659)
  ·
    refine ⟨3558644041554757921202489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2372429361036505280801659 3558644041554757921202489)
    ·
      refine ⟨2668983031166068440901867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3558644041554757921202489 2668983031166068440901867)
      ·
        refine ⟨4003474546749102661352801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2668983031166068440901867 4003474546749102661352801)
        ·
          refine ⟨3002605910061826996014601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4003474546749102661352801 3002605910061826996014601)
          ·
            refine ⟨2251954432546370247010951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3002605910061826996014601 2251954432546370247010951)
            ·
              refine ⟨3377931648819555370516427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2251954432546370247010951 3377931648819555370516427)
              ·
                refine ⟨5066897473229333055774641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3377931648819555370516427 5066897473229333055774641)
                ·
                  refine ⟨3800173104921999791830981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5066897473229333055774641 3800173104921999791830981)
                  ·
                    refine ⟨712532457172874960968309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3800173104921999791830981 712532457172874960968309)
                    ·
                      rfl

theorem cell22_2081478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 1, 1, 2, 4].length) (baseStart_2081478 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2081478 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2081478 prefixEnd_2081478 := by exact prefixLift 2081478
  have htrace : WordTrace (prefixWord ++ tailWord_2081478) baseStart_2081478 baseEnd_2081478 := by
    simpa [prefixWord, tailWord_2081478, baseEnd_2081478] using wordTrace_append hprefix tailTrace_2081478
  have hstable : (prefixWord ++ tailWord_2081478).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2081478).length < 2 ^ (prefixWord ++ tailWord_2081478).sum := by decide
  have hdescent : baseEnd_2081478 < baseStart_2081478 := by decide
  rcases family_descends (prefixWord ++ tailWord_2081478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2081534 : List Nat := [4, 2, 2, 1, 2, 1, 1, 4, 1, 4]
def baseStart_2081534 : Nat := 118140960795 + 2081534 * 2 ^ 59
def prefixEnd_2081534 : Nat := 4983230072969 + 3 ^ 40 * 2081534 * 2
def baseEnd_2081534 : Nat := 712551627117309481568137

theorem tailTrace_2081534 : CollatzResearch.WordTrace tailWord_2081534 prefixEnd_2081534 712551627117309481568137 := by
  unfold tailWord_2081534
  simp only [CollatzResearch.WordTrace]
  refine ⟨9489972755120661318711457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50613188027310193699794437 9489972755120661318711457)
  ·
    refine ⟨7117479566340495989033593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9489972755120661318711457 7117479566340495989033593)
    ·
      refine ⟨5338109674755371991775195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7117479566340495989033593 5338109674755371991775195)
      ·
        refine ⟨8007164512133057987662793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5338109674755371991775195 8007164512133057987662793)
        ·
          refine ⟨6005373384099793490747095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8007164512133057987662793 6005373384099793490747095)
          ·
            refine ⟨9008060076149690236120643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6005373384099793490747095 9008060076149690236120643)
            ·
              refine ⟨13512090114224535354180965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9008060076149690236120643 13512090114224535354180965)
              ·
                refine ⟨2533516896417100378908931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13512090114224535354180965 2533516896417100378908931)
                ·
                  refine ⟨3800275344625650568363397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2533516896417100378908931 3800275344625650568363397)
                  ·
                    refine ⟨712551627117309481568137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3800275344625650568363397 712551627117309481568137)
                    ·
                      rfl

theorem cell22_2081534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 4, 1, 4].length) (baseStart_2081534 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2081534 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2081534 prefixEnd_2081534 := by exact prefixLift 2081534
  have htrace : WordTrace (prefixWord ++ tailWord_2081534) baseStart_2081534 baseEnd_2081534 := by
    simpa [prefixWord, tailWord_2081534, baseEnd_2081534] using wordTrace_append hprefix tailTrace_2081534
  have hstable : (prefixWord ++ tailWord_2081534).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2081534).length < 2 ^ (prefixWord ++ tailWord_2081534).sum := by decide
  have hdescent : baseEnd_2081534 < baseStart_2081534 := by decide
  rcases family_descends (prefixWord ++ tailWord_2081534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2081545 : List Nat := [1, 2, 1, 1, 3, 2, 4, 1, 1, 6]
def baseStart_2081545 : Nat := 118140960795 + 2081545 * 2 ^ 59
def prefixEnd_2081545 : Nat := 4983230072969 + 3 ^ 40 * 2081545 * 2
def baseEnd_2081545 : Nat := 712555392642109119543103

theorem tailTrace_2081545 : CollatzResearch.WordTrace tailWord_2081545 prefixEnd_2081545 712555392642109119543103 := by
  unfold tailWord_2081545
  simp only [CollatzResearch.WordTrace]
  refine ⟨75920183243925439428342089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50613455495950292952228059 75920183243925439428342089)
  ·
    refine ⟨56940137432944079571256567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75920183243925439428342089 56940137432944079571256567)
    ·
      refine ⟨85410206149416119356884851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56940137432944079571256567 85410206149416119356884851)
      ·
        refine ⟨128115309224124179035327277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85410206149416119356884851 128115309224124179035327277)
        ·
          refine ⟨48043240959046567138247729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128115309224124179035327277 48043240959046567138247729)
          ·
            refine ⟨36032430719284925353685797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48043240959046567138247729 36032430719284925353685797)
            ·
              refine ⟨6756080759865923503816087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36032430719284925353685797 6756080759865923503816087)
              ·
                refine ⟨10134121139798885255724131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6756080759865923503816087 10134121139798885255724131)
                ·
                  refine ⟨15201181709698327883586197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10134121139798885255724131 15201181709698327883586197)
                  ·
                    refine ⟨712555392642109119543103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15201181709698327883586197 712555392642109119543103)
                    ·
                      rfl

theorem cell22_2081545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4, 1, 1, 6].length) (baseStart_2081545 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2081545 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2081545 prefixEnd_2081545 := by exact prefixLift 2081545
  have htrace : WordTrace (prefixWord ++ tailWord_2081545) baseStart_2081545 baseEnd_2081545 := by
    simpa [prefixWord, tailWord_2081545, baseEnd_2081545] using wordTrace_append hprefix tailTrace_2081545
  have hstable : (prefixWord ++ tailWord_2081545).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2081545).length < 2 ^ (prefixWord ++ tailWord_2081545).sum := by decide
  have hdescent : baseEnd_2081545 < baseStart_2081545 := by decide
  rcases family_descends (prefixWord ++ tailWord_2081545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2081562 : List Nat := [3, 1, 1, 3, 2, 1, 3, 2, 2, 4]
def baseStart_2081562 : Nat := 118140960795 + 2081562 * 2 ^ 59
def prefixEnd_2081562 : Nat := 4983230072969 + 3 ^ 40 * 2081562 * 2
def baseEnd_2081562 : Nat := 712561212089526741868051

theorem tailTrace_2081562 : CollatzResearch.WordTrace tailWord_2081562 prefixEnd_2081562 712561212089526741868051 := by
  unfold tailWord_2081562
  simp only [CollatzResearch.WordTrace]
  refine ⟨18980200821215962832927735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50613868856575900887807293 18980200821215962832927735)
  ·
    refine ⟨28470301231823944249391603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18980200821215962832927735 28470301231823944249391603)
    ·
      refine ⟨42705451847735916374087405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28470301231823944249391603 42705451847735916374087405)
      ·
        refine ⟨16014544442900968640282777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42705451847735916374087405 16014544442900968640282777)
        ·
          refine ⟨12010908332175726480212083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16014544442900968640282777 12010908332175726480212083)
          ·
            refine ⟨18016362498263589720318125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12010908332175726480212083 18016362498263589720318125)
            ·
              refine ⟨6756135936848846145119297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18016362498263589720318125 6756135936848846145119297)
              ·
                refine ⟨5067101952636634608839473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6756135936848846145119297 5067101952636634608839473)
                ·
                  refine ⟨3800326464477475956629605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5067101952636634608839473 3800326464477475956629605)
                  ·
                    refine ⟨712561212089526741868051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3800326464477475956629605 712561212089526741868051)
                    ·
                      rfl

theorem cell22_2081562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 3, 2, 2, 4].length) (baseStart_2081562 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2081562 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2081562 prefixEnd_2081562 := by exact prefixLift 2081562
  have htrace : WordTrace (prefixWord ++ tailWord_2081562) baseStart_2081562 baseEnd_2081562 := by
    simpa [prefixWord, tailWord_2081562, baseEnd_2081562] using wordTrace_append hprefix tailTrace_2081562
  have hstable : (prefixWord ++ tailWord_2081562).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2081562).length < 2 ^ (prefixWord ++ tailWord_2081562).sum := by decide
  have hdescent : baseEnd_2081562 < baseStart_2081562 := by decide
  rcases family_descends (prefixWord ++ tailWord_2081562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2081592 : List Nat := [2, 1, 2, 1, 3, 2, 2, 1, 5, 3]
def baseStart_2081592 : Nat := 118140960795 + 2081592 * 2 ^ 59
def prefixEnd_2081592 : Nat := 4983230072969 + 3 ^ 40 * 2081592 * 2
def baseEnd_2081592 : Nat := 712571481702616663617959

theorem tailTrace_2081592 : CollatzResearch.WordTrace tailWord_2081592 prefixEnd_2081592 712571481702616663617959 := by
  unfold tailWord_2081592
  simp only [CollatzResearch.WordTrace]
  refine ⟨37960948737377583227651515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50614598316503444303535353 37960948737377583227651515)
  ·
    refine ⟨56941423106066374841477273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37960948737377583227651515 56941423106066374841477273)
    ·
      refine ⟨42706067329549781131107955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56941423106066374841477273 42706067329549781131107955)
      ·
        refine ⟨64059100994324671696661933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42706067329549781131107955 64059100994324671696661933)
        ·
          refine ⟨24022162872871751886248225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64059100994324671696661933 24022162872871751886248225)
          ·
            refine ⟨18016622154653813914686169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24022162872871751886248225 18016622154653813914686169)
            ·
              refine ⟨13512466615990360436014627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18016622154653813914686169 13512466615990360436014627)
              ·
                refine ⟨20268699923985540654021941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13512466615990360436014627 20268699923985540654021941)
                ·
                  refine ⟨1900190617873644436314557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20268699923985540654021941 1900190617873644436314557)
                  ·
                    refine ⟨712571481702616663617959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1900190617873644436314557 712571481702616663617959)
                    ·
                      rfl

theorem cell22_2081592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 1, 5, 3].length) (baseStart_2081592 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2081592 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2081592 prefixEnd_2081592 := by exact prefixLift 2081592
  have htrace : WordTrace (prefixWord ++ tailWord_2081592) baseStart_2081592 baseEnd_2081592 := by
    simpa [prefixWord, tailWord_2081592, baseEnd_2081592] using wordTrace_append hprefix tailTrace_2081592
  have hstable : (prefixWord ++ tailWord_2081592).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2081592).length < 2 ^ (prefixWord ++ tailWord_2081592).sum := by decide
  have hdescent : baseEnd_2081592 < baseStart_2081592 := by decide
  rcases family_descends (prefixWord ++ tailWord_2081592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2081605 : List Nat := [1, 3, 1, 1, 1, 2, 2, 4, 7]
def baseStart_2081605 : Nat := 118140960795 + 2081605 * 2 ^ 59
def prefixEnd_2081605 : Nat := 4983230072969 + 3 ^ 40 * 2081605 * 2
def baseEnd_2081605 : Nat := 237525310622762987680973

theorem tailTrace_2081605 : CollatzResearch.WordTrace tailWord_2081605 prefixEnd_2081605 237525310622762987680973 := by
  unfold tailWord_2081605
  simp only [CollatzResearch.WordTrace]
  refine ⟨75922371623708069675526269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50614914415805379783684179 75922371623708069675526269)
  ·
    refine ⟨28470889358890526128322351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75922371623708069675526269 28470889358890526128322351)
    ·
      refine ⟨42706334038335789192483527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28470889358890526128322351 42706334038335789192483527)
      ·
        refine ⟨64059501057503683788725291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42706334038335789192483527 64059501057503683788725291)
        ·
          refine ⟨96089251586255525683087937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64059501057503683788725291 96089251586255525683087937)
          ·
            refine ⟨72066938689691644262315953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96089251586255525683087937 72066938689691644262315953)
            ·
              refine ⟨54050204017268733196736965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72066938689691644262315953 54050204017268733196736965)
              ·
                refine ⟨10134413253237887474388181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54050204017268733196736965 10134413253237887474388181)
                ·
                  refine ⟨237525310622762987680973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10134413253237887474388181 237525310622762987680973)
                  ·
                    rfl

theorem cell22_2081605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 4, 7].length) (baseStart_2081605 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2081605 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2081605 prefixEnd_2081605 := by exact prefixLift 2081605
  have htrace : WordTrace (prefixWord ++ tailWord_2081605) baseStart_2081605 baseEnd_2081605 := by
    simpa [prefixWord, tailWord_2081605, baseEnd_2081605] using wordTrace_append hprefix tailTrace_2081605
  have hstable : (prefixWord ++ tailWord_2081605).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2081605).length < 2 ^ (prefixWord ++ tailWord_2081605).sum := by decide
  have hdescent : baseEnd_2081605 < baseStart_2081605 := by decide
  rcases family_descends (prefixWord ++ tailWord_2081605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2081626 : List Nat := [3, 1, 1, 2, 1, 5, 1, 4, 1, 3]
def baseStart_2081626 : Nat := 118140960795 + 2081626 * 2 ^ 59
def prefixEnd_2081626 : Nat := 4983230072969 + 3 ^ 40 * 2081626 * 2
def baseEnd_2081626 : Nat := 712583120597451908267855

theorem tailTrace_2081626 : CollatzResearch.WordTrace tailWord_2081626 prefixEnd_2081626 712583120597451908267855 := by
  unfold tailWord_2081626
  simp only [CollatzResearch.WordTrace]
  refine ⟨18980784389157997565510183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50615425037754660174693821 18980784389157997565510183)
  ·
    refine ⟨28471176583736996348265275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18980784389157997565510183 28471176583736996348265275)
    ·
      refine ⟨42706764875605494522397913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28471176583736996348265275 42706764875605494522397913)
      ·
        refine ⟨32030073656704120891798435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42706764875605494522397913 32030073656704120891798435)
        ·
          refine ⟨48045110485056181337697653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32030073656704120891798435 48045110485056181337697653)
          ·
            refine ⟨4504229107974017000409155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 48045110485056181337697653 4504229107974017000409155)
            ·
              refine ⟨6756343661961025500613733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4504229107974017000409155 6756343661961025500613733)
              ·
                refine ⟨1266814436617692281365075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6756343661961025500613733 1266814436617692281365075)
                ·
                  refine ⟨1900221654926538422047613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1266814436617692281365075 1900221654926538422047613)
                  ·
                    refine ⟨712583120597451908267855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1900221654926538422047613 712583120597451908267855)
                    ·
                      rfl

theorem cell22_2081626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 1, 4, 1, 3].length) (baseStart_2081626 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2081626 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2081626 prefixEnd_2081626 := by exact prefixLift 2081626
  have htrace : WordTrace (prefixWord ++ tailWord_2081626) baseStart_2081626 baseEnd_2081626 := by
    simpa [prefixWord, tailWord_2081626, baseEnd_2081626] using wordTrace_append hprefix tailTrace_2081626
  have hstable : (prefixWord ++ tailWord_2081626).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2081626).length < 2 ^ (prefixWord ++ tailWord_2081626).sum := by decide
  have hdescent : baseEnd_2081626 < baseStart_2081626 := by decide
  rcases family_descends (prefixWord ++ tailWord_2081626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2081669 : List Nat := [1, 3, 1, 1, 3, 4, 1, 3, 1, 4]
def baseStart_2081669 : Nat := 118140960795 + 2081669 * 2 ^ 59
def prefixEnd_2081669 : Nat := 4983230072969 + 3 ^ 40 * 2081669 * 2
def baseEnd_2081669 : Nat := 712597840376214129442723

theorem tailTrace_2081669 : CollatzResearch.WordTrace tailWord_2081669 prefixEnd_2081669 712597840376214129442723 := by
  unfold tailWord_2081669
  simp only [CollatzResearch.WordTrace]
  refine ⟨75924705895476208605856061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50616470596984139070570707 75924705895476208605856061)
  ·
    refine ⟨28471764710803578227196023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75924705895476208605856061 28471764710803578227196023)
    ·
      refine ⟨42707647066205367340794035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28471764710803578227196023 42707647066205367340794035)
      ·
        refine ⟨64061470599308051011191053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42707647066205367340794035 64061470599308051011191053)
        ·
          refine ⟨24023051474740519129196645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64061470599308051011191053 24023051474740519129196645)
          ·
            refine ⟨4504322151513847336724371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24023051474740519129196645 4504322151513847336724371)
            ·
              refine ⟨6756483227270771005086557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4504322151513847336724371 6756483227270771005086557)
              ·
                refine ⟨2533681210226539126907459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6756483227270771005086557 2533681210226539126907459)
                ·
                  refine ⟨3800521815339808690361189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2533681210226539126907459 3800521815339808690361189)
                  ·
                    refine ⟨712597840376214129442723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3800521815339808690361189 712597840376214129442723)
                    ·
                      rfl

theorem cell22_2081669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 1, 3, 1, 4].length) (baseStart_2081669 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2081669 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2081669 prefixEnd_2081669 := by exact prefixLift 2081669
  have htrace : WordTrace (prefixWord ++ tailWord_2081669) baseStart_2081669 baseEnd_2081669 := by
    simpa [prefixWord, tailWord_2081669, baseEnd_2081669] using wordTrace_append hprefix tailTrace_2081669
  have hstable : (prefixWord ++ tailWord_2081669).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2081669).length < 2 ^ (prefixWord ++ tailWord_2081669).sum := by decide
  have hdescent : baseEnd_2081669 < baseStart_2081669 := by decide
  rcases family_descends (prefixWord ++ tailWord_2081669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2081684 : List Nat := [2, 4, 2, 1, 1, 1, 4, 1, 6]
def baseStart_2081684 : Nat := 118140960795 + 2081684 * 2 ^ 59
def prefixEnd_2081684 : Nat := 4983230072969 + 3 ^ 40 * 2081684 * 2
def baseEnd_2081684 : Nat := 237534325060919696772559

theorem tailTrace_2081684 : CollatzResearch.WordTrace tailWord_2081684 prefixEnd_2081684 237534325060919696772559 := by
  unfold tailWord_2081684
  simp only [CollatzResearch.WordTrace]
  refine ⟨37962626495210933083826053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50616835326947910778434737 37962626495210933083826053)
  ·
    refine ⟨7117992467852049953217385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37962626495210933083826053 7117992467852049953217385)
    ·
      refine ⟨5338494350889037464913039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7117992467852049953217385 5338494350889037464913039)
      ·
        refine ⟨8007741526333556197369559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5338494350889037464913039 8007741526333556197369559)
        ·
          refine ⟨12011612289500334296054339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8007741526333556197369559 12011612289500334296054339)
          ·
            refine ⟨18017418434250501444081509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12011612289500334296054339 18017418434250501444081509)
            ·
              refine ⟨3378265956421969020765283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18017418434250501444081509 3378265956421969020765283)
              ·
                refine ⟨5067398934632953531147925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3378265956421969020765283 5067398934632953531147925)
                ·
                  refine ⟨237534325060919696772559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5067398934632953531147925 237534325060919696772559)
                  ·
                    rfl

theorem cell22_2081684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 4, 1, 6].length) (baseStart_2081684 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2081684 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2081684 prefixEnd_2081684 := by exact prefixLift 2081684
  have htrace : WordTrace (prefixWord ++ tailWord_2081684) baseStart_2081684 baseEnd_2081684 := by
    simpa [prefixWord, tailWord_2081684, baseEnd_2081684] using wordTrace_append hprefix tailTrace_2081684
  have hstable : (prefixWord ++ tailWord_2081684).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2081684).length < 2 ^ (prefixWord ++ tailWord_2081684).sum := by decide
  have hdescent : baseEnd_2081684 < baseStart_2081684 := by decide
  rcases family_descends (prefixWord ++ tailWord_2081684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2081699 : List Nat := [1, 1, 1, 4, 1, 2, 2, 5, 2, 3]
def baseStart_2081699 : Nat := 118140960795 + 2081699 * 2 ^ 59
def prefixEnd_2081699 : Nat := 4983230072969 + 3 ^ 40 * 2081699 * 2
def baseEnd_2081699 : Nat := 712608109989304051192631

theorem tailTrace_2081699 : CollatzResearch.WordTrace tailWord_2081699 prefixEnd_2081699 712608109989304051192631 := by
  unfold tailWord_2081699
  simp only [CollatzResearch.WordTrace]
  refine ⟨75925800085367523729448151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50617200056911682486298767 75925800085367523729448151)
  ·
    refine ⟨113888700128051285594172227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75925800085367523729448151 113888700128051285594172227)
    ·
      refine ⟨170833050192076928391258341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113888700128051285594172227 170833050192076928391258341)
      ·
        refine ⟨32031196911014424073360939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 170833050192076928391258341 32031196911014424073360939)
        ·
          refine ⟨48046795366521636110041409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32031196911014424073360939 48046795366521636110041409)
          ·
            refine ⟨36035096524891227082531057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48046795366521636110041409 36035096524891227082531057)
            ·
              refine ⟨27026322393668420311898293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36035096524891227082531057 27026322393668420311898293)
              ·
                refine ⟨2533717724406414404240465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27026322393668420311898293 2533717724406414404240465)
                ·
                  refine ⟨1900288293304810803180349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2533717724406414404240465 1900288293304810803180349)
                  ·
                    refine ⟨712608109989304051192631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1900288293304810803180349 712608109989304051192631)
                    ·
                      rfl

theorem cell22_2081699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 5, 2, 3].length) (baseStart_2081699 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2081699 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2081699 prefixEnd_2081699 := by exact prefixLift 2081699
  have htrace : WordTrace (prefixWord ++ tailWord_2081699) baseStart_2081699 baseEnd_2081699 := by
    simpa [prefixWord, tailWord_2081699, baseEnd_2081699] using wordTrace_append hprefix tailTrace_2081699
  have hstable : (prefixWord ++ tailWord_2081699).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2081699).length < 2 ^ (prefixWord ++ tailWord_2081699).sum := by decide
  have hdescent : baseEnd_2081699 < baseStart_2081699 := by decide
  rcases family_descends (prefixWord ++ tailWord_2081699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2081750 : List Nat := [5, 2, 1, 1, 2, 1, 4, 1, 2, 3]
def baseStart_2081750 : Nat := 118140960795 + 2081750 * 2 ^ 59
def prefixEnd_2081750 : Nat := 4983230072969 + 3 ^ 40 * 2081750 * 2
def baseEnd_2081750 : Nat := 712625568331556918167475

theorem tailTrace_2081750 : CollatzResearch.WordTrace tailWord_2081750 prefixEnd_2081750 712625568331556918167475 := by
  unfold tailWord_2081750
  simp only [CollatzResearch.WordTrace]
  refine ⟨4745478763011422464972169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 50618440138788506293036469 4745478763011422464972169)
  ·
    refine ⟨3559109072258566848729127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4745478763011422464972169 3559109072258566848729127)
    ·
      refine ⟨5338663608387850273093691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3559109072258566848729127 5338663608387850273093691)
      ·
        refine ⟨8007995412581775409640537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5338663608387850273093691 8007995412581775409640537)
        ·
          refine ⟨6005996559436331557230403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8007995412581775409640537 6005996559436331557230403)
          ·
            refine ⟨9008994839154497335845605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6005996559436331557230403 9008994839154497335845605)
            ·
              refine ⟨1689186532341468250471051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9008994839154497335845605 1689186532341468250471051)
              ·
                refine ⟨2533779798512202375706577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1689186532341468250471051 2533779798512202375706577)
                ·
                  refine ⟨1900334848884151781779933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2533779798512202375706577 1900334848884151781779933)
                  ·
                    refine ⟨712625568331556918167475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1900334848884151781779933 712625568331556918167475)
                    ·
                      rfl

theorem cell22_2081750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 4, 1, 2, 3].length) (baseStart_2081750 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2081750 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2081750 prefixEnd_2081750 := by exact prefixLift 2081750
  have htrace : WordTrace (prefixWord ++ tailWord_2081750) baseStart_2081750 baseEnd_2081750 := by
    simpa [prefixWord, tailWord_2081750, baseEnd_2081750] using wordTrace_append hprefix tailTrace_2081750
  have hstable : (prefixWord ++ tailWord_2081750).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2081750).length < 2 ^ (prefixWord ++ tailWord_2081750).sum := by decide
  have hdescent : baseEnd_2081750 < baseStart_2081750 := by decide
  rcases family_descends (prefixWord ++ tailWord_2081750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2081772 : List Nat := [2, 2, 1, 1, 2, 1, 1, 1, 6, 5]
def baseStart_2081772 : Nat := 118140960795 + 2081772 * 2 ^ 59
def prefixEnd_2081772 : Nat := 4983230072969 + 3 ^ 40 * 2081772 * 2
def baseEnd_2081772 : Nat := 712633099381156194117407

theorem tailTrace_2081772 : CollatzResearch.WordTrace tailWord_2081772 prefixEnd_2081772 712633099381156194117407 := by
  unfold tailWord_2081772
  simp only [CollatzResearch.WordTrace]
  refine ⟨37964231307051528598427785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50618975076068704797903713 37964231307051528598427785)
  ·
    refine ⟨28473173480288646448820839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37964231307051528598427785 28473173480288646448820839)
    ·
      refine ⟨42709760220432969673231259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28473173480288646448820839 42709760220432969673231259)
      ·
        refine ⟨64064640330649454509846889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42709760220432969673231259 64064640330649454509846889)
        ·
          refine ⟨48048480247987090882385167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64064640330649454509846889 48048480247987090882385167)
          ·
            refine ⟨72072720371980636323577751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48048480247987090882385167 72072720371980636323577751)
            ·
              refine ⟨108109080557970954485366627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72072720371980636323577751 108109080557970954485366627)
              ·
                refine ⟨162163620836956431728049941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108109080557970954485366627 162163620836956431728049941)
                ·
                  refine ⟨7601419726732332737252341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 162163620836956431728049941 7601419726732332737252341)
                  ·
                    refine ⟨712633099381156194117407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7601419726732332737252341 712633099381156194117407)
                    ·
                      rfl

theorem cell22_2081772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 5].length) (baseStart_2081772 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2081772 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2081772 prefixEnd_2081772 := by exact prefixLift 2081772
  have htrace : WordTrace (prefixWord ++ tailWord_2081772) baseStart_2081772 baseEnd_2081772 := by
    simpa [prefixWord, tailWord_2081772, baseEnd_2081772] using wordTrace_append hprefix tailTrace_2081772
  have hstable : (prefixWord ++ tailWord_2081772).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2081772).length < 2 ^ (prefixWord ++ tailWord_2081772).sum := by decide
  have hdescent : baseEnd_2081772 < baseStart_2081772 := by decide
  rcases family_descends (prefixWord ++ tailWord_2081772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2081780 : List Nat := [2, 6, 2, 1, 2, 9]
def baseStart_2081780 : Nat := 118140960795 + 2081780 * 2 ^ 59
def prefixEnd_2081780 : Nat := 4983230072969 + 3 ^ 40 * 2081780 * 2
def baseEnd_2081780 : Nat := 8797973307958602961943

theorem tailTrace_2081780 : CollatzResearch.WordTrace tailWord_2081780 prefixEnd_2081780 8797973307958602961943 := by
  unfold tailWord_2081780
  simp only [CollatzResearch.WordTrace]
  refine ⟨37964377199037037281573397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50619169598716049708764529 37964377199037037281573397)
  ·
    refine ⟨1779580181204861122573753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 37964377199037037281573397 1779580181204861122573753)
    ·
      refine ⟨1334685135903645841930315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1779580181204861122573753 1334685135903645841930315)
      ·
        refine ⟨2002027703855468762895473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1334685135903645841930315 2002027703855468762895473)
        ·
          refine ⟨1501520777891601572171605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2002027703855468762895473 1501520777891601572171605)
          ·
            refine ⟨8797973307958602961943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1501520777891601572171605 8797973307958602961943)
            ·
              rfl

theorem cell22_2081780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 9].length) (baseStart_2081780 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2081780 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2081780 prefixEnd_2081780 := by exact prefixLift 2081780
  have htrace : WordTrace (prefixWord ++ tailWord_2081780) baseStart_2081780 baseEnd_2081780 := by
    simpa [prefixWord, tailWord_2081780, baseEnd_2081780] using wordTrace_append hprefix tailTrace_2081780
  have hstable : (prefixWord ++ tailWord_2081780).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2081780).length < 2 ^ (prefixWord ++ tailWord_2081780).sum := by decide
  have hdescent : baseEnd_2081780 < baseStart_2081780 := by decide
  rcases family_descends (prefixWord ++ tailWord_2081780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2081804 : List Nat := [2, 2, 1, 2, 3, 2, 1, 2, 3, 4]
def baseStart_2081804 : Nat := 118140960795 + 2081804 * 2 ^ 59
def prefixEnd_2081804 : Nat := 4983230072969 + 3 ^ 40 * 2081804 * 2
def baseEnd_2081804 : Nat := 712644053635118777317309

theorem tailTrace_2081804 : CollatzResearch.WordTrace tailWord_2081804 prefixEnd_2081804 712644053635118777317309 := by
  unfold tailWord_2081804
  simp only [CollatzResearch.WordTrace]
  refine ⟨37964814874993563331010233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50619753166658084441346977 37964814874993563331010233)
  ·
    refine ⟨28473611156245172498257675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37964814874993563331010233 28473611156245172498257675)
    ·
      refine ⟨42710416734367758747386513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28473611156245172498257675 42710416734367758747386513)
      ·
        refine ⟨32032812550775819060539885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42710416734367758747386513 32032812550775819060539885)
        ·
          refine ⟨12012304706540932147702457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32032812550775819060539885 12012304706540932147702457)
          ·
            refine ⟨9009228529905699110776843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12012304706540932147702457 9009228529905699110776843)
            ·
              refine ⟨13513842794858548666165265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9009228529905699110776843 13513842794858548666165265)
              ·
                refine ⟨10135382096143911499623949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13513842794858548666165265 10135382096143911499623949)
                ·
                  refine ⟨3800768286053966812358981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10135382096143911499623949 3800768286053966812358981)
                  ·
                    refine ⟨712644053635118777317309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3800768286053966812358981 712644053635118777317309)
                    ·
                      rfl

theorem cell22_2081804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 2, 3, 4].length) (baseStart_2081804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2081804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2081804 prefixEnd_2081804 := by exact prefixLift 2081804
  have htrace : WordTrace (prefixWord ++ tailWord_2081804) baseStart_2081804 baseEnd_2081804 := by
    simpa [prefixWord, tailWord_2081804, baseEnd_2081804] using wordTrace_append hprefix tailTrace_2081804
  have hstable : (prefixWord ++ tailWord_2081804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2081804).length < 2 ^ (prefixWord ++ tailWord_2081804).sum := by decide
  have hdescent : baseEnd_2081804 < baseStart_2081804 := by decide
  rcases family_descends (prefixWord ++ tailWord_2081804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2081836 : List Nat := [2, 2, 1, 1, 1, 2, 6, 3, 4]
def baseStart_2081836 : Nat := 118140960795 + 2081836 * 2 ^ 59
def prefixEnd_2081836 : Nat := 4983230072969 + 3 ^ 40 * 2081836 * 2
def baseEnd_2081836 : Nat := 237551669296360453505737

theorem tailTrace_2081836 : CollatzResearch.WordTrace tailWord_2081836 prefixEnd_2081836 237551669296360453505737 := by
  unfold tailWord_2081836
  simp only [CollatzResearch.WordTrace]
  refine ⟨37965398442935598063592681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50620531257247464084790241 37965398442935598063592681)
  ·
    refine ⟨28474048832201698547694511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37965398442935598063592681 28474048832201698547694511)
    ·
      refine ⟨42711073248302547821541767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28474048832201698547694511 42711073248302547821541767)
      ·
        refine ⟨64066609872453821732312651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42711073248302547821541767 64066609872453821732312651)
        ·
          refine ⟨96099914808680732598468977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64066609872453821732312651 96099914808680732598468977)
          ·
            refine ⟨72074936106510549448851733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96099914808680732598468977 72074936106510549448851733)
            ·
              refine ⟨3378512629992682005414925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 72074936106510549448851733 3378512629992682005414925)
              ·
                refine ⟨1266942236247255752030597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3378512629992682005414925 1266942236247255752030597)
                ·
                  refine ⟨237551669296360453505737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1266942236247255752030597 237551669296360453505737)
                  ·
                    rfl

theorem cell22_2081836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 6, 3, 4].length) (baseStart_2081836 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2081836 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2081836 prefixEnd_2081836 := by exact prefixLift 2081836
  have htrace : WordTrace (prefixWord ++ tailWord_2081836) baseStart_2081836 baseEnd_2081836 := by
    simpa [prefixWord, tailWord_2081836, baseEnd_2081836] using wordTrace_append hprefix tailTrace_2081836
  have hstable : (prefixWord ++ tailWord_2081836).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2081836).length < 2 ^ (prefixWord ++ tailWord_2081836).sum := by decide
  have hdescent : baseEnd_2081836 < baseStart_2081836 := by decide
  rcases family_descends (prefixWord ++ tailWord_2081836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2081988 : List Nat := [2, 3, 3, 1, 3, 1, 1, 2, 6]
def baseStart_2081988 : Nat := 118140960795 + 2081988 * 2 ^ 59
def prefixEnd_2081988 : Nat := 4983230072969 + 3 ^ 40 * 2081988 * 2
def baseEnd_2081988 : Nat := 237569013531801210238915

theorem tailTrace_2081988 : CollatzResearch.WordTrace tailWord_2081988 prefixEnd_2081988 237569013531801210238915 := by
  unfold tailWord_2081988
  simp only [CollatzResearch.WordTrace]
  refine ⟨37968170390660263043359309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50624227187547017391145745 37968170390660263043359309)
  ·
    refine ⟨14238063896497598641259741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37968170390660263043359309 14238063896497598641259741)
    ·
      refine ⟨5339273961186599490472403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14238063896497598641259741 5339273961186599490472403)
      ·
        refine ⟨8008910941779899235708605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5339273961186599490472403 8008910941779899235708605)
        ·
          refine ⟨3003341603167462213390727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8008910941779899235708605 3003341603167462213390727)
          ·
            refine ⟨4505012404751193320086091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3003341603167462213390727 4505012404751193320086091)
            ·
              refine ⟨6757518607126789980129137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4505012404751193320086091 6757518607126789980129137)
              ·
                refine ⟨5068138955345092485096853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6757518607126789980129137 5068138955345092485096853)
                ·
                  refine ⟨237569013531801210238915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5068138955345092485096853 237569013531801210238915)
                  ·
                    rfl

theorem cell22_2081988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 1, 2, 6].length) (baseStart_2081988 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2081988 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2081988 prefixEnd_2081988 := by exact prefixLift 2081988
  have htrace : WordTrace (prefixWord ++ tailWord_2081988) baseStart_2081988 baseEnd_2081988 := by
    simpa [prefixWord, tailWord_2081988, baseEnd_2081988] using wordTrace_append hprefix tailTrace_2081988
  have hstable : (prefixWord ++ tailWord_2081988).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2081988).length < 2 ^ (prefixWord ++ tailWord_2081988).sum := by decide
  have hdescent : baseEnd_2081988 < baseStart_2081988 := by decide
  rcases family_descends (prefixWord ++ tailWord_2081988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2082005 : List Nat := [1, 3, 2, 4, 1, 2, 2, 3, 4]
def baseStart_2082005 : Nat := 118140960795 + 2082005 * 2 ^ 59
def prefixEnd_2082005 : Nat := 4983230072969 + 3 ^ 40 * 2082005 * 2
def baseEnd_2082005 : Nat := 237570953347607084347231

theorem tailTrace_2082005 : CollatzResearch.WordTrace tailWord_2082005 prefixEnd_2082005 237570953347607084347231 := by
  unfold tailWord_2082005
  simp only [CollatzResearch.WordTrace]
  refine ⟨75936960822258937990087469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50624640548172625326724979 75936960822258937990087469)
  ·
    refine ⟨28476360308347101746282801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75936960822258937990087469 28476360308347101746282801)
    ·
      refine ⟨21357270231260326309712101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28476360308347101746282801 21357270231260326309712101)
      ·
        refine ⟨4004488168361311183071019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21357270231260326309712101 4004488168361311183071019)
        ·
          refine ⟨6006732252541966774606529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4004488168361311183071019 6006732252541966774606529)
          ·
            refine ⟨4505049189406475080954897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6006732252541966774606529 4505049189406475080954897)
            ·
              refine ⟨3378786892054856310716173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4505049189406475080954897 3378786892054856310716173)
              ·
                refine ⟨1267045084520571116518565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3378786892054856310716173 1267045084520571116518565)
                ·
                  refine ⟨237570953347607084347231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1267045084520571116518565 237570953347607084347231)
                  ·
                    rfl

theorem cell22_2082005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 2, 3, 4].length) (baseStart_2082005 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2082005 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2082005 prefixEnd_2082005 := by exact prefixLift 2082005
  have htrace : WordTrace (prefixWord ++ tailWord_2082005) baseStart_2082005 baseEnd_2082005 := by
    simpa [prefixWord, tailWord_2082005, baseEnd_2082005] using wordTrace_append hprefix tailTrace_2082005
  have hstable : (prefixWord ++ tailWord_2082005).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2082005).length < 2 ^ (prefixWord ++ tailWord_2082005).sum := by decide
  have hdescent : baseEnd_2082005 < baseStart_2082005 := by decide
  rcases family_descends (prefixWord ++ tailWord_2082005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2082076 : List Nat := [2, 2, 3, 1, 1, 1, 2, 1, 4, 5]
def baseStart_2082076 : Nat := 118140960795 + 2082076 * 2 ^ 59
def prefixEnd_2082076 : Nat := 4983230072969 + 3 ^ 40 * 2082076 * 2
def baseEnd_2082076 : Nat := 712737164793800734516475

theorem tailTrace_2082076 : CollatzResearch.WordTrace tailWord_2082076 prefixEnd_2082076 712737164793800734516475 := by
  unfold tailWord_2082076
  simp only [CollatzResearch.WordTrace]
  refine ⟨37969775202500858557961041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50626366936667811410614721 37969775202500858557961041)
  ·
    refine ⟨28477331401875643918470781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37969775202500858557961041 28477331401875643918470781)
    ·
      refine ⟨10678999275703366469426543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28477331401875643918470781 10678999275703366469426543)
      ·
        refine ⟨16018498913555049704139815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10678999275703366469426543 16018498913555049704139815)
        ·
          refine ⟨24027748370332574556209723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16018498913555049704139815 24027748370332574556209723)
          ·
            refine ⟨36041622555498861834314585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24027748370332574556209723 36041622555498861834314585)
            ·
              refine ⟨27031216916624146375735939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36041622555498861834314585 27031216916624146375735939)
              ·
                refine ⟨40546825374936219563603909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27031216916624146375735939 40546825374936219563603909)
                ·
                  refine ⟨7602529757800541168175733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40546825374936219563603909 7602529757800541168175733)
                  ·
                    refine ⟨712737164793800734516475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7602529757800541168175733 712737164793800734516475)
                    ·
                      rfl

theorem cell22_2082076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 1, 4, 5].length) (baseStart_2082076 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2082076 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2082076 prefixEnd_2082076 := by exact prefixLift 2082076
  have htrace : WordTrace (prefixWord ++ tailWord_2082076) baseStart_2082076 baseEnd_2082076 := by
    simpa [prefixWord, tailWord_2082076, baseEnd_2082076] using wordTrace_append hprefix tailTrace_2082076
  have hstable : (prefixWord ++ tailWord_2082076).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2082076).length < 2 ^ (prefixWord ++ tailWord_2082076).sum := by decide
  have hdescent : baseEnd_2082076 < baseStart_2082076 := by decide
  rcases family_descends (prefixWord ++ tailWord_2082076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2082082 : List Nat := [3, 3, 1, 1, 4, 2, 1, 1, 3, 3]
def baseStart_2082082 : Nat := 118140960795 + 2082082 * 2 ^ 59
def prefixEnd_2082082 : Nat := 4983230072969 + 3 ^ 40 * 2082082 * 2
def baseEnd_2082082 : Nat := 712739218716418718866457

theorem tailTrace_2082082 : CollatzResearch.WordTrace tailWord_2082082 prefixEnd_2082082 712739218716418718866457 := by
  unfold tailWord_2082082
  simp only [CollatzResearch.WordTrace]
  refine ⟨18984942310744995035160125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50626512828653320093760333 18984942310744995035160125)
  ·
    refine ⟨7119353366529373138185047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18984942310744995035160125 7119353366529373138185047)
    ·
      refine ⟨10679030049794059707277571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7119353366529373138185047 10679030049794059707277571)
      ·
        refine ⟨16018545074691089560916357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10679030049794059707277571 16018545074691089560916357)
        ·
          refine ⟨3003477201504579292671817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16018545074691089560916357 3003477201504579292671817)
          ·
            refine ⟨2252607901128434469503863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3003477201504579292671817 2252607901128434469503863)
            ·
              refine ⟨3378911851692651704255795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2252607901128434469503863 3378911851692651704255795)
              ·
                refine ⟨5068367777538977556383693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3378911851692651704255795 5068367777538977556383693)
                ·
                  refine ⟨1900637916577116583643885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5068367777538977556383693 1900637916577116583643885)
                  ·
                    refine ⟨712739218716418718866457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1900637916577116583643885 712739218716418718866457)
                    ·
                      rfl

theorem cell22_2082082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 1, 1, 3, 3].length) (baseStart_2082082 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2082082 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2082082 prefixEnd_2082082 := by exact prefixLift 2082082
  have htrace : WordTrace (prefixWord ++ tailWord_2082082) baseStart_2082082 baseEnd_2082082 := by
    simpa [prefixWord, tailWord_2082082, baseEnd_2082082] using wordTrace_append hprefix tailTrace_2082082
  have hstable : (prefixWord ++ tailWord_2082082).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2082082).length < 2 ^ (prefixWord ++ tailWord_2082082).sum := by decide
  have hdescent : baseEnd_2082082 < baseStart_2082082 := by decide
  rcases family_descends (prefixWord ++ tailWord_2082082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2082106 : List Nat := [3, 1, 1, 1, 4, 1, 2, 1, 8]
def baseStart_2082106 : Nat := 118140960795 + 2082106 * 2 ^ 59
def prefixEnd_2082106 : Nat := 4983230072969 + 3 ^ 40 * 2082106 * 2
def baseEnd_2082106 : Nat := 237582478135630218755461

theorem tailTrace_2082106 : CollatzResearch.WordTrace tailWord_2082106 prefixEnd_2082106 237582478135630218755461 := by
  unfold tailWord_2082106
  simp only [CollatzResearch.WordTrace]
  refine ⟨18985161148723258059878543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50627096396595354826342781 18985161148723258059878543)
  ·
    refine ⟨28477741723084887089817815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18985161148723258059878543 28477741723084887089817815)
    ·
      refine ⟨42716612584627330634726723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28477741723084887089817815 42716612584627330634726723)
      ·
        refine ⟨64074918876940995952090085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42716612584627330634726723 64074918876940995952090085)
        ·
          refine ⟨12014047289426436741016891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64074918876940995952090085 12014047289426436741016891)
          ·
            refine ⟨18021070934139655111525337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12014047289426436741016891 18021070934139655111525337)
            ·
              refine ⟨13515803200604741333644003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18021070934139655111525337 13515803200604741333644003)
              ·
                refine ⟨20273704800907112000466005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13515803200604741333644003 20273704800907112000466005)
                ·
                  refine ⟨237582478135630218755461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20273704800907112000466005 237582478135630218755461)
                  ·
                    rfl

theorem cell22_2082106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 1, 8].length) (baseStart_2082106 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2082106 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2082106 prefixEnd_2082106 := by exact prefixLift 2082106
  have htrace : WordTrace (prefixWord ++ tailWord_2082106) baseStart_2082106 baseEnd_2082106 := by
    simpa [prefixWord, tailWord_2082106, baseEnd_2082106] using wordTrace_append hprefix tailTrace_2082106
  have hstable : (prefixWord ++ tailWord_2082106).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2082106).length < 2 ^ (prefixWord ++ tailWord_2082106).sum := by decide
  have hdescent : baseEnd_2082106 < baseStart_2082106 := by decide
  rcases family_descends (prefixWord ++ tailWord_2082106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2082108 : List Nat := [2, 2, 2, 2, 1, 4, 1, 1, 3, 4]
def baseStart_2082108 : Nat := 118140960795 + 2082108 * 2 ^ 59
def prefixEnd_2082108 : Nat := 4983230072969 + 3 ^ 40 * 2082108 * 2
def baseEnd_2082108 : Nat := 712748119047763317716377

theorem tailTrace_2082108 : CollatzResearch.WordTrace tailWord_2082108 prefixEnd_2082108 712748119047763317716377 := by
  unfold tailWord_2082108
  simp only [CollatzResearch.WordTrace]
  refine ⟨37970358770442893290543489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50627145027257191054057985 37970358770442893290543489)
  ·
    refine ⟨28477769077832169967907617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37970358770442893290543489 28477769077832169967907617)
    ·
      refine ⟨21358326808374127475930713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28477769077832169967907617 21358326808374127475930713)
      ·
        refine ⟨16018745106280595606948035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21358326808374127475930713 16018745106280595606948035)
        ·
          refine ⟨24028117659420893410422053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16018745106280595606948035 24028117659420893410422053)
          ·
            refine ⟨4505272061141417514454135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24028117659420893410422053 4505272061141417514454135)
            ·
              refine ⟨6757908091712126271681203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4505272061141417514454135 6757908091712126271681203)
              ·
                refine ⟨10136862137568189407521805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6757908091712126271681203 10136862137568189407521805)
                ·
                  refine ⟨3801323301588071027820677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10136862137568189407521805 3801323301588071027820677)
                  ·
                    refine ⟨712748119047763317716377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3801323301588071027820677 712748119047763317716377)
                    ·
                      rfl

theorem cell22_2082108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 1, 1, 3, 4].length) (baseStart_2082108 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2082108 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2082108 prefixEnd_2082108 := by exact prefixLift 2082108
  have htrace : WordTrace (prefixWord ++ tailWord_2082108) baseStart_2082108 baseEnd_2082108 := by
    simpa [prefixWord, tailWord_2082108, baseEnd_2082108] using wordTrace_append hprefix tailTrace_2082108
  have hstable : (prefixWord ++ tailWord_2082108).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2082108).length < 2 ^ (prefixWord ++ tailWord_2082108).sum := by decide
  have hdescent : baseEnd_2082108 < baseStart_2082108 := by decide
  rcases family_descends (prefixWord ++ tailWord_2082108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2082121 : List Nat := [1, 2, 1, 1, 2, 3, 3, 1, 3, 5]
def baseStart_2082121 : Nat := 118140960795 + 2082121 * 2 ^ 59
def prefixEnd_2082121 : Nat := 4983230072969 + 3 ^ 40 * 2082121 * 2
def baseEnd_2082121 : Nat := 712752569213435617141337

theorem tailTrace_2082121 : CollatzResearch.WordTrace tailWord_2082121 prefixEnd_2082121 712752569213435617141337 := by
  unfold tailWord_2082121
  simp only [CollatzResearch.WordTrace]
  refine ⟨75941191689838689801310217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50627461126559126534206811 75941191689838689801310217)
  ·
    refine ⟨56955893767379017350982663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75941191689838689801310217 56955893767379017350982663)
    ·
      refine ⟨85433840651068526026473995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56955893767379017350982663 85433840651068526026473995)
      ·
        refine ⟨128150760976602789039710993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85433840651068526026473995 128150760976602789039710993)
        ·
          refine ⟨96113070732452091779783245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128150760976602789039710993 96113070732452091779783245)
          ·
            refine ⟨36042401524669534417418717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96113070732452091779783245 36042401524669534417418717)
            ·
              refine ⟨13515900571751075406532019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36042401524669534417418717 13515900571751075406532019)
              ·
                refine ⟨20273850857626613109798029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13515900571751075406532019 20273850857626613109798029)
                ·
                  refine ⟨7602694071609979916174261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20273850857626613109798029 7602694071609979916174261)
                  ·
                    refine ⟨712752569213435617141337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7602694071609979916174261 712752569213435617141337)
                    ·
                      rfl

theorem cell22_2082121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 1, 3, 5].length) (baseStart_2082121 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2082121 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2082121 prefixEnd_2082121 := by exact prefixLift 2082121
  have htrace : WordTrace (prefixWord ++ tailWord_2082121) baseStart_2082121 baseEnd_2082121 := by
    simpa [prefixWord, tailWord_2082121, baseEnd_2082121] using wordTrace_append hprefix tailTrace_2082121
  have hstable : (prefixWord ++ tailWord_2082121).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2082121).length < 2 ^ (prefixWord ++ tailWord_2082121).sum := by decide
  have hdescent : baseEnd_2082121 < baseStart_2082121 := by decide
  rcases family_descends (prefixWord ++ tailWord_2082121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2082138 : List Nat := [3, 1, 1, 2, 1, 2, 2, 3, 4, 3]
def baseStart_2082138 : Nat := 118140960795 + 2082138 * 2 ^ 59
def prefixEnd_2082138 : Nat := 4983230072969 + 3 ^ 40 * 2082138 * 2
def baseEnd_2082138 : Nat := 712758388660853239466285

theorem tailTrace_2082138 : CollatzResearch.WordTrace tailWord_2082138 prefixEnd_2082138 712758388660853239466285 := by
  unfold tailWord_2082138
  simp only [CollatzResearch.WordTrace]
  refine ⟨18985452932694275426169767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50627874487184734469786045 18985452932694275426169767)
  ·
    refine ⟨28478179399041413139254651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18985452932694275426169767 28478179399041413139254651)
    ·
      refine ⟨42717269098562119708881977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28478179399041413139254651 42717269098562119708881977)
      ·
        refine ⟨32037951823921589781661483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42717269098562119708881977 32037951823921589781661483)
        ·
          refine ⟨48056927735882384672492225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32037951823921589781661483 48056927735882384672492225)
          ·
            refine ⟨36042695801911788504369169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48056927735882384672492225 36042695801911788504369169)
            ·
              refine ⟨27032021851433841378276877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36042695801911788504369169 27032021851433841378276877)
              ·
                refine ⟨10137008194287690516853829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27032021851433841378276877 10137008194287690516853829)
                ·
                  refine ⟨1900689036428941971910093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10137008194287690516853829 1900689036428941971910093)
                  ·
                    refine ⟨712758388660853239466285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1900689036428941971910093 712758388660853239466285)
                    ·
                      rfl

theorem cell22_2082138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 3, 4, 3].length) (baseStart_2082138 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2082138 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2082138 prefixEnd_2082138 := by exact prefixLift 2082138
  have htrace : WordTrace (prefixWord ++ tailWord_2082138) baseStart_2082138 baseEnd_2082138 := by
    simpa [prefixWord, tailWord_2082138, baseEnd_2082138] using wordTrace_append hprefix tailTrace_2082138
  have hstable : (prefixWord ++ tailWord_2082138).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2082138).length < 2 ^ (prefixWord ++ tailWord_2082138).sum := by decide
  have hdescent : baseEnd_2082138 < baseStart_2082138 := by decide
  rcases family_descends (prefixWord ++ tailWord_2082138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2082206 : List Nat := [4, 3, 1, 2, 2, 1, 3, 1, 2, 3]
def baseStart_2082206 : Nat := 118140960795 + 2082206 * 2 ^ 59
def prefixEnd_2082206 : Nat := 4983230072969 + 3 ^ 40 * 2082206 * 2
def baseEnd_2082206 : Nat := 712781666450523728766077

theorem tailTrace_2082206 : CollatzResearch.WordTrace tailWord_2082206 prefixEnd_2082206 712781666450523728766077 := by
  unfold tailWord_2082206
  simp only [CollatzResearch.WordTrace]
  refine ⟨9493036486816343664769309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50629527929687166212102981 9493036486816343664769309)
  ·
    refine ⟨3559888682556128874288491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9493036486816343664769309 3559888682556128874288491)
    ·
      refine ⟨5339833023834193311432737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3559888682556128874288491 5339833023834193311432737)
      ·
        refine ⟨4004874767875644983574553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5339833023834193311432737 4004874767875644983574553)
        ·
          refine ⟨3003656075906733737680915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4004874767875644983574553 3003656075906733737680915)
          ·
            refine ⟨4505484113860100606521373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3003656075906733737680915 4505484113860100606521373)
            ·
              refine ⟨1689556542697537727445515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4505484113860100606521373 1689556542697537727445515)
              ·
                refine ⟨2534334814046306591168273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1689556542697537727445515 2534334814046306591168273)
                ·
                  refine ⟨1900751110534729943376205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2534334814046306591168273 1900751110534729943376205)
                  ·
                    refine ⟨712781666450523728766077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1900751110534729943376205 712781666450523728766077)
                    ·
                      rfl

theorem cell22_2082206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 3, 1, 2, 3].length) (baseStart_2082206 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2082206 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2082206 prefixEnd_2082206 := by exact prefixLift 2082206
  have htrace : WordTrace (prefixWord ++ tailWord_2082206) baseStart_2082206 baseEnd_2082206 := by
    simpa [prefixWord, tailWord_2082206, baseEnd_2082206] using wordTrace_append hprefix tailTrace_2082206
  have hstable : (prefixWord ++ tailWord_2082206).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2082206).length < 2 ^ (prefixWord ++ tailWord_2082206).sum := by decide
  have hdescent : baseEnd_2082206 < baseStart_2082206 := by decide
  rcases family_descends (prefixWord ++ tailWord_2082206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2082277 : List Nat := [1, 3, 1, 5, 1, 1, 3, 2, 1, 4]
def baseStart_2082277 : Nat := 118140960795 + 2082277 * 2 ^ 59
def prefixEnd_2082277 : Nat := 4983230072969 + 3 ^ 40 * 2082277 * 2
def baseEnd_2082277 : Nat := 712805971201503210240859

theorem tailTrace_2082277 : CollatzResearch.WordTrace tailWord_2082277 prefixEnd_2082277 712805971201503210240859 := by
  unfold tailWord_2082277
  simp only [CollatzResearch.WordTrace]
  refine ⟨75946881477273528443989085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50631254318182352295992723 75946881477273528443989085)
  ·
    refine ⟨28480080553977573166495907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75946881477273528443989085 28480080553977573166495907)
    ·
      refine ⟨42720120830966359749743861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28480080553977573166495907 42720120830966359749743861)
      ·
        refine ⟨4005011327903096226538487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 42720120830966359749743861 4005011327903096226538487)
        ·
          refine ⟨6007516991854644339807731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4005011327903096226538487 6007516991854644339807731)
          ·
            refine ⟨9011275487781966509711597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6007516991854644339807731 9011275487781966509711597)
            ·
              refine ⟨3379228307918237441141849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9011275487781966509711597 3379228307918237441141849)
              ·
                refine ⟨2534421230938678080856387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3379228307918237441141849 2534421230938678080856387)
                ·
                  refine ⟨3801631846408017121284581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2534421230938678080856387 3801631846408017121284581)
                  ·
                    refine ⟨712805971201503210240859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3801631846408017121284581 712805971201503210240859)
                    ·
                      rfl

theorem cell22_2082277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 3, 2, 1, 4].length) (baseStart_2082277 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2082277 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2082277 prefixEnd_2082277 := by exact prefixLift 2082277
  have htrace : WordTrace (prefixWord ++ tailWord_2082277) baseStart_2082277 baseEnd_2082277 := by
    simpa [prefixWord, tailWord_2082277, baseEnd_2082277] using wordTrace_append hprefix tailTrace_2082277
  have hstable : (prefixWord ++ tailWord_2082277).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2082277).length < 2 ^ (prefixWord ++ tailWord_2082277).sum := by decide
  have hdescent : baseEnd_2082277 < baseStart_2082277 := by decide
  rcases family_descends (prefixWord ++ tailWord_2082277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2082290 : List Nat := [3, 2, 1, 4, 1, 1, 1, 1, 3, 5]
def baseStart_2082290 : Nat := 118140960795 + 2082290 * 2 ^ 59
def prefixEnd_2082290 : Nat := 4983230072969 + 3 ^ 40 * 2082290 * 2
def baseEnd_2082290 : Nat := 712810421367175509665819

theorem tailTrace_2082290 : CollatzResearch.WordTrace tailWord_2082290 prefixEnd_2082290 712810421367175509665819 := by
  unfold tailWord_2082290
  simp only [CollatzResearch.WordTrace]
  refine ⟨18986838906556607916053081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50631570417484287776141549 18986838906556607916053081)
  ·
    refine ⟨14240129179917455937039811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18986838906556607916053081 14240129179917455937039811)
    ·
      refine ⟨21360193769876183905559717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14240129179917455937039811 21360193769876183905559717)
      ·
        refine ⟨4005036331851784482292447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21360193769876183905559717 4005036331851784482292447)
        ·
          refine ⟨6007554497777676723438671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4005036331851784482292447 6007554497777676723438671)
          ·
            refine ⟨9011331746666515085158007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6007554497777676723438671 9011331746666515085158007)
            ·
              refine ⟨13516997619999772627737011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9011331746666515085158007 13516997619999772627737011)
              ·
                refine ⟨20275496429999658941605517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13516997619999772627737011 20275496429999658941605517)
                ·
                  refine ⟨7603311161249872103102069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20275496429999658941605517 7603311161249872103102069)
                  ·
                    refine ⟨712810421367175509665819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7603311161249872103102069 712810421367175509665819)
                    ·
                      rfl

theorem cell22_2082290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 1, 3, 5].length) (baseStart_2082290 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2082290 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2082290 prefixEnd_2082290 := by exact prefixLift 2082290
  have htrace : WordTrace (prefixWord ++ tailWord_2082290) baseStart_2082290 baseEnd_2082290 := by
    simpa [prefixWord, tailWord_2082290, baseEnd_2082290] using wordTrace_append hprefix tailTrace_2082290
  have hstable : (prefixWord ++ tailWord_2082290).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2082290).length < 2 ^ (prefixWord ++ tailWord_2082290).sum := by decide
  have hdescent : baseEnd_2082290 < baseStart_2082290 := by decide
  rcases family_descends (prefixWord ++ tailWord_2082290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2082294 : List Nat := [5, 1, 1, 1, 2, 3, 3, 1, 1, 4]
def baseStart_2082294 : Nat := 118140960795 + 2082294 * 2 ^ 59
def prefixEnd_2082294 : Nat := 4983230072969 + 3 ^ 40 * 2082294 * 2
def baseEnd_2082294 : Nat := 712811790648920832565807

theorem tailTrace_2082294 : CollatzResearch.WordTrace tailWord_2082294 prefixEnd_2082294 712811790648920832565807 := by
  unfold tailWord_2082294
  simp only [CollatzResearch.WordTrace]
  refine ⟨4746718844888246271709871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 50631667678807960231571957 4746718844888246271709871)
  ·
    refine ⟨7120078267332369407564807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4746718844888246271709871 7120078267332369407564807)
    ·
      refine ⟨10680117400998554111347211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7120078267332369407564807 10680117400998554111347211)
      ·
        refine ⟨16020176101497831167020817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10680117400998554111347211 16020176101497831167020817)
        ·
          refine ⟨12015132076123373375265613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16020176101497831167020817 12015132076123373375265613)
          ·
            refine ⟨4505674528546265015724605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12015132076123373375265613 4505674528546265015724605)
            ·
              refine ⟨1689627948204849380896727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4505674528546265015724605 1689627948204849380896727)
              ·
                refine ⟨2534441922307274071345091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1689627948204849380896727 2534441922307274071345091)
                ·
                  refine ⟨3801662883460911107017637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2534441922307274071345091 3801662883460911107017637)
                  ·
                    refine ⟨712811790648920832565807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3801662883460911107017637 712811790648920832565807)
                    ·
                      rfl

theorem cell22_2082294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 3, 1, 1, 4].length) (baseStart_2082294 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2082294 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2082294 prefixEnd_2082294 := by exact prefixLift 2082294
  have htrace : WordTrace (prefixWord ++ tailWord_2082294) baseStart_2082294 baseEnd_2082294 := by
    simpa [prefixWord, tailWord_2082294, baseEnd_2082294] using wordTrace_append hprefix tailTrace_2082294
  have hstable : (prefixWord ++ tailWord_2082294).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2082294).length < 2 ^ (prefixWord ++ tailWord_2082294).sum := by decide
  have hdescent : baseEnd_2082294 < baseStart_2082294 := by decide
  rcases family_descends (prefixWord ++ tailWord_2082294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2082324 : List Nat := [2, 4, 3, 1, 2, 1, 2, 1, 1, 5]
def baseStart_2082324 : Nat := 118140960795 + 2082324 * 2 ^ 59
def prefixEnd_2082324 : Nat := 4983230072969 + 3 ^ 40 * 2082324 * 2
def baseEnd_2082324 : Nat := 712822060262010754315715

theorem tailTrace_2082324 : CollatzResearch.WordTrace tailWord_2082324 prefixEnd_2082324 712822060262010754315715 := by
  unfold tailWord_2082324
  simp only [CollatzResearch.WordTrace]
  refine ⟨37974297854051627735475013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50632397138735503647300017 37974297854051627735475013)
  ·
    refine ⟨7120180847634680200401565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37974297854051627735475013 7120180847634680200401565)
    ·
      refine ⟨2670067817863005075150587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7120180847634680200401565 2670067817863005075150587)
      ·
        refine ⟨4005101726794507612725881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2670067817863005075150587 4005101726794507612725881)
        ·
          refine ⟨3003826295095880709544411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4005101726794507612725881 3003826295095880709544411)
          ·
            refine ⟨4505739442643821064316617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3003826295095880709544411 4505739442643821064316617)
            ·
              refine ⟨3379304581982865798237463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4505739442643821064316617 3379304581982865798237463)
              ·
                refine ⟨5068956872974298697356195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3379304581982865798237463 5068956872974298697356195)
                ·
                  refine ⟨7603435309461448046034293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5068956872974298697356195 7603435309461448046034293)
                  ·
                    refine ⟨712822060262010754315715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7603435309461448046034293 712822060262010754315715)
                    ·
                      rfl

theorem cell22_2082324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_2082324 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2082324 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2082324 prefixEnd_2082324 := by exact prefixLift 2082324
  have htrace : WordTrace (prefixWord ++ tailWord_2082324) baseStart_2082324 baseEnd_2082324 := by
    simpa [prefixWord, tailWord_2082324, baseEnd_2082324] using wordTrace_append hprefix tailTrace_2082324
  have hstable : (prefixWord ++ tailWord_2082324).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2082324).length < 2 ^ (prefixWord ++ tailWord_2082324).sum := by decide
  have hdescent : baseEnd_2082324 < baseStart_2082324 := by decide
  rcases family_descends (prefixWord ++ tailWord_2082324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2082335 : List Nat := [1, 1, 2, 4, 1, 1, 3, 1, 5, 3]
def baseStart_2082335 : Nat := 118140960795 + 2082335 * 2 ^ 59
def prefixEnd_2082335 : Nat := 4983230072969 + 3 ^ 40 * 2082335 * 2
def baseEnd_2082335 : Nat := 712825825786810392290681

theorem tailTrace_2082335 : CollatzResearch.WordTrace tailWord_2082335 prefixEnd_2082335 712825825786810392290681 := by
  unfold tailWord_2082335
  simp only [CollatzResearch.WordTrace]
  refine ⟨75948996911063404349600459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50632664607375602899733639 75948996911063404349600459)
  ·
    refine ⟨113923495366595106524400689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75948996911063404349600459 113923495366595106524400689)
    ·
      refine ⟨85442621524946329893300517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113923495366595106524400689 85442621524946329893300517)
      ·
        refine ⟨16020491535927436854993847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85442621524946329893300517 16020491535927436854993847)
        ·
          refine ⟨24030737303891155282490771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16020491535927436854993847 24030737303891155282490771)
          ·
            refine ⟨36046105955836732923736157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24030737303891155282490771 36046105955836732923736157)
            ·
              refine ⟨13517289733438774846401059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36046105955836732923736157 13517289733438774846401059)
              ·
                refine ⟨20275934600158162269601589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13517289733438774846401059 20275934600158162269601589)
                ·
                  refine ⟨1900868868764827712775149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20275934600158162269601589 1900868868764827712775149)
                  ·
                    refine ⟨712825825786810392290681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1900868868764827712775149 712825825786810392290681)
                    ·
                      rfl

theorem cell22_2082335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 1, 5, 3].length) (baseStart_2082335 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2082335 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2082335 prefixEnd_2082335 := by exact prefixLift 2082335
  have htrace : WordTrace (prefixWord ++ tailWord_2082335) baseStart_2082335 baseEnd_2082335 := by
    simpa [prefixWord, tailWord_2082335, baseEnd_2082335] using wordTrace_append hprefix tailTrace_2082335
  have hstable : (prefixWord ++ tailWord_2082335).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2082335).length < 2 ^ (prefixWord ++ tailWord_2082335).sum := by decide
  have hdescent : baseEnd_2082335 < baseStart_2082335 := by decide
  rcases family_descends (prefixWord ++ tailWord_2082335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2082339 : List Nat := [1, 1, 1, 4, 6, 1, 1, 1, 2, 4]
def baseStart_2082339 : Nat := 118140960795 + 2082339 * 2 ^ 59
def prefixEnd_2082339 : Nat := 4983230072969 + 3 ^ 40 * 2082339 * 2
def baseEnd_2082339 : Nat := 712827195068555715190669

theorem tailTrace_2082339 : CollatzResearch.WordTrace tailWord_2082339 prefixEnd_2082339 712827195068555715190669 := by
  unfold tailWord_2082339
  simp only [CollatzResearch.WordTrace]
  refine ⟨75949142803048913032746071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50632761868699275355164047 75949142803048913032746071)
  ·
    refine ⟨113923714204573369549119107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75949142803048913032746071 113923714204573369549119107)
    ·
      refine ⟨170885571306860054323678661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113923714204573369549119107 170885571306860054323678661)
      ·
        refine ⟨32041044620036260185689749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 170885571306860054323678661 32041044620036260185689749)
        ·
          refine ⟨1501923966564199696204207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 32041044620036260185689749 1501923966564199696204207)
          ·
            refine ⟨2252885949846299544306311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1501923966564199696204207 2252885949846299544306311)
            ·
              refine ⟨3379328924769449316459467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2252885949846299544306311 3379328924769449316459467)
              ·
                refine ⟨5068993387154173974689201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3379328924769449316459467 5068993387154173974689201)
                ·
                  refine ⟨3801745040365630481016901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5068993387154173974689201 3801745040365630481016901)
                  ·
                    refine ⟨712827195068555715190669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3801745040365630481016901 712827195068555715190669)
                    ·
                      rfl

theorem cell22_2082339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 1, 1, 2, 4].length) (baseStart_2082339 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2082339 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2082339 prefixEnd_2082339 := by exact prefixLift 2082339
  have htrace : WordTrace (prefixWord ++ tailWord_2082339) baseStart_2082339 baseEnd_2082339 := by
    simpa [prefixWord, tailWord_2082339, baseEnd_2082339] using wordTrace_append hprefix tailTrace_2082339
  have hstable : (prefixWord ++ tailWord_2082339).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2082339).length < 2 ^ (prefixWord ++ tailWord_2082339).sum := by decide
  have hdescent : baseEnd_2082339 < baseStart_2082339 := by decide
  rcases family_descends (prefixWord ++ tailWord_2082339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2082358 : List Nat := [5, 1, 2, 1, 4, 1, 1, 2, 2, 3]
def baseStart_2082358 : Nat := 118140960795 + 2082358 * 2 ^ 59
def prefixEnd_2082358 : Nat := 4983230072969 + 3 ^ 40 * 2082358 * 2
def baseEnd_2082358 : Nat := 712833699156845998965611

theorem tailTrace_2082358 : CollatzResearch.WordTrace tailWord_2082358 prefixEnd_2082358 712833699156845998965611 := by
  unfold tailWord_2082358
  simp only [CollatzResearch.WordTrace]
  refine ⟨4746864736873754954855483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 50633223859986719518458485 4746864736873754954855483)
  ·
    refine ⟨7120297105310632432283225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4746864736873754954855483 7120297105310632432283225)
    ·
      refine ⟨5340222828982974324212419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7120297105310632432283225 5340222828982974324212419)
      ·
        refine ⟨8010334243474461486318629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5340222828982974324212419 8010334243474461486318629)
        ·
          refine ⟨1501937670651461528684743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8010334243474461486318629 1501937670651461528684743)
          ·
            refine ⟨2252906505977192293027115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1501937670651461528684743 2252906505977192293027115)
            ·
              refine ⟨3379359758965788439540673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2252906505977192293027115 3379359758965788439540673)
              ·
                refine ⟨2534519819224341329655505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3379359758965788439540673 2534519819224341329655505)
                ·
                  refine ⟨1900889864418255997241629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2534519819224341329655505 1900889864418255997241629)
                  ·
                    refine ⟨712833699156845998965611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1900889864418255997241629 712833699156845998965611)
                    ·
                      rfl

theorem cell22_2082358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 1, 2, 2, 3].length) (baseStart_2082358 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2082358 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2082358 prefixEnd_2082358 := by exact prefixLift 2082358
  have htrace : WordTrace (prefixWord ++ tailWord_2082358) baseStart_2082358 baseEnd_2082358 := by
    simpa [prefixWord, tailWord_2082358, baseEnd_2082358] using wordTrace_append hprefix tailTrace_2082358
  have hstable : (prefixWord ++ tailWord_2082358).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2082358).length < 2 ^ (prefixWord ++ tailWord_2082358).sum := by decide
  have hdescent : baseEnd_2082358 < baseStart_2082358 := by decide
  rcases family_descends (prefixWord ++ tailWord_2082358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2082369 : List Nat := [1, 2, 5, 1, 1, 1, 1, 6, 1, 3]
def baseStart_2082369 : Nat := 118140960795 + 2082369 * 2 ^ 59
def prefixEnd_2082369 : Nat := 4983230072969 + 3 ^ 40 * 2082369 * 2
def baseEnd_2082369 : Nat := 712837464681645636940577

theorem tailTrace_2082369 : CollatzResearch.WordTrace tailWord_2082369 prefixEnd_2082369 712837464681645636940577 := by
  unfold tailWord_2082369
  simp only [CollatzResearch.WordTrace]
  refine ⟨75950236992940228156338161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50633491328626818770892107 75950236992940228156338161)
  ·
    refine ⟨56962677744705171117253621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75950236992940228156338161 56962677744705171117253621)
    ·
      refine ⟨5340251038566109792242527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 56962677744705171117253621 5340251038566109792242527)
      ·
        refine ⟨8010376557849164688363791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5340251038566109792242527 8010376557849164688363791)
        ·
          refine ⟨12015564836773747032545687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8010376557849164688363791 12015564836773747032545687)
          ·
            refine ⟨18023347255160620548818531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12015564836773747032545687 18023347255160620548818531)
            ·
              refine ⟨27035020882740930823227797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18023347255160620548818531 27035020882740930823227797)
              ·
                refine ⟨1267266603878481132338803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 27035020882740930823227797 1267266603878481132338803)
                ·
                  refine ⟨1900899905817721698508205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1267266603878481132338803 1900899905817721698508205)
                  ·
                    refine ⟨712837464681645636940577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1900899905817721698508205 712837464681645636940577)
                    ·
                      rfl

theorem cell22_2082369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 6, 1, 3].length) (baseStart_2082369 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2082369 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2082369 prefixEnd_2082369 := by exact prefixLift 2082369
  have htrace : WordTrace (prefixWord ++ tailWord_2082369) baseStart_2082369 baseEnd_2082369 := by
    simpa [prefixWord, tailWord_2082369, baseEnd_2082369] using wordTrace_append hprefix tailTrace_2082369
  have hstable : (prefixWord ++ tailWord_2082369).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2082369).length < 2 ^ (prefixWord ++ tailWord_2082369).sum := by decide
  have hdescent : baseEnd_2082369 < baseStart_2082369 := by decide
  rcases family_descends (prefixWord ++ tailWord_2082369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2082380 : List Nat := [2, 2, 1, 3, 1, 3, 2, 1, 2, 5]
def baseStart_2082380 : Nat := 118140960795 + 2082380 * 2 ^ 59
def prefixEnd_2082380 : Nat := 4983230072969 + 3 ^ 40 * 2082380 * 2
def baseEnd_2082380 : Nat := 712841230206445274915543

theorem tailTrace_2082380 : CollatzResearch.WordTrace tailWord_2082380 prefixEnd_2082380 712841230206445274915543 := by
  unfold tailWord_2082380
  simp only [CollatzResearch.WordTrace]
  refine ⟨37975319097950188517494297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50633758797266918023325729 37975319097950188517494297)
  ·
    refine ⟨28481489323462641388120723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37975319097950188517494297 28481489323462641388120723)
    ·
      refine ⟨42722233985193962082181085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28481489323462641388120723 42722233985193962082181085)
      ·
        refine ⟨16020837744447735780817907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42722233985193962082181085 16020837744447735780817907)
        ·
          refine ⟨24031256616671603671226861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16020837744447735780817907 24031256616671603671226861)
          ·
            refine ⟨9011721231251851376710073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24031256616671603671226861 9011721231251851376710073)
            ·
              refine ⟨6758790923438888532532555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9011721231251851376710073 6758790923438888532532555)
              ·
                refine ⟨10138186385158332798798833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6758790923438888532532555 10138186385158332798798833)
                ·
                  refine ⟨7603639788868749599099125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10138186385158332798798833 7603639788868749599099125)
                  ·
                    refine ⟨712841230206445274915543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7603639788868749599099125 712841230206445274915543)
                    ·
                      rfl

theorem cell22_2082380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2, 1, 2, 5].length) (baseStart_2082380 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2082380 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2082380 prefixEnd_2082380 := by exact prefixLift 2082380
  have htrace : WordTrace (prefixWord ++ tailWord_2082380) baseStart_2082380 baseEnd_2082380 := by
    simpa [prefixWord, tailWord_2082380, baseEnd_2082380] using wordTrace_append hprefix tailTrace_2082380
  have hstable : (prefixWord ++ tailWord_2082380).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2082380).length < 2 ^ (prefixWord ++ tailWord_2082380).sum := by decide
  have hdescent : baseEnd_2082380 < baseStart_2082380 := by decide
  rcases family_descends (prefixWord ++ tailWord_2082380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2082455 : List Nat := [1, 1, 3, 3, 2, 2, 2, 8]
def baseStart_2082455 : Nat := 118140960795 + 2082455 * 2 ^ 59
def prefixEnd_2082455 : Nat := 4983230072969 + 3 ^ 40 * 2082455 * 2
def baseEnd_2082455 : Nat := 79207433804352231032257

theorem tailTrace_2082455 : CollatzResearch.WordTrace tailWord_2082455 prefixEnd_2082455 79207433804352231032257 := by
  unfold tailWord_2082455
  simp only [CollatzResearch.WordTrace]
  refine ⟨75953373670628664843968819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50635582447085776562645879 75953373670628664843968819)
  ·
    refine ⟨113930060505942997265953229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75953373670628664843968819 113930060505942997265953229)
    ·
      refine ⟨42723772689728623974732461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113930060505942997265953229 42723772689728623974732461)
      ·
        refine ⟨16021414758648233990524673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42723772689728623974732461 16021414758648233990524673)
        ·
          refine ⟨12016061068986175492893505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16021414758648233990524673 12016061068986175492893505)
          ·
            refine ⟨9012045801739631619670129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12016061068986175492893505 9012045801739631619670129)
            ·
              refine ⟨6759034351304723714752597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9012045801739631619670129 6759034351304723714752597)
              ·
                refine ⟨79207433804352231032257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6759034351304723714752597 79207433804352231032257)
                ·
                  rfl

theorem cell22_2082455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2, 8].length) (baseStart_2082455 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2082455 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2082455 prefixEnd_2082455 := by exact prefixLift 2082455
  have htrace : WordTrace (prefixWord ++ tailWord_2082455) baseStart_2082455 baseEnd_2082455 := by
    simpa [prefixWord, tailWord_2082455, baseEnd_2082455] using wordTrace_append hprefix tailTrace_2082455
  have hstable : (prefixWord ++ tailWord_2082455).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2082455).length < 2 ^ (prefixWord ++ tailWord_2082455).sum := by decide
  have hdescent : baseEnd_2082455 < baseStart_2082455 := by decide
  rcases family_descends (prefixWord ++ tailWord_2082455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2082521 : List Nat := [1, 2, 1, 2, 3, 4, 2, 3, 1, 3]
def baseStart_2082521 : Nat := 118140960795 + 2082521 * 2 ^ 59
def prefixEnd_2082521 : Nat := 4983230072969 + 3 ^ 40 * 2082521 * 2
def baseEnd_2082521 : Nat := 712889497387967907140111

theorem tailTrace_2082521 : CollatzResearch.WordTrace tailWord_2082521 prefixEnd_2082521 712889497387967907140111 := by
  unfold tailWord_2082521
  simp only [CollatzResearch.WordTrace]
  refine ⟨75955780888389558115871417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50637187258926372077247611 75955780888389558115871417)
  ·
    refine ⟨56966835666292168586903563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75955780888389558115871417 56966835666292168586903563)
    ·
      refine ⟨85450253499438252880355345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56966835666292168586903563 85450253499438252880355345)
      ·
        refine ⟨64087690124578689660266509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85450253499438252880355345 64087690124578689660266509)
        ·
          refine ⟨24032883796717008622599941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64087690124578689660266509 24032883796717008622599941)
          ·
            refine ⟨4506165711884439116737489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24032883796717008622599941 4506165711884439116737489)
            ·
              refine ⟨3379624283913329337553117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4506165711884439116737489 3379624283913329337553117)
              ·
                refine ⟨1267359106467498501582419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3379624283913329337553117 1267359106467498501582419)
                ·
                  refine ⟨1901038659701247752373629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1267359106467498501582419 1901038659701247752373629)
                  ·
                    refine ⟨712889497387967907140111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1901038659701247752373629 712889497387967907140111)
                    ·
                      rfl

theorem cell22_2082521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 2, 3, 1, 3].length) (baseStart_2082521 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2082521 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2082521 prefixEnd_2082521 := by exact prefixLift 2082521
  have htrace : WordTrace (prefixWord ++ tailWord_2082521) baseStart_2082521 baseEnd_2082521 := by
    simpa [prefixWord, tailWord_2082521, baseEnd_2082521] using wordTrace_append hprefix tailTrace_2082521
  have hstable : (prefixWord ++ tailWord_2082521).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2082521).length < 2 ^ (prefixWord ++ tailWord_2082521).sum := by decide
  have hdescent : baseEnd_2082521 < baseStart_2082521 := by decide
  rcases family_descends (prefixWord ++ tailWord_2082521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2082564 : List Nat := [2, 3, 2, 2, 1, 2, 1, 4, 1, 4]
def baseStart_2082564 : Nat := 118140960795 + 2082564 * 2 ^ 59
def prefixEnd_2082564 : Nat := 4983230072969 + 3 ^ 40 * 2082564 * 2
def baseEnd_2082564 : Nat := 712904217166730128314979

theorem tailTrace_2082564 : CollatzResearch.WordTrace tailWord_2082564 prefixEnd_2082564 712904217166730128314979 := by
  unfold tailWord_2082564
  simp only [CollatzResearch.WordTrace]
  refine ⟨37978674613616888229843373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50638232818155850973124497 37978674613616888229843373)
  ·
    refine ⟨14242002980106333086191265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37978674613616888229843373 14242002980106333086191265)
    ·
      refine ⟨10681502235079749814643449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14242002980106333086191265 10681502235079749814643449)
      ·
        refine ⟨8011126676309812360982587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10681502235079749814643449 8011126676309812360982587)
        ·
          refine ⟨12016690014464718541473881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8011126676309812360982587 12016690014464718541473881)
          ·
            refine ⟨9012517510848538906105411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12016690014464718541473881 9012517510848538906105411)
            ·
              refine ⟨13518776266272808359158117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9012517510848538906105411 13518776266272808359158117)
              ·
                refine ⟨2534770549926151567342147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13518776266272808359158117 2534770549926151567342147)
                ·
                  refine ⟨3802155824889227351013221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2534770549926151567342147 3802155824889227351013221)
                  ·
                    refine ⟨712904217166730128314979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3802155824889227351013221 712904217166730128314979)
                    ·
                      rfl

theorem cell22_2082564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 4, 1, 4].length) (baseStart_2082564 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2082564 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2082564 prefixEnd_2082564 := by exact prefixLift 2082564
  have htrace : WordTrace (prefixWord ++ tailWord_2082564) baseStart_2082564 baseEnd_2082564 := by
    simpa [prefixWord, tailWord_2082564, baseEnd_2082564] using wordTrace_append hprefix tailTrace_2082564
  have hstable : (prefixWord ++ tailWord_2082564).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2082564).length < 2 ^ (prefixWord ++ tailWord_2082564).sum := by decide
  have hdescent : baseEnd_2082564 < baseStart_2082564 := by decide
  rcases family_descends (prefixWord ++ tailWord_2082564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2082594 : List Nat := [3, 3, 1, 1, 2, 1, 1, 3, 4, 3]
def baseStart_2082594 : Nat := 118140960795 + 2082594 * 2 ^ 59
def prefixEnd_2082594 : Nat := 4983230072969 + 3 ^ 40 * 2082594 * 2
def baseEnd_2082594 : Nat := 712914486779820050064887

theorem tailTrace_2082594 : CollatzResearch.WordTrace tailWord_2082594 prefixEnd_2082594 712914486779820050064887 := by
  unfold tailWord_2082594
  simp only [CollatzResearch.WordTrace]
  refine ⟨18989610854281272895819709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50638962278083394388852557 18989610854281272895819709)
  ·
    refine ⟨7121104070355477335932391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18989610854281272895819709 7121104070355477335932391)
    ·
      refine ⟨10681656105533216003898587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7121104070355477335932391 10681656105533216003898587)
      ·
        refine ⟨16022484158299824005847881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10681656105533216003898587 16022484158299824005847881)
        ·
          refine ⟨12016863118724868004385911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16022484158299824005847881 12016863118724868004385911)
          ·
            refine ⟨18025294678087302006578867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12016863118724868004385911 18025294678087302006578867)
            ·
              refine ⟨27037942017130953009868301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18025294678087302006578867 27037942017130953009868301)
              ·
                refine ⟨10139228256424107378700613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27037942017130953009868301 10139228256424107378700613)
                ·
                  refine ⟨1901105298079520133506365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10139228256424107378700613 1901105298079520133506365)
                  ·
                    refine ⟨712914486779820050064887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1901105298079520133506365 712914486779820050064887)
                    ·
                      rfl

theorem cell22_2082594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 3, 4, 3].length) (baseStart_2082594 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2082594 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2082594 prefixEnd_2082594 := by exact prefixLift 2082594
  have htrace : WordTrace (prefixWord ++ tailWord_2082594) baseStart_2082594 baseEnd_2082594 := by
    simpa [prefixWord, tailWord_2082594, baseEnd_2082594] using wordTrace_append hprefix tailTrace_2082594
  have hstable : (prefixWord ++ tailWord_2082594).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2082594).length < 2 ^ (prefixWord ++ tailWord_2082594).sum := by decide
  have hdescent : baseEnd_2082594 < baseStart_2082594 := by decide
  rcases family_descends (prefixWord ++ tailWord_2082594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2082611 : List Nat := [1, 1, 1, 2, 7, 1, 1, 3, 2, 3]
def baseStart_2082611 : Nat := 118140960795 + 2082611 * 2 ^ 59
def prefixEnd_2082611 : Nat := 4983230072969 + 3 ^ 40 * 2082611 * 2
def baseEnd_2082611 : Nat := 712920306227237672389835

theorem tailTrace_2082611 : CollatzResearch.WordTrace tailWord_2082611 prefixEnd_2082611 712920306227237672389835 := by
  unfold tailWord_2082611
  simp only [CollatzResearch.WordTrace]
  refine ⟨75959063458063503486647687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50639375638709002324431791 75959063458063503486647687)
  ·
    refine ⟨113938595187095255229971531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75959063458063503486647687 113938595187095255229971531)
    ·
      refine ⟨170907892780642882844957297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113938595187095255229971531 170907892780642882844957297)
      ·
        refine ⟨128180919585482162133717973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170907892780642882844957297 128180919585482162133717973)
        ·
          refine ⟨3004240302784738175009015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 128180919585482162133717973 3004240302784738175009015)
          ·
            refine ⟨4506360454177107262513523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3004240302784738175009015 4506360454177107262513523)
            ·
              refine ⟨6759540681265660893770285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4506360454177107262513523 6759540681265660893770285)
              ·
                refine ⟨2534827755474622835163857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6759540681265660893770285 2534827755474622835163857)
                ·
                  refine ⟨1901120816605967126372893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2534827755474622835163857 1901120816605967126372893)
                  ·
                    refine ⟨712920306227237672389835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1901120816605967126372893 712920306227237672389835)
                    ·
                      rfl

theorem cell22_2082611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 1, 3, 2, 3].length) (baseStart_2082611 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2082611 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2082611 prefixEnd_2082611 := by exact prefixLift 2082611
  have htrace : WordTrace (prefixWord ++ tailWord_2082611) baseStart_2082611 baseEnd_2082611 := by
    simpa [prefixWord, tailWord_2082611, baseEnd_2082611] using wordTrace_append hprefix tailTrace_2082611
  have hstable : (prefixWord ++ tailWord_2082611).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2082611).length < 2 ^ (prefixWord ++ tailWord_2082611).sum := by decide
  have hdescent : baseEnd_2082611 < baseStart_2082611 := by decide
  rcases family_descends (prefixWord ++ tailWord_2082611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2082669 : List Nat := [1, 5, 1, 1, 1, 1, 4, 3, 5]
def baseStart_2082669 : Nat := 118140960795 + 2082669 * 2 ^ 59
def prefixEnd_2082669 : Nat := 4983230072969 + 3 ^ 40 * 2082669 * 2
def baseEnd_2082669 : Nat := 237646720270848284813219

theorem tailTrace_2082669 : CollatzResearch.WordTrace tailWord_2082669 prefixEnd_2082669 237646720270848284813219 := by
  unfold tailWord_2082669
  simp only [CollatzResearch.WordTrace]
  refine ⟨75961178891853379392259061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50640785927902252928172707 75961178891853379392259061)
  ·
    refine ⟨7121360521111254318024287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 75961178891853379392259061 7121360521111254318024287)
    ·
      refine ⟨10682040781666881477036431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7121360521111254318024287 10682040781666881477036431)
      ·
        refine ⟨16023061172500322215554647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10682040781666881477036431 16023061172500322215554647)
        ·
          refine ⟨24034591758750483323331971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16023061172500322215554647 24034591758750483323331971)
          ·
            refine ⟨36051887638125724984997957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24034591758750483323331971 36051887638125724984997957)
            ·
              refine ⟨6759728932148573434687117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36051887638125724984997957 6759728932148573434687117)
              ·
                refine ⟨2534898349555715038007669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6759728932148573434687117 2534898349555715038007669)
                ·
                  refine ⟨237646720270848284813219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2534898349555715038007669 237646720270848284813219)
                  ·
                    rfl

theorem cell22_2082669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 4, 3, 5].length) (baseStart_2082669 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2082669 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2082669 prefixEnd_2082669 := by exact prefixLift 2082669
  have htrace : WordTrace (prefixWord ++ tailWord_2082669) baseStart_2082669 baseEnd_2082669 := by
    simpa [prefixWord, tailWord_2082669, baseEnd_2082669] using wordTrace_append hprefix tailTrace_2082669
  have hstable : (prefixWord ++ tailWord_2082669).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2082669).length < 2 ^ (prefixWord ++ tailWord_2082669).sum := by decide
  have hdescent : baseEnd_2082669 < baseStart_2082669 := by decide
  rcases family_descends (prefixWord ++ tailWord_2082669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2082697 : List Nat := [1, 2, 1, 1, 5, 1, 1, 2, 8]
def baseStart_2082697 : Nat := 118140960795 + 2082697 * 2 ^ 59
def prefixEnd_2082697 : Nat := 4983230072969 + 3 ^ 40 * 2082697 * 2
def baseEnd_2082697 : Nat := 237649915261587371579857

theorem tailTrace_2082697 : CollatzResearch.WordTrace tailWord_2082697 prefixEnd_2082697 237649915261587371579857 := by
  unfold tailWord_2082697
  simp only [CollatzResearch.WordTrace]
  refine ⟨75962200135751940174278345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50641466757167960116185563 75962200135751940174278345)
  ·
    refine ⟨56971650101813955130708759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75962200135751940174278345 56971650101813955130708759)
    ·
      refine ⟨85457475152720932696063139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56971650101813955130708759 85457475152720932696063139)
      ·
        refine ⟨128186212729081399044094709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85457475152720932696063139 128186212729081399044094709)
        ·
          refine ⟨12017457443351381160383879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 128186212729081399044094709 12017457443351381160383879)
          ·
            refine ⟨18026186165027071740575819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12017457443351381160383879 18026186165027071740575819)
            ·
              refine ⟨27039279247540607610863729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18026186165027071740575819 27039279247540607610863729)
              ·
                refine ⟨20279459435655455708147797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27039279247540607610863729 20279459435655455708147797)
                ·
                  refine ⟨237649915261587371579857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20279459435655455708147797 237649915261587371579857)
                  ·
                    rfl

theorem cell22_2082697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 2, 8].length) (baseStart_2082697 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2082697 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2082697 prefixEnd_2082697 := by exact prefixLift 2082697
  have htrace : WordTrace (prefixWord ++ tailWord_2082697) baseStart_2082697 baseEnd_2082697 := by
    simpa [prefixWord, tailWord_2082697, baseEnd_2082697] using wordTrace_append hprefix tailTrace_2082697
  have hstable : (prefixWord ++ tailWord_2082697).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2082697).length < 2 ^ (prefixWord ++ tailWord_2082697).sum := by decide
  have hdescent : baseEnd_2082697 < baseStart_2082697 := by decide
  rcases family_descends (prefixWord ++ tailWord_2082697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2082714 : List Nat := [3, 1, 1, 4, 2, 1, 1, 3, 6]
def baseStart_2082714 : Nat := 118140960795 + 2082714 * 2 ^ 59
def prefixEnd_2082714 : Nat := 4983230072969 + 3 ^ 40 * 2082714 * 2
def baseEnd_2082714 : Nat := 237651855077393245688173

theorem tailTrace_2082714 : CollatzResearch.WordTrace tailWord_2082714 prefixEnd_2082714 237651855077393245688173 := by
  unfold tailWord_2082714
  simp only [CollatzResearch.WordTrace]
  refine ⟨18990705044172588019411799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50641880117793568051764797 18990705044172588019411799)
  ·
    refine ⟨28486057566258882029117699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18990705044172588019411799 28486057566258882029117699)
    ·
      refine ⟨42729086349388323043676549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28486057566258882029117699 42729086349388323043676549)
      ·
        refine ⟨8011703690510310570689353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42729086349388323043676549 8011703690510310570689353)
        ·
          refine ⟨6008777767882732928017015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8011703690510310570689353 6008777767882732928017015)
          ·
            refine ⟨9013166651824099392025523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6008777767882732928017015 9013166651824099392025523)
            ·
              refine ⟨13519749977736149088038285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9013166651824099392025523 13519749977736149088038285)
              ·
                refine ⟨5069906241651055908014357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13519749977736149088038285 5069906241651055908014357)
                ·
                  refine ⟨237651855077393245688173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5069906241651055908014357 237651855077393245688173)
                  ·
                    rfl

theorem cell22_2082714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 3, 6].length) (baseStart_2082714 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2082714 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2082714 prefixEnd_2082714 := by exact prefixLift 2082714
  have htrace : WordTrace (prefixWord ++ tailWord_2082714) baseStart_2082714 baseEnd_2082714 := by
    simpa [prefixWord, tailWord_2082714, baseEnd_2082714] using wordTrace_append hprefix tailTrace_2082714
  have hstable : (prefixWord ++ tailWord_2082714).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2082714).length < 2 ^ (prefixWord ++ tailWord_2082714).sum := by decide
  have hdescent : baseEnd_2082714 < baseStart_2082714 := by decide
  rcases family_descends (prefixWord ++ tailWord_2082714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2082744 : List Nat := [2, 1, 2, 1, 2, 3, 2, 3, 2, 4]
def baseStart_2082744 : Nat := 118140960795 + 2082744 * 2 ^ 59
def prefixEnd_2082744 : Nat := 4983230072969 + 3 ^ 40 * 2082744 * 2
def baseEnd_2082744 : Nat := 712965834845269658814427

theorem tailTrace_2082744 : CollatzResearch.WordTrace tailWord_2082744 prefixEnd_2082744 712965834845269658814427 := by
  unfold tailWord_2082744
  simp only [CollatzResearch.WordTrace]
  refine ⟨37981957183290833600619643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50642609577721111467492857 37981957183290833600619643)
  ·
    refine ⟨56972935774936250400929465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37981957183290833600619643 56972935774936250400929465)
    ·
      refine ⟨42729701831202187800697099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56972935774936250400929465 42729701831202187800697099)
      ·
        refine ⟨64094552746803281701045649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42729701831202187800697099 64094552746803281701045649)
        ·
          refine ⟨48070914560102461275784237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64094552746803281701045649 48070914560102461275784237)
          ·
            refine ⟨18026592960038422978419089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48070914560102461275784237 18026592960038422978419089)
            ·
              refine ⟨13519944720028817233814317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18026592960038422978419089 13519944720028817233814317)
              ·
                refine ⟨5069979270010806462680369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13519944720028817233814317 5069979270010806462680369)
                ·
                  refine ⟨3802484452508104847010277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5069979270010806462680369 3802484452508104847010277)
                  ·
                    refine ⟨712965834845269658814427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3802484452508104847010277 712965834845269658814427)
                    ·
                      rfl

theorem cell22_2082744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 3, 2, 4].length) (baseStart_2082744 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2082744 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2082744 prefixEnd_2082744 := by exact prefixLift 2082744
  have htrace : WordTrace (prefixWord ++ tailWord_2082744) baseStart_2082744 baseEnd_2082744 := by
    simpa [prefixWord, tailWord_2082744, baseEnd_2082744] using wordTrace_append hprefix tailTrace_2082744
  have hstable : (prefixWord ++ tailWord_2082744).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2082744).length < 2 ^ (prefixWord ++ tailWord_2082744).sum := by decide
  have hdescent : baseEnd_2082744 < baseStart_2082744 := by decide
  rcases family_descends (prefixWord ++ tailWord_2082744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2082821 : List Nat := [1, 3, 1, 1, 2, 5, 2, 2, 5]
def baseStart_2082821 : Nat := 118140960795 + 2082821 * 2 ^ 59
def prefixEnd_2082821 : Nat := 4983230072969 + 3 ^ 40 * 2082821 * 2
def baseEnd_2082821 : Nat := 237664064506289041546397

theorem tailTrace_2082821 : CollatzResearch.WordTrace tailWord_2082821 prefixEnd_2082821 237664064506289041546397 := by
  unfold tailWord_2082821
  simp only [CollatzResearch.WordTrace]
  refine ⟨75966722787302709351792317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50644481858201806234528211 75966722787302709351792317)
  ·
    refine ⟨28487521045238516006922119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75966722787302709351792317 28487521045238516006922119)
    ·
      refine ⟨42731281567857774010383179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28487521045238516006922119 42731281567857774010383179)
      ·
        refine ⟨64096922351786661015574769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42731281567857774010383179 64096922351786661015574769)
        ·
          refine ⟨48072691763839995761681077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64096922351786661015574769 48072691763839995761681077)
          ·
            refine ⟨4506814852859999602657601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 48072691763839995761681077 4506814852859999602657601)
            ·
              refine ⟨3380111139644999701993201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4506814852859999602657601 3380111139644999701993201)
              ·
                refine ⟨2535083354733749776494901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3380111139644999701993201 2535083354733749776494901)
                ·
                  refine ⟨237664064506289041546397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2535083354733749776494901 237664064506289041546397)
                  ·
                    rfl

theorem cell22_2082821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 2, 2, 5].length) (baseStart_2082821 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2082821 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2082821 prefixEnd_2082821 := by exact prefixLift 2082821
  have htrace : WordTrace (prefixWord ++ tailWord_2082821) baseStart_2082821 baseEnd_2082821 := by
    simpa [prefixWord, tailWord_2082821, baseEnd_2082821] using wordTrace_append hprefix tailTrace_2082821
  have hstable : (prefixWord ++ tailWord_2082821).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2082821).length < 2 ^ (prefixWord ++ tailWord_2082821).sum := by decide
  have hdescent : baseEnd_2082821 < baseStart_2082821 := by decide
  rcases family_descends (prefixWord ++ tailWord_2082821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2082851 : List Nat := [1, 1, 1, 4, 3, 1, 2, 4, 1, 4]
def baseStart_2082851 : Nat := 118140960795 + 2082851 * 2 ^ 59
def prefixEnd_2082851 : Nat := 4983230072969 + 3 ^ 40 * 2082851 * 2
def baseEnd_2082851 : Nat := 713002463131957046389099

theorem tailTrace_2082851 : CollatzResearch.WordTrace tailWord_2082851 prefixEnd_2082851 713002463131957046389099 := by
  unfold tailWord_2082851
  simp only [CollatzResearch.WordTrace]
  refine ⟨75967816977194024475384407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50645211318129349650256271 75967816977194024475384407)
  ·
    refine ⟨113951725465791036713076611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75967816977194024475384407 113951725465791036713076611)
    ·
      refine ⟨170927588198686555069614917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113951725465791036713076611 170927588198686555069614917)
      ·
        refine ⟨32048922787253729075552797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 170927588198686555069614917 32048922787253729075552797)
        ·
          refine ⟨12018346045220148403332299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32048922787253729075552797 12018346045220148403332299)
          ·
            refine ⟨18027519067830222604998449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12018346045220148403332299 18027519067830222604998449)
            ·
              refine ⟨13520639300872666953748837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18027519067830222604998449 13520639300872666953748837)
              ·
                refine ⟨2535119868913625053827907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13520639300872666953748837 2535119868913625053827907)
                ·
                  refine ⟨3802679803370437580741861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2535119868913625053827907 3802679803370437580741861)
                  ·
                    refine ⟨713002463131957046389099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3802679803370437580741861 713002463131957046389099)
                    ·
                      rfl

theorem cell22_2082851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 4, 1, 4].length) (baseStart_2082851 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2082851 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2082851 prefixEnd_2082851 := by exact prefixLift 2082851
  have htrace : WordTrace (prefixWord ++ tailWord_2082851) baseStart_2082851 baseEnd_2082851 := by
    simpa [prefixWord, tailWord_2082851, baseEnd_2082851] using wordTrace_append hprefix tailTrace_2082851
  have hstable : (prefixWord ++ tailWord_2082851).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2082851).length < 2 ^ (prefixWord ++ tailWord_2082851).sum := by decide
  have hdescent : baseEnd_2082851 < baseStart_2082851 := by decide
  rcases family_descends (prefixWord ++ tailWord_2082851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2082902 : List Nat := [5, 2, 2, 1, 1, 2, 2, 2, 1, 4]
def baseStart_2082902 : Nat := 118140960795 + 2082902 * 2 ^ 59
def prefixEnd_2082902 : Nat := 4983230072969 + 3 ^ 40 * 2082902 * 2
def baseEnd_2082902 : Nat := 713019921474209913363943

theorem tailTrace_2082902 : CollatzResearch.WordTrace tailWord_2082902 prefixEnd_2082902 713019921474209913363943 := by
  unfold tailWord_2082902
  simp only [CollatzResearch.WordTrace]
  refine ⟨4748104818750578761593185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 50646451400006173456993973 4748104818750578761593185)
  ·
    refine ⟨3561078614062934071194889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4748104818750578761593185 3561078614062934071194889)
    ·
      refine ⟨2670808960547200553396167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3561078614062934071194889 2670808960547200553396167)
      ·
        refine ⟨4006213440820800830094251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2670808960547200553396167 4006213440820800830094251)
        ·
          refine ⟨6009320161231201245141377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4006213440820800830094251 6009320161231201245141377)
          ·
            refine ⟨4506990120923400933856033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6009320161231201245141377 4506990120923400933856033)
            ·
              refine ⟨3380242590692550700392025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4506990120923400933856033 3380242590692550700392025)
              ·
                refine ⟨2535181943019413025294019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3380242590692550700392025 2535181943019413025294019)
                ·
                  refine ⟨3802772914529119537941029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2535181943019413025294019 3802772914529119537941029)
                  ·
                    refine ⟨713019921474209913363943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3802772914529119537941029 713019921474209913363943)
                    ·
                      rfl

theorem cell22_2082902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_2082902 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2082902 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2082902 prefixEnd_2082902 := by exact prefixLift 2082902
  have htrace : WordTrace (prefixWord ++ tailWord_2082902) baseStart_2082902 baseEnd_2082902 := by
    simpa [prefixWord, tailWord_2082902, baseEnd_2082902] using wordTrace_append hprefix tailTrace_2082902
  have hstable : (prefixWord ++ tailWord_2082902).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2082902).length < 2 ^ (prefixWord ++ tailWord_2082902).sum := by decide
  have hdescent : baseEnd_2082902 < baseStart_2082902 := by decide
  rcases family_descends (prefixWord ++ tailWord_2082902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2083001 : List Nat := [1, 2, 1, 4, 1, 2, 2, 3, 6]
def baseStart_2083001 : Nat := 118140960795 + 2083001 * 2 ^ 59
def prefixEnd_2083001 : Nat := 4983230072969 + 3 ^ 40 * 2083001 * 2
def baseEnd_2083001 : Nat := 237684603732468885046213

theorem tailTrace_2083001 : CollatzResearch.WordTrace tailWord_2083001 prefixEnd_2083001 237684603732468885046213 := by
  unfold tailWord_2083001
  simp only [CollatzResearch.WordTrace]
  refine ⟨75973287926650600093344857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50648858617767066728896571 75973287926650600093344857)
  ·
    refine ⟨56979965944987950070008643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75973287926650600093344857 56979965944987950070008643)
    ·
      refine ⟨85469948917481925105012965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56979965944987950070008643 85469948917481925105012965)
      ·
        refine ⟨16025615422027860957189931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85469948917481925105012965 16025615422027860957189931)
        ·
          refine ⟨24038423133041791435784897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16025615422027860957189931 24038423133041791435784897)
          ·
            refine ⟨18028817349781343576838673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24038423133041791435784897 18028817349781343576838673)
            ·
              refine ⟨13521613012336007682629005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18028817349781343576838673 13521613012336007682629005)
              ·
                refine ⟨5070604879626002880985877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13521613012336007682629005 5070604879626002880985877)
                ·
                  refine ⟨237684603732468885046213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5070604879626002880985877 237684603732468885046213)
                  ·
                    rfl

theorem cell22_2083001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 3, 6].length) (baseStart_2083001 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2083001 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2083001 prefixEnd_2083001 := by exact prefixLift 2083001
  have htrace : WordTrace (prefixWord ++ tailWord_2083001) baseStart_2083001 baseEnd_2083001 := by
    simpa [prefixWord, tailWord_2083001, baseEnd_2083001] using wordTrace_append hprefix tailTrace_2083001
  have hstable : (prefixWord ++ tailWord_2083001).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2083001).length < 2 ^ (prefixWord ++ tailWord_2083001).sum := by decide
  have hdescent : baseEnd_2083001 < baseStart_2083001 := by decide
  rcases family_descends (prefixWord ++ tailWord_2083001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2083037 : List Nat := [1, 4, 3, 2, 1, 1, 4, 1, 1, 4]
def baseStart_2083037 : Nat := 118140960795 + 2083037 * 2 ^ 59
def prefixEnd_2083037 : Nat := 4983230072969 + 3 ^ 40 * 2083037 * 2
def baseEnd_2083037 : Nat := 713066134733114561238529

theorem tailTrace_2083037 : CollatzResearch.WordTrace tailWord_2083037 prefixEnd_2083037 713066134733114561238529 := by
  unfold tailWord_2083037
  simp only [CollatzResearch.WordTrace]
  refine ⟨75974600954520178241655365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50649733969680118827770243 75974600954520178241655365)
  ·
    refine ⟨14245237678972533420310381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75974600954520178241655365 14245237678972533420310381)
    ·
      refine ⟨5341964129614700032616393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14245237678972533420310381 5341964129614700032616393)
      ·
        refine ⟨4006473097211025024462295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5341964129614700032616393 4006473097211025024462295)
        ·
          refine ⟨6009709645816537536693443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4006473097211025024462295 6009709645816537536693443)
          ·
            refine ⟨9014564468724806305040165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6009709645816537536693443 9014564468724806305040165)
            ·
              refine ⟨1690230837885901182195031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9014564468724806305040165 1690230837885901182195031)
              ·
                refine ⟨2535346256828851773292547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1690230837885901182195031 2535346256828851773292547)
                ·
                  refine ⟨3803019385243277659938821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2535346256828851773292547 3803019385243277659938821)
                  ·
                    refine ⟨713066134733114561238529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3803019385243277659938821 713066134733114561238529)
                    ·
                      rfl

theorem cell22_2083037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 4, 1, 1, 4].length) (baseStart_2083037 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2083037 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2083037 prefixEnd_2083037 := by exact prefixLift 2083037
  have htrace : WordTrace (prefixWord ++ tailWord_2083037) baseStart_2083037 baseEnd_2083037 := by
    simpa [prefixWord, tailWord_2083037, baseEnd_2083037] using wordTrace_append hprefix tailTrace_2083037
  have hstable : (prefixWord ++ tailWord_2083037).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2083037).length < 2 ^ (prefixWord ++ tailWord_2083037).sum := by decide
  have hdescent : baseEnd_2083037 < baseStart_2083037 := by decide
  rcases family_descends (prefixWord ++ tailWord_2083037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2083080 : List Nat := [2, 1, 3, 2, 3, 3, 2, 6]
def baseStart_2083080 : Nat := 118140960795 + 2083080 * 2 ^ 59
def prefixEnd_2083080 : Nat := 4983230072969 + 3 ^ 40 * 2083080 * 2
def baseEnd_2083080 : Nat := 79231206056875198045933

theorem tailTrace_2083080 : CollatzResearch.WordTrace tailWord_2083080 prefixEnd_2083080 79231206056875198045933 := by
  unfold tailWord_2083080
  simp only [CollatzResearch.WordTrace]
  refine ⟨37988084646682198292735347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50650779528909597723647129 37988084646682198292735347)
  ·
    refine ⟨56982126970023297439103021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37988084646682198292735347 56982126970023297439103021)
    ·
      refine ⟨21368297613758736539663633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56982126970023297439103021 21368297613758736539663633)
      ·
        refine ⟨16026223210319052404747725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21368297613758736539663633 16026223210319052404747725)
        ·
          refine ⟨6009833703869644651780397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16026223210319052404747725 6009833703869644651780397)
          ·
            refine ⟨2253687638951116744417649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6009833703869644651780397 2253687638951116744417649)
            ·
              refine ⟨1690265729213337558313237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2253687638951116744417649 1690265729213337558313237)
              ·
                refine ⟨79231206056875198045933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1690265729213337558313237 79231206056875198045933)
                ·
                  rfl

theorem cell22_2083080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 2, 6].length) (baseStart_2083080 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2083080 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2083080 prefixEnd_2083080 := by exact prefixLift 2083080
  have htrace : WordTrace (prefixWord ++ tailWord_2083080) baseStart_2083080 baseEnd_2083080 := by
    simpa [prefixWord, tailWord_2083080, baseEnd_2083080] using wordTrace_append hprefix tailTrace_2083080
  have hstable : (prefixWord ++ tailWord_2083080).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2083080).length < 2 ^ (prefixWord ++ tailWord_2083080).sum := by decide
  have hdescent : baseEnd_2083080 < baseStart_2083080 := by decide
  rcases family_descends (prefixWord ++ tailWord_2083080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2083108 : List Nat := [2, 3, 1, 3, 1, 2, 2, 1, 7]
def baseStart_2083108 : Nat := 118140960795 + 2083108 * 2 ^ 59
def prefixEnd_2083108 : Nat := 4983230072969 + 3 ^ 40 * 2083108 * 2
def baseEnd_2083108 : Nat := 237696813161364680904437

theorem tailTrace_2083108 : CollatzResearch.WordTrace tailWord_2083108 prefixEnd_2083108 237696813161364680904437 := by
  unfold tailWord_2083108
  simp only [CollatzResearch.WordTrace]
  refine ⟨37988595268631478683744989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50651460358175304911659985 37988595268631478683744989)
  ·
    refine ⟨14245723225736804506404371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37988595268631478683744989 14245723225736804506404371)
    ·
      refine ⟨21368584838605206759606557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14245723225736804506404371 21368584838605206759606557)
      ·
        refine ⟨8013219314476952534852459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21368584838605206759606557 8013219314476952534852459)
        ·
          refine ⟨12019828971715428802278689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8013219314476952534852459 12019828971715428802278689)
          ·
            refine ⟨9014871728786571601709017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12019828971715428802278689 9014871728786571601709017)
            ·
              refine ⟨6761153796589928701281763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9014871728786571601709017 6761153796589928701281763)
              ·
                refine ⟨10141730694884893051922645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6761153796589928701281763 10141730694884893051922645)
                ·
                  refine ⟨237696813161364680904437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10141730694884893051922645 237696813161364680904437)
                  ·
                    rfl

theorem cell22_2083108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 2, 1, 7].length) (baseStart_2083108 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2083108 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2083108 prefixEnd_2083108 := by exact prefixLift 2083108
  have htrace : WordTrace (prefixWord ++ tailWord_2083108) baseStart_2083108 baseEnd_2083108 := by
    simpa [prefixWord, tailWord_2083108, baseEnd_2083108] using wordTrace_append hprefix tailTrace_2083108
  have hstable : (prefixWord ++ tailWord_2083108).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2083108).length < 2 ^ (prefixWord ++ tailWord_2083108).sum := by decide
  have hdescent : baseEnd_2083108 < baseStart_2083108 := by decide
  rcases family_descends (prefixWord ++ tailWord_2083108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2083118 : List Nat := [4, 1, 3, 3, 2, 1, 2, 1, 2, 3]
def baseStart_2083118 : Nat := 118140960795 + 2083118 * 2 ^ 59
def prefixEnd_2083118 : Nat := 4983230072969 + 3 ^ 40 * 2083118 * 2
def baseEnd_2083118 : Nat := 713093862688457349963281

theorem tailTrace_2083118 : CollatzResearch.WordTrace tailWord_2083118 prefixEnd_2083118 713093862688457349963281 := by
  unfold tailWord_2083118
  simp only [CollatzResearch.WordTrace]
  refine ⟨9497194408403341134419251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50651703511484486050236005 9497194408403341134419251)
  ·
    refine ⟨14245791612605011701628877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9497194408403341134419251 14245791612605011701628877)
    ·
      refine ⟨5342171854726879388110829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14245791612605011701628877 5342171854726879388110829)
      ·
        refine ⟨2003314445522579770541561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5342171854726879388110829 2003314445522579770541561)
        ·
          refine ⟨1502485834141934827906171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2003314445522579770541561 1502485834141934827906171)
          ·
            refine ⟨2253728751212902241859257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1502485834141934827906171 2253728751212902241859257)
            ·
              refine ⟨1690296563409676681394443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2253728751212902241859257 1690296563409676681394443)
              ·
                refine ⟨2535444845114515022091665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1690296563409676681394443 2535444845114515022091665)
                ·
                  refine ⟨1901583633835886266568749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2535444845114515022091665 1901583633835886266568749)
                  ·
                    refine ⟨713093862688457349963281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1901583633835886266568749 713093862688457349963281)
                    ·
                      rfl

theorem cell22_2083118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 2, 1, 2, 3].length) (baseStart_2083118 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2083118 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2083118 prefixEnd_2083118 := by exact prefixLift 2083118
  have htrace : WordTrace (prefixWord ++ tailWord_2083118) baseStart_2083118 baseEnd_2083118 := by
    simpa [prefixWord, tailWord_2083118, baseEnd_2083118] using wordTrace_append hprefix tailTrace_2083118
  have hstable : (prefixWord ++ tailWord_2083118).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2083118).length < 2 ^ (prefixWord ++ tailWord_2083118).sum := by decide
  have hdescent : baseEnd_2083118 < baseStart_2083118 := by decide
  rcases family_descends (prefixWord ++ tailWord_2083118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2083258 : List Nat := [3, 1, 1, 1, 2, 1, 1, 4, 1, 7]
def baseStart_2083258 : Nat := 118140960795 + 2083258 * 2 ^ 59
def prefixEnd_2083258 : Nat := 4983230072969 + 3 ^ 40 * 2083258 * 2
def baseEnd_2083258 : Nat := 713141787549543651462851

theorem tailTrace_2083258 : CollatzResearch.WordTrace tailWord_2083258 prefixEnd_2083258 713141787549543651462851 := by
  unfold tailWord_2083258
  simp only [CollatzResearch.WordTrace]
  refine ⟨18995665371679883246362607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50655107657813021990300285 18995665371679883246362607)
  ·
    refine ⟨28493498057519824869543911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18995665371679883246362607 28493498057519824869543911)
    ·
      refine ⟨42740247086279737304315867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28493498057519824869543911 42740247086279737304315867)
      ·
        refine ⟨64110370629419605956473801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42740247086279737304315867 64110370629419605956473801)
        ·
          refine ⟨48082777972064704467355351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64110370629419605956473801 48082777972064704467355351)
          ·
            refine ⟨72124166958097056701033027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48082777972064704467355351 72124166958097056701033027)
            ·
              refine ⟨108186250437145585051549541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72124166958097056701033027 108186250437145585051549541)
              ·
                refine ⟨20284921956964797197165539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 108186250437145585051549541 20284921956964797197165539)
                ·
                  refine ⟨30427382935447195795748309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20284921956964797197165539 30427382935447195795748309)
                  ·
                    refine ⟨713141787549543651462851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30427382935447195795748309 713141787549543651462851)
                    ·
                      rfl

theorem cell22_2083258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 4, 1, 7].length) (baseStart_2083258 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2083258 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2083258 prefixEnd_2083258 := by exact prefixLift 2083258
  have htrace : WordTrace (prefixWord ++ tailWord_2083258) baseStart_2083258 baseEnd_2083258 := by
    simpa [prefixWord, tailWord_2083258, baseEnd_2083258] using wordTrace_append hprefix tailTrace_2083258
  have hstable : (prefixWord ++ tailWord_2083258).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2083258).length < 2 ^ (prefixWord ++ tailWord_2083258).sum := by decide
  have hdescent : baseEnd_2083258 < baseStart_2083258 := by decide
  rcases family_descends (prefixWord ++ tailWord_2083258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2083260 : List Nat := [2, 2, 2, 4, 1, 1, 1, 2, 7]
def baseStart_2083260 : Nat := 118140960795 + 2083260 * 2 ^ 59
def prefixEnd_2083260 : Nat := 4983230072969 + 3 ^ 40 * 2083260 * 2
def baseEnd_2083260 : Nat := 237714157396805437637615

theorem tailTrace_2083260 : CollatzResearch.WordTrace tailWord_2083260 prefixEnd_2083260 237714157396805437637615 := by
  unfold tailWord_2083260
  simp only [CollatzResearch.WordTrace]
  refine ⟨37991367216356143663511617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50655156288474858218015489 37991367216356143663511617)
  ·
    refine ⟨28493525412267107747633713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37991367216356143663511617 28493525412267107747633713)
    ·
      refine ⟨21370144059200330810725285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28493525412267107747633713 21370144059200330810725285)
      ·
        refine ⟨4006902011100062027010991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21370144059200330810725285 4006902011100062027010991)
        ·
          refine ⟨6010353016650093040516487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4006902011100062027010991 6010353016650093040516487)
          ·
            refine ⟨9015529524975139560774731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6010353016650093040516487 9015529524975139560774731)
            ·
              refine ⟨13523294287462709341162097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9015529524975139560774731 13523294287462709341162097)
              ·
                refine ⟨10142470715597032005871573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13523294287462709341162097 10142470715597032005871573)
                ·
                  refine ⟨237714157396805437637615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10142470715597032005871573 237714157396805437637615)
                  ·
                    rfl

theorem cell22_2083260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 2, 7].length) (baseStart_2083260 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2083260 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2083260 prefixEnd_2083260 := by exact prefixLift 2083260
  have htrace : WordTrace (prefixWord ++ tailWord_2083260) baseStart_2083260 baseEnd_2083260 := by
    simpa [prefixWord, tailWord_2083260, baseEnd_2083260] using wordTrace_append hprefix tailTrace_2083260
  have hstable : (prefixWord ++ tailWord_2083260).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2083260).length < 2 ^ (prefixWord ++ tailWord_2083260).sum := by decide
  have hdescent : baseEnd_2083260 < baseStart_2083260 := by decide
  rcases family_descends (prefixWord ++ tailWord_2083260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2083290 : List Nat := [3, 1, 1, 2, 3, 1, 2, 2, 3, 4]
def baseStart_2083290 : Nat := 118140960795 + 2083290 * 2 ^ 59
def prefixEnd_2083290 : Nat := 4983230072969 + 3 ^ 40 * 2083290 * 2
def baseEnd_2083290 : Nat := 713152741803506234662753

theorem tailTrace_2083290 : CollatzResearch.WordTrace tailWord_2083290 prefixEnd_2083290 713152741803506234662753 := by
  unfold tailWord_2083290
  simp only [CollatzResearch.WordTrace]
  refine ⟨18995957155650900612653831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50655885748402401633743549 18995957155650900612653831)
  ·
    refine ⟨28493935733476350918980747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18995957155650900612653831 28493935733476350918980747)
    ·
      refine ⟨42740903600214526378471121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28493935733476350918980747 42740903600214526378471121)
      ·
        refine ⟨32055677700160894783853341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42740903600214526378471121 32055677700160894783853341)
        ·
          refine ⟨12020879137560335543945003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32055677700160894783853341 12020879137560335543945003)
          ·
            refine ⟨18031318706340503315917505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12020879137560335543945003 18031318706340503315917505)
            ·
              refine ⟨13523489029755377486938129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18031318706340503315917505 13523489029755377486938129)
              ·
                refine ⟨10142616772316533115203597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13523489029755377486938129 10142616772316533115203597)
                ·
                  refine ⟨3803481289618699918201349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10142616772316533115203597 3803481289618699918201349)
                  ·
                    refine ⟨713152741803506234662753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3803481289618699918201349 713152741803506234662753)
                    ·
                      rfl

theorem cell22_2083290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 2, 3, 4].length) (baseStart_2083290 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2083290 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2083290 prefixEnd_2083290 := by exact prefixLift 2083290
  have htrace : WordTrace (prefixWord ++ tailWord_2083290) baseStart_2083290 baseEnd_2083290 := by
    simpa [prefixWord, tailWord_2083290, baseEnd_2083290] using wordTrace_append hprefix tailTrace_2083290
  have hstable : (prefixWord ++ tailWord_2083290).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2083290).length < 2 ^ (prefixWord ++ tailWord_2083290).sum := by decide
  have hdescent : baseEnd_2083290 < baseStart_2083290 := by decide
  rcases family_descends (prefixWord ++ tailWord_2083290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2083320 : List Nat := [2, 1, 2, 1, 1, 4, 3, 2, 1, 5]
def baseStart_2083320 : Nat := 118140960795 + 2083320 * 2 ^ 59
def prefixEnd_2083320 : Nat := 4983230072969 + 3 ^ 40 * 2083320 * 2
def baseEnd_2083320 : Nat := 713163011416596156412661

theorem tailTrace_2083320 : CollatzResearch.WordTrace tailWord_2083320 prefixEnd_2083320 713163011416596156412661 := by
  unfold tailWord_2083320
  simp only [CollatzResearch.WordTrace]
  refine ⟨37992461406247458787103707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50656615208329945049471609 37992461406247458787103707)
  ·
    refine ⟨56988692109371188180655561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37992461406247458787103707 56988692109371188180655561)
    ·
      refine ⟨42741519082028391135491671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56988692109371188180655561 42741519082028391135491671)
      ·
        refine ⟨64112278623042586703237507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42741519082028391135491671 64112278623042586703237507)
        ·
          refine ⟨96168417934563880054856261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64112278623042586703237507 96168417934563880054856261)
          ·
            refine ⟨18031578362730727510285549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 96168417934563880054856261 18031578362730727510285549)
            ·
              refine ⟨6761841886024022816357081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18031578362730727510285549 6761841886024022816357081)
              ·
                refine ⟨5071381414518017112267811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6761841886024022816357081 5071381414518017112267811)
                ·
                  refine ⟨7607072121777025668401717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5071381414518017112267811 7607072121777025668401717)
                  ·
                    refine ⟨713163011416596156412661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7607072121777025668401717 713163011416596156412661)
                    ·
                      rfl

theorem cell22_2083320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3, 2, 1, 5].length) (baseStart_2083320 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2083320 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2083320 prefixEnd_2083320 := by exact prefixLift 2083320
  have htrace : WordTrace (prefixWord ++ tailWord_2083320) baseStart_2083320 baseEnd_2083320 := by
    simpa [prefixWord, tailWord_2083320, baseEnd_2083320] using wordTrace_append hprefix tailTrace_2083320
  have hstable : (prefixWord ++ tailWord_2083320).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2083320).length < 2 ^ (prefixWord ++ tailWord_2083320).sum := by decide
  have hdescent : baseEnd_2083320 < baseStart_2083320 := by decide
  rcases family_descends (prefixWord ++ tailWord_2083320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2083339 : List Nat := [1, 1, 1, 1, 7, 1, 4, 2, 4]
def baseStart_2083339 : Nat := 118140960795 + 2083339 * 2 ^ 59
def prefixEnd_2083339 : Nat := 4983230072969 + 3 ^ 40 * 2083339 * 2
def baseEnd_2083339 : Nat := 237723171834962146729201

theorem tailTrace_2083339 : CollatzResearch.WordTrace tailWord_2083339 prefixEnd_2083339 237723171834962146729201 := by
  unfold tailWord_2083339
  simp only [CollatzResearch.WordTrace]
  refine ⟨75985615799426083819149071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50657077199617389212766047 75985615799426083819149071)
  ·
    refine ⟨113978423699139125728723607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75985615799426083819149071 113978423699139125728723607)
    ·
      refine ⟨170967635548708688593085411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113978423699139125728723607 170967635548708688593085411)
      ·
        refine ⟨256451453323063032889628117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170967635548708688593085411 256451453323063032889628117)
        ·
          refine ⟨6010580937259289833350659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 256451453323063032889628117 6010580937259289833350659)
          ·
            refine ⟨9015871405888934750025989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6010580937259289833350659 9015871405888934750025989)
            ·
              refine ⟨1690475888604175265629873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9015871405888934750025989 1690475888604175265629873)
              ·
                refine ⟨1267856916453131449222405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1690475888604175265629873 1267856916453131449222405)
                ·
                  refine ⟨237723171834962146729201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1267856916453131449222405 237723171834962146729201)
                  ·
                    rfl

theorem cell22_2083339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 4, 2, 4].length) (baseStart_2083339 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2083339 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2083339 prefixEnd_2083339 := by exact prefixLift 2083339
  have htrace : WordTrace (prefixWord ++ tailWord_2083339) baseStart_2083339 baseEnd_2083339 := by
    simpa [prefixWord, tailWord_2083339, baseEnd_2083339] using wordTrace_append hprefix tailTrace_2083339
  have hstable : (prefixWord ++ tailWord_2083339).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2083339).length < 2 ^ (prefixWord ++ tailWord_2083339).sum := by decide
  have hdescent : baseEnd_2083339 < baseStart_2083339 := by decide
  rcases family_descends (prefixWord ++ tailWord_2083339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2083399 : List Nat := [1, 1, 4, 1, 4, 2, 2, 1, 3, 3]
def baseStart_2083399 : Nat := 118140960795 + 2083399 * 2 ^ 59
def prefixEnd_2083399 : Nat := 4983230072969 + 3 ^ 40 * 2083399 * 2
def baseEnd_2083399 : Nat := 713190054731066283687419

theorem tailTrace_2083399 : CollatzResearch.WordTrace tailWord_2083399 prefixEnd_2083399 713190054731066283687419 := by
  unfold tailWord_2083399
  simp only [CollatzResearch.WordTrace]
  refine ⟨75987804179208714066333251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50658536119472476044222167 75987804179208714066333251)
  ·
    refine ⟨113981706268813071099499877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75987804179208714066333251 113981706268813071099499877)
    ·
      refine ⟨21371569925402450831156227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 113981706268813071099499877 21371569925402450831156227)
      ·
        refine ⟨32057354888103676246734341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21371569925402450831156227 32057354888103676246734341)
        ·
          refine ⟨6010754041519439296262689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32057354888103676246734341 6010754041519439296262689)
          ·
            refine ⟨4508065531139579472197017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6010754041519439296262689 4508065531139579472197017)
            ·
              refine ⟨3381049148354684604147763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4508065531139579472197017 3381049148354684604147763)
              ·
                refine ⟨5071573722532026906221645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3381049148354684604147763 5071573722532026906221645)
                ·
                  refine ⟨1901840145949510089833117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5071573722532026906221645 1901840145949510089833117)
                  ·
                    refine ⟨713190054731066283687419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1901840145949510089833117 713190054731066283687419)
                    ·
                      rfl

theorem cell22_2083399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 2, 1, 3, 3].length) (baseStart_2083399 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2083399 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2083399 prefixEnd_2083399 := by exact prefixLift 2083399
  have htrace : WordTrace (prefixWord ++ tailWord_2083399) baseStart_2083399 baseEnd_2083399 := by
    simpa [prefixWord, tailWord_2083399, baseEnd_2083399] using wordTrace_append hprefix tailTrace_2083399
  have hstable : (prefixWord ++ tailWord_2083399).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2083399).length < 2 ^ (prefixWord ++ tailWord_2083399).sum := by decide
  have hdescent : baseEnd_2083399 < baseStart_2083399 := by decide
  rcases family_descends (prefixWord ++ tailWord_2083399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2083455 : List Nat := [1, 1, 2, 2, 1, 1, 1, 3, 5, 5]
def baseStart_2083455 : Nat := 118140960795 + 2083455 * 2 ^ 59
def prefixEnd_2083455 : Nat := 4983230072969 + 3 ^ 40 * 2083455 * 2
def baseEnd_2083455 : Nat := 713209224675500804287247

theorem tailTrace_2083455 : CollatzResearch.WordTrace tailWord_2083455 prefixEnd_2083455 713209224675500804287247 := by
  unfold tailWord_2083455
  simp only [CollatzResearch.WordTrace]
  refine ⟨75989846667005835630371819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50659897778003890420247879 75989846667005835630371819)
  ·
    refine ⟨113984770000508753445557729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75989846667005835630371819 113984770000508753445557729)
    ·
      refine ⟨85488577500381565084168297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113984770000508753445557729 85488577500381565084168297)
      ·
        refine ⟨64116433125286173813126223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85488577500381565084168297 64116433125286173813126223)
        ·
          refine ⟨96174649687929260719689335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64116433125286173813126223 96174649687929260719689335)
          ·
            refine ⟨144261974531893891079534003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96174649687929260719689335 144261974531893891079534003)
            ·
              refine ⟨216392961797840836619301005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144261974531893891079534003 216392961797840836619301005)
              ·
                refine ⟨81147360674190313732237877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 216392961797840836619301005 81147360674190313732237877)
                ·
                  refine ⟨7607565063205341912397301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 81147360674190313732237877 7607565063205341912397301)
                  ·
                    refine ⟨713209224675500804287247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7607565063205341912397301 713209224675500804287247)
                    ·
                      rfl

theorem cell22_2083455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 3, 5, 5].length) (baseStart_2083455 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2083455 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2083455 prefixEnd_2083455 := by exact prefixLift 2083455
  have htrace : WordTrace (prefixWord ++ tailWord_2083455) baseStart_2083455 baseEnd_2083455 := by
    simpa [prefixWord, tailWord_2083455, baseEnd_2083455] using wordTrace_append hprefix tailTrace_2083455
  have hstable : (prefixWord ++ tailWord_2083455).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2083455).length < 2 ^ (prefixWord ++ tailWord_2083455).sum := by decide
  have hdescent : baseEnd_2083455 < baseStart_2083455 := by decide
  rcases family_descends (prefixWord ++ tailWord_2083455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2083476 : List Nat := [2, 4, 2, 2, 1, 1, 3, 2, 1, 4]
def baseStart_2083476 : Nat := 118140960795 + 2083476 * 2 ^ 59
def prefixEnd_2083476 : Nat := 4983230072969 + 3 ^ 40 * 2083476 * 2
def baseEnd_2083476 : Nat := 713216413404663749512183

theorem tailTrace_2083476 : CollatzResearch.WordTrace tailWord_2083476 prefixEnd_2083476 713216413404663749512183 := by
  unfold tailWord_2083476
  simp only [CollatzResearch.WordTrace]
  refine ⟨37995306299964878108443141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50660408399953170811257521 37995306299964878108443141)
  ·
    refine ⟨7124119931243414645333089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37995306299964878108443141 7124119931243414645333089)
    ·
      refine ⟨5343089948432560983999817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7124119931243414645333089 5343089948432560983999817)
      ·
        refine ⟨4007317461324420737999863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5343089948432560983999817 4007317461324420737999863)
        ·
          refine ⟨6010976191986631106999795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4007317461324420737999863 6010976191986631106999795)
          ·
            refine ⟨9016464287979946660499693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6010976191986631106999795 9016464287979946660499693)
            ·
              refine ⟨3381174107992479997687385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9016464287979946660499693 3381174107992479997687385)
              ·
                refine ⟨2535880580994359998265539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3381174107992479997687385 2535880580994359998265539)
                ·
                  refine ⟨3803820871491539997398309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2535880580994359998265539 3803820871491539997398309)
                  ·
                    refine ⟨713216413404663749512183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3803820871491539997398309 713216413404663749512183)
                    ·
                      rfl

theorem cell22_2083476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 3, 2, 1, 4].length) (baseStart_2083476 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2083476 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2083476 prefixEnd_2083476 := by exact prefixLift 2083476
  have htrace : WordTrace (prefixWord ++ tailWord_2083476) baseStart_2083476 baseEnd_2083476 := by
    simpa [prefixWord, tailWord_2083476, baseEnd_2083476] using wordTrace_append hprefix tailTrace_2083476
  have hstable : (prefixWord ++ tailWord_2083476).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2083476).length < 2 ^ (prefixWord ++ tailWord_2083476).sum := by decide
  have hdescent : baseEnd_2083476 < baseStart_2083476 := by decide
  rcases family_descends (prefixWord ++ tailWord_2083476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2083489 : List Nat := [1, 2, 3, 3, 3, 1, 1, 2, 1, 5]
def baseStart_2083489 : Nat := 118140960795 + 2083489 * 2 ^ 59
def prefixEnd_2083489 : Nat := 4983230072969 + 3 ^ 40 * 2083489 * 2
def baseEnd_2083489 : Nat := 713220863570336048937143

theorem tailTrace_2083489 : CollatzResearch.WordTrace tailWord_2083489 prefixEnd_2083489 713220863570336048937143 := by
  unfold tailWord_2083489
  simp only [CollatzResearch.WordTrace]
  refine ⟨75991086748882659437109521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50660724499255106291406347 75991086748882659437109521)
  ·
    refine ⟨56993315061661994577832141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75991086748882659437109521 56993315061661994577832141)
    ·
      refine ⟨21372493148123247966687053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56993315061661994577832141 21372493148123247966687053)
      ·
        refine ⟨8014684930546217987507645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21372493148123247966687053 8014684930546217987507645)
        ·
          refine ⟨3005506848954831745315367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8014684930546217987507645 3005506848954831745315367)
          ·
            refine ⟨4508260273432247617973051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3005506848954831745315367 4508260273432247617973051)
            ·
              refine ⟨6762390410148371426959577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4508260273432247617973051 6762390410148371426959577)
              ·
                refine ⟨5071792807611278570219683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6762390410148371426959577 5071792807611278570219683)
                ·
                  refine ⟨7607689211416917855329525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5071792807611278570219683 7607689211416917855329525)
                  ·
                    refine ⟨713220863570336048937143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7607689211416917855329525 713220863570336048937143)
                    ·
                      rfl

theorem cell22_2083489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 1, 2, 1, 5].length) (baseStart_2083489 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2083489 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2083489 prefixEnd_2083489 := by exact prefixLift 2083489
  have htrace : WordTrace (prefixWord ++ tailWord_2083489) baseStart_2083489 baseEnd_2083489 := by
    simpa [prefixWord, tailWord_2083489, baseEnd_2083489] using wordTrace_append hprefix tailTrace_2083489
  have hstable : (prefixWord ++ tailWord_2083489).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2083489).length < 2 ^ (prefixWord ++ tailWord_2083489).sum := by decide
  have hdescent : baseEnd_2083489 < baseStart_2083489 := by decide
  rcases family_descends (prefixWord ++ tailWord_2083489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2083534 : List Nat := [4, 1, 1, 1, 3, 2, 1, 1, 5, 3]
def baseStart_2083534 : Nat := 118140960795 + 2083534 * 2 ^ 59
def prefixEnd_2083534 : Nat := 4983230072969 + 3 ^ 40 * 2083534 * 2
def baseEnd_2083534 : Nat := 713236267989970931562005

theorem tailTrace_2083534 : CollatzResearch.WordTrace tailWord_2083534 prefixEnd_2083534 713236267989970931562005 := by
  unfold tailWord_2083534
  simp only [CollatzResearch.WordTrace]
  refine ⟨9499091004214954015312207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50661818689146421414998437 9499091004214954015312207)
  ·
    refine ⟨14248636506322431022968311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9499091004214954015312207 14248636506322431022968311)
    ·
      refine ⟨21372954759483646534452467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14248636506322431022968311 21372954759483646534452467)
      ·
        refine ⟨32059432139225469801678701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21372954759483646534452467 32059432139225469801678701)
        ·
          refine ⟨12022287052209551175629513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32059432139225469801678701 12022287052209551175629513)
          ·
            refine ⟨9016715289157163381722135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12022287052209551175629513 9016715289157163381722135)
            ·
              refine ⟨13525072933735745072583203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9016715289157163381722135 13525072933735745072583203)
              ·
                refine ⟨20287609400603617608874805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13525072933735745072583203 20287609400603617608874805)
                ·
                  refine ⟨1901963381306589150832013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20287609400603617608874805 1901963381306589150832013)
                  ·
                    refine ⟨713236267989970931562005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1901963381306589150832013 713236267989970931562005)
                    ·
                      rfl

theorem cell22_2083534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 1, 5, 3].length) (baseStart_2083534 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2083534 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2083534 prefixEnd_2083534 := by exact prefixLift 2083534
  have htrace : WordTrace (prefixWord ++ tailWord_2083534) baseStart_2083534 baseEnd_2083534 := by
    simpa [prefixWord, tailWord_2083534, baseEnd_2083534] using wordTrace_append hprefix tailTrace_2083534
  have hstable : (prefixWord ++ tailWord_2083534).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2083534).length < 2 ^ (prefixWord ++ tailWord_2083534).sum := by decide
  have hdescent : baseEnd_2083534 < baseStart_2083534 := by decide
  rcases family_descends (prefixWord ++ tailWord_2083534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2083538 : List Nat := [3, 2, 2, 2, 4, 1, 1, 1, 2, 4]
def baseStart_2083538 : Nat := 118140960795 + 2083538 * 2 ^ 59
def prefixEnd_2083538 : Nat := 4983230072969 + 3 ^ 40 * 2083538 * 2
def baseEnd_2083538 : Nat := 713237637271716254461993

theorem tailTrace_2083538 : CollatzResearch.WordTrace tailWord_2083538 prefixEnd_2083538 713237637271716254461993 := by
  unfold tailWord_2083538
  simp only [CollatzResearch.WordTrace]
  refine ⟨18998218481426285201410817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50661915950470093870428845 18998218481426285201410817)
  ·
    refine ⟨14248663861069713901058113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18998218481426285201410817 14248663861069713901058113)
    ·
      refine ⟨10686497895802285425793585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14248663861069713901058113 10686497895802285425793585)
      ·
        refine ⟨8014873421851714069345189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10686497895802285425793585 8014873421851714069345189)
        ·
          refine ⟨1502788766597196388002223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8014873421851714069345189 1502788766597196388002223)
          ·
            refine ⟨2254183149895794582003335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1502788766597196388002223 2254183149895794582003335)
            ·
              refine ⟨3381274724843691873005003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2254183149895794582003335 3381274724843691873005003)
              ·
                refine ⟨5071912087265537809507505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3381274724843691873005003 5071912087265537809507505)
                ·
                  refine ⟨3803934065449153357130629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5071912087265537809507505 3803934065449153357130629)
                  ·
                    refine ⟨713237637271716254461993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3803934065449153357130629 713237637271716254461993)
                    ·
                      rfl

theorem cell22_2083538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 1, 1, 2, 4].length) (baseStart_2083538 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2083538 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2083538 prefixEnd_2083538 := by exact prefixLift 2083538
  have htrace : WordTrace (prefixWord ++ tailWord_2083538) baseStart_2083538 baseEnd_2083538 := by
    simpa [prefixWord, tailWord_2083538, baseEnd_2083538] using wordTrace_append hprefix tailTrace_2083538
  have hstable : (prefixWord ++ tailWord_2083538).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2083538).length < 2 ^ (prefixWord ++ tailWord_2083538).sum := by decide
  have hdescent : baseEnd_2083538 < baseStart_2083538 := by decide
  rcases family_descends (prefixWord ++ tailWord_2083538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2083551 : List Nat := [1, 1, 2, 3, 2, 3, 1, 5, 1, 3]
def baseStart_2083551 : Nat := 118140960795 + 2083551 * 2 ^ 59
def prefixEnd_2083551 : Nat := 4983230072969 + 3 ^ 40 * 2083551 * 2
def baseEnd_2083551 : Nat := 713242087437388553886953

theorem tailTrace_2083551 : CollatzResearch.WordTrace tailWord_2083551 prefixEnd_2083551 713242087437388553886953 := by
  unfold tailWord_2083551
  simp only [CollatzResearch.WordTrace]
  refine ⟨75993348074658044025866507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50662232049772029350577671 75993348074658044025866507)
  ·
    refine ⟨113990022111987066038799761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75993348074658044025866507 113990022111987066038799761)
    ·
      refine ⟨85492516583990299529099821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113990022111987066038799761 85492516583990299529099821)
      ·
        refine ⟨32059693718996362323412433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85492516583990299529099821 32059693718996362323412433)
        ·
          refine ⟨24044770289247271742559325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32059693718996362323412433 24044770289247271742559325)
          ·
            refine ⟨9016788858467726903459747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24044770289247271742559325 9016788858467726903459747)
            ·
              refine ⟨13525183287701590355189621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9016788858467726903459747 13525183287701590355189621)
              ·
                refine ⟨1267985933222024095799027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13525183287701590355189621 1267985933222024095799027)
                ·
                  refine ⟨1901978899833036143698541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1267985933222024095799027 1901978899833036143698541)
                  ·
                    refine ⟨713242087437388553886953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1901978899833036143698541 713242087437388553886953)
                    ·
                      rfl

theorem cell22_2083551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 5, 1, 3].length) (baseStart_2083551 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2083551 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2083551 prefixEnd_2083551 := by exact prefixLift 2083551
  have htrace : WordTrace (prefixWord ++ tailWord_2083551) baseStart_2083551 baseEnd_2083551 := by
    simpa [prefixWord, tailWord_2083551, baseEnd_2083551] using wordTrace_append hprefix tailTrace_2083551
  have hstable : (prefixWord ++ tailWord_2083551).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2083551).length < 2 ^ (prefixWord ++ tailWord_2083551).sum := by decide
  have hdescent : baseEnd_2083551 < baseStart_2083551 := by decide
  rcases family_descends (prefixWord ++ tailWord_2083551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2083577 : List Nat := [1, 2, 1, 3, 1, 1, 1, 3, 5, 4]
def baseStart_2083577 : Nat := 118140960795 + 2083577 * 2 ^ 59
def prefixEnd_2083577 : Nat := 4983230072969 + 3 ^ 40 * 2083577 * 2
def baseEnd_2083577 : Nat := 713250987768733152736873

theorem tailTrace_2083577 : CollatzResearch.WordTrace tailWord_2083577 prefixEnd_2083577 713250987768733152736873 := by
  unfold tailWord_2083577
  simp only [CollatzResearch.WordTrace]
  refine ⟨75994296372563850466312985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50662864248375900310875323 75994296372563850466312985)
  ·
    refine ⟨56995722279422887849734739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75994296372563850466312985 56995722279422887849734739)
    ·
      refine ⟨85493583419134331774602109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56995722279422887849734739 85493583419134331774602109)
      ·
        refine ⟨32060093782175374415475791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85493583419134331774602109 32060093782175374415475791)
        ·
          refine ⟨48090140673263061623213687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32060093782175374415475791 48090140673263061623213687)
          ·
            refine ⟨72135211009894592434820531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48090140673263061623213687 72135211009894592434820531)
            ·
              refine ⟨108202816514841888652230797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72135211009894592434820531 108202816514841888652230797)
              ·
                refine ⟨40576056193065708244586549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 108202816514841888652230797 40576056193065708244586549)
                ·
                  refine ⟨3804005268099910147929989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40576056193065708244586549 3804005268099910147929989)
                  ·
                    refine ⟨713250987768733152736873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3804005268099910147929989 713250987768733152736873)
                    ·
                      rfl

theorem cell22_2083577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 3, 5, 4].length) (baseStart_2083577 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2083577 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2083577 prefixEnd_2083577 := by exact prefixLift 2083577
  have htrace : WordTrace (prefixWord ++ tailWord_2083577) baseStart_2083577 baseEnd_2083577 := by
    simpa [prefixWord, tailWord_2083577, baseEnd_2083577] using wordTrace_append hprefix tailTrace_2083577
  have hstable : (prefixWord ++ tailWord_2083577).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2083577).length < 2 ^ (prefixWord ++ tailWord_2083577).sum := by decide
  have hdescent : baseEnd_2083577 < baseStart_2083577 := by decide
  rcases family_descends (prefixWord ++ tailWord_2083577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2083602 : List Nat := [3, 2, 4, 1, 2, 2, 1, 3, 1, 3]
def baseStart_2083602 : Nat := 118140960795 + 2083602 * 2 ^ 59
def prefixEnd_2083602 : Nat := 4983230072969 + 3 ^ 40 * 2083602 * 2
def baseEnd_2083602 : Nat := 713259545779641420861797

theorem tailTrace_2083602 : CollatzResearch.WordTrace tailWord_2083602 prefixEnd_2083602 713259545779641420861797 := by
  unfold tailWord_2083602
  simp only [CollatzResearch.WordTrace]
  refine ⟨18998802049368319933993265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50663472131648853157315373 18998802049368319933993265)
  ·
    refine ⟨14249101537026239950494949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18998802049368319933993265 14249101537026239950494949)
    ·
      refine ⟨2671706538192419990717803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14249101537026239950494949 2671706538192419990717803)
      ·
        refine ⟨4007559807288629986076705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2671706538192419990717803 4007559807288629986076705)
        ·
          refine ⟨3005669855466472489557529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4007559807288629986076705 3005669855466472489557529)
          ·
            refine ⟨2254252391599854367168147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3005669855466472489557529 2254252391599854367168147)
            ·
              refine ⟨3381378587399781550752221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2254252391599854367168147 3381378587399781550752221)
              ·
                refine ⟨1268016970274918081532083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3381378587399781550752221 1268016970274918081532083)
                ·
                  refine ⟨1902025455412377122298125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1268016970274918081532083 1902025455412377122298125)
                  ·
                    refine ⟨713259545779641420861797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1902025455412377122298125 713259545779641420861797)
                    ·
                      rfl

theorem cell22_2083602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 1, 3, 1, 3].length) (baseStart_2083602 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2083602 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2083602 prefixEnd_2083602 := by exact prefixLift 2083602
  have htrace : WordTrace (prefixWord ++ tailWord_2083602) baseStart_2083602 baseEnd_2083602 := by
    simpa [prefixWord, tailWord_2083602, baseEnd_2083602] using wordTrace_append hprefix tailTrace_2083602
  have hstable : (prefixWord ++ tailWord_2083602).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2083602).length < 2 ^ (prefixWord ++ tailWord_2083602).sum := by decide
  have hdescent : baseEnd_2083602 < baseStart_2083602 := by decide
  rcases family_descends (prefixWord ++ tailWord_2083602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2083609 : List Nat := [1, 2, 1, 2, 1, 1, 1, 9, 4]
def baseStart_2083609 : Nat := 118140960795 + 2083609 * 2 ^ 59
def prefixEnd_2083609 : Nat := 4983230072969 + 3 ^ 40 * 2083609 * 2
def baseEnd_2083609 : Nat := 237753980674231911978925

theorem tailTrace_2083609 : CollatzResearch.WordTrace tailWord_2083609 prefixEnd_2083609 237753980674231911978925 := by
  unfold tailWord_2083609
  simp only [CollatzResearch.WordTrace]
  refine ⟨75995463508447919931477881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50663642338965279954318587 75995463508447919931477881)
  ·
    refine ⟨56996597631335939948608411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75995463508447919931477881 56996597631335939948608411)
    ·
      refine ⟨85494896447003909922912617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56996597631335939948608411 85494896447003909922912617)
      ·
        refine ⟨64121172335252932442184463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85494896447003909922912617 64121172335252932442184463)
        ·
          refine ⟨96181758502879398663276695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64121172335252932442184463 96181758502879398663276695)
          ·
            refine ⟨144272637754319097994915043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96181758502879398663276695 144272637754319097994915043)
            ·
              refine ⟨216408956631478646992372565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144272637754319097994915043 216408956631478646992372565)
              ·
                refine ⟨1268021230262570197220933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 216408956631478646992372565 1268021230262570197220933)
                ·
                  refine ⟨237753980674231911978925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1268021230262570197220933 237753980674231911978925)
                  ·
                    rfl

theorem cell22_2083609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 9, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 9, 4].length) (baseStart_2083609 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2083609 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2083609 prefixEnd_2083609 := by exact prefixLift 2083609
  have htrace : WordTrace (prefixWord ++ tailWord_2083609) baseStart_2083609 baseEnd_2083609 := by
    simpa [prefixWord, tailWord_2083609, baseEnd_2083609] using wordTrace_append hprefix tailTrace_2083609
  have hstable : (prefixWord ++ tailWord_2083609).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2083609).length < 2 ^ (prefixWord ++ tailWord_2083609).sum := by decide
  have hdescent : baseEnd_2083609 < baseStart_2083609 := by decide
  rcases family_descends (prefixWord ++ tailWord_2083609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2083645 : List Nat := [1, 4, 1, 4, 3, 1, 1, 2, 1, 4]
def baseStart_2083645 : Nat := 118140960795 + 2083645 * 2 ^ 59
def prefixEnd_2083645 : Nat := 4983230072969 + 3 ^ 40 * 2083645 * 2
def baseEnd_2083645 : Nat := 713274265558403642036665

theorem tailTrace_2083645 : CollatzResearch.WordTrace tailWord_2083645 prefixEnd_2083645 713274265558403642036665 := by
  unfold tailWord_2083645
  simp only [CollatzResearch.WordTrace]
  refine ⟨75996776536317498079788389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50664517690878332053192259 75996776536317498079788389)
  ·
    refine ⟨14249395600559530889960323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75996776536317498079788389 14249395600559530889960323)
    ·
      refine ⟨21374093400839296334940485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14249395600559530889960323 21374093400839296334940485)
      ·
        refine ⟨4007642512657368062801341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21374093400839296334940485 4007642512657368062801341)
        ·
          refine ⟨1502865942246513023550503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4007642512657368062801341 1502865942246513023550503)
          ·
            refine ⟨2254298913369769535325755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1502865942246513023550503 2254298913369769535325755)
            ·
              refine ⟨3381448370054654302988633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2254298913369769535325755 3381448370054654302988633)
              ·
                refine ⟨2536086277540990727241475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3381448370054654302988633 2536086277540990727241475)
                ·
                  refine ⟨3804129416311486090862213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2536086277540990727241475 3804129416311486090862213)
                  ·
                    refine ⟨713274265558403642036665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3804129416311486090862213 713274265558403642036665)
                    ·
                      rfl

theorem cell22_2083645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 1, 2, 1, 4].length) (baseStart_2083645 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2083645 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2083645 prefixEnd_2083645 := by exact prefixLift 2083645
  have htrace : WordTrace (prefixWord ++ tailWord_2083645) baseStart_2083645 baseEnd_2083645 := by
    simpa [prefixWord, tailWord_2083645, baseEnd_2083645] using wordTrace_append hprefix tailTrace_2083645
  have hstable : (prefixWord ++ tailWord_2083645).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2083645).length < 2 ^ (prefixWord ++ tailWord_2083645).sum := by decide
  have hdescent : baseEnd_2083645 < baseStart_2083645 := by decide
  rcases family_descends (prefixWord ++ tailWord_2083645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2083667 : List Nat := [1, 1, 1, 2, 1, 1, 3, 2, 4, 6]
def baseStart_2083667 : Nat := 118140960795 + 2083667 * 2 ^ 59
def prefixEnd_2083667 : Nat := 4983230072969 + 3 ^ 40 * 2083667 * 2
def baseEnd_2083667 : Nat := 713281796608002917986597

theorem tailTrace_2083667 : CollatzResearch.WordTrace tailWord_2083667 prefixEnd_2083667 713281796608002917986597 := by
  unfold tailWord_2083667
  simp only [CollatzResearch.WordTrace]
  refine ⟨75997578942237795837089255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50665052628158530558059503 75997578942237795837089255)
  ·
    refine ⟨113996368413356693755633883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75997578942237795837089255 113996368413356693755633883)
    ·
      refine ⟨170994552620035040633450825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113996368413356693755633883 170994552620035040633450825)
      ·
        refine ⟨128245914465026280475088119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170994552620035040633450825 128245914465026280475088119)
        ·
          refine ⟨192368871697539420712632179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128245914465026280475088119 192368871697539420712632179)
          ·
            refine ⟨288553307546309131068948269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192368871697539420712632179 288553307546309131068948269)
            ·
              refine ⟨108207490329865924150855601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 288553307546309131068948269 108207490329865924150855601)
              ·
                refine ⟨81155617747399443113141701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108207490329865924150855601 81155617747399443113141701)
                ·
                  refine ⟨15216678327637395583714069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 81155617747399443113141701 15216678327637395583714069)
                  ·
                    refine ⟨713281796608002917986597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15216678327637395583714069 713281796608002917986597)
                    ·
                      rfl

theorem cell22_2083667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 2, 4, 6].length) (baseStart_2083667 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2083667 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2083667 prefixEnd_2083667 := by exact prefixLift 2083667
  have htrace : WordTrace (prefixWord ++ tailWord_2083667) baseStart_2083667 baseEnd_2083667 := by
    simpa [prefixWord, tailWord_2083667, baseEnd_2083667] using wordTrace_append hprefix tailTrace_2083667
  have hstable : (prefixWord ++ tailWord_2083667).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2083667).length < 2 ^ (prefixWord ++ tailWord_2083667).sum := by decide
  have hdescent : baseEnd_2083667 < baseStart_2083667 := by decide
  rcases family_descends (prefixWord ++ tailWord_2083667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2083684 : List Nat := [2, 3, 1, 1, 4, 1, 1, 1, 2, 6]
def baseStart_2083684 : Nat := 118140960795 + 2083684 * 2 ^ 59
def prefixEnd_2083684 : Nat := 4983230072969 + 3 ^ 40 * 2083684 * 2
def baseEnd_2083684 : Nat := 713287616055420540311545

theorem tailTrace_2083684 : CollatzResearch.WordTrace tailWord_2083684 prefixEnd_2083684 713287616055420540311545 := by
  unfold tailWord_2083684
  simp only [CollatzResearch.WordTrace]
  refine ⟨37999099491588103870229053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50665465988784138493638737 37999099491588103870229053)
  ·
    refine ⟨14249662309345538951335895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37999099491588103870229053 14249662309345538951335895)
    ·
      refine ⟨21374493464018308427003843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14249662309345538951335895 21374493464018308427003843)
      ·
        refine ⟨32061740196027462640505765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21374493464018308427003843 32061740196027462640505765)
        ·
          refine ⟨6011576286755149245094831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32061740196027462640505765 6011576286755149245094831)
          ·
            refine ⟨9017364430132723867642247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6011576286755149245094831 9017364430132723867642247)
            ·
              refine ⟨13526046645199085801463371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9017364430132723867642247 13526046645199085801463371)
              ·
                refine ⟨20289069967798628702195057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13526046645199085801463371 20289069967798628702195057)
                ·
                  refine ⟨15216802475848971526646293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20289069967798628702195057 15216802475848971526646293)
                  ·
                    refine ⟨713287616055420540311545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15216802475848971526646293 713287616055420540311545)
                    ·
                      rfl

theorem cell22_2083684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 1, 2, 6].length) (baseStart_2083684 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2083684 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2083684 prefixEnd_2083684 := by exact prefixLift 2083684
  have htrace : WordTrace (prefixWord ++ tailWord_2083684) baseStart_2083684 baseEnd_2083684 := by
    simpa [prefixWord, tailWord_2083684, baseEnd_2083684] using wordTrace_append hprefix tailTrace_2083684
  have hstable : (prefixWord ++ tailWord_2083684).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2083684).length < 2 ^ (prefixWord ++ tailWord_2083684).sum := by decide
  have hdescent : baseEnd_2083684 < baseStart_2083684 := by decide
  rcases family_descends (prefixWord ++ tailWord_2083684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2083699 : List Nat := [1, 1, 1, 2, 2, 1, 6, 3, 5]
def baseStart_2083699 : Nat := 118140960795 + 2083699 * 2 ^ 59
def prefixEnd_2083699 : Nat := 4983230072969 + 3 ^ 40 * 2083699 * 2
def baseEnd_2083699 : Nat := 237764250287321833728833

theorem tailTrace_2083699 : CollatzResearch.WordTrace tailWord_2083699 prefixEnd_2083699 237764250287321833728833 := by
  unfold tailWord_2083699
  simp only [CollatzResearch.WordTrace]
  refine ⟨75998746078121865302254151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50665830718747910201502767 75998746078121865302254151)
  ·
    refine ⟨113998119117182797953381227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75998746078121865302254151 113998119117182797953381227)
    ·
      refine ⟨170997178675774196930071841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113998119117182797953381227 170997178675774196930071841)
      ·
        refine ⟨128247884006830647697553881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170997178675774196930071841 128247884006830647697553881)
        ·
          refine ⟨96185913005122985773165411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128247884006830647697553881 96185913005122985773165411)
          ·
            refine ⟨144278869507684478659748117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96185913005122985773165411 144278869507684478659748117)
            ·
              refine ⟨6763072008172709937175693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 144278869507684478659748117 6763072008172709937175693)
              ·
                refine ⟨2536152003064766226440885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6763072008172709937175693 2536152003064766226440885)
                ·
                  refine ⟨237764250287321833728833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2536152003064766226440885 237764250287321833728833)
                  ·
                    rfl

theorem cell22_2083699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6, 3, 5].length) (baseStart_2083699 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2083699 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2083699 prefixEnd_2083699 := by exact prefixLift 2083699
  have htrace : WordTrace (prefixWord ++ tailWord_2083699) baseStart_2083699 baseEnd_2083699 := by
    simpa [prefixWord, tailWord_2083699, baseEnd_2083699] using wordTrace_append hprefix tailTrace_2083699
  have hstable : (prefixWord ++ tailWord_2083699).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2083699).length < 2 ^ (prefixWord ++ tailWord_2083699).sum := by decide
  have hdescent : baseEnd_2083699 < baseStart_2083699 := by decide
  rcases family_descends (prefixWord ++ tailWord_2083699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2083720 : List Nat := [2, 1, 3, 3, 2, 2, 2, 3, 1, 3]
def baseStart_2083720 : Nat := 118140960795 + 2083720 * 2 ^ 59
def prefixEnd_2083720 : Nat := 4983230072969 + 3 ^ 40 * 2083720 * 2
def baseEnd_2083720 : Nat := 713299939591128446411435

theorem tailTrace_2083720 : CollatzResearch.WordTrace tailWord_2083720 prefixEnd_2083720 713299939591128446411435 := by
  unfold tailWord_2083720
  simp only [CollatzResearch.WordTrace]
  refine ⟨37999756005522892944384307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50666341340697190592512409 37999756005522892944384307)
  ·
    refine ⟨56999634008284339416576461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37999756005522892944384307 56999634008284339416576461)
    ·
      refine ⟨21374862753106627281216173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56999634008284339416576461 21374862753106627281216173)
      ·
        refine ⟨8015573532414985230456065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21374862753106627281216173 8015573532414985230456065)
        ·
          refine ⟨6011680149311238922842049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8015573532414985230456065 6011680149311238922842049)
          ·
            refine ⟨4508760111983429192131537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6011680149311238922842049 4508760111983429192131537)
            ·
              refine ⟨3381570083987571894098653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4508760111983429192131537 3381570083987571894098653)
              ·
                refine ⟨1268088781495339460286995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3381570083987571894098653 1268088781495339460286995)
                ·
                  refine ⟨1902133172243009190430493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1268088781495339460286995 1902133172243009190430493)
                  ·
                    refine ⟨713299939591128446411435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1902133172243009190430493 713299939591128446411435)
                    ·
                      rfl

theorem cell22_2083720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 2, 3, 1, 3].length) (baseStart_2083720 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2083720 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2083720 prefixEnd_2083720 := by exact prefixLift 2083720
  have htrace : WordTrace (prefixWord ++ tailWord_2083720) baseStart_2083720 baseEnd_2083720 := by
    simpa [prefixWord, tailWord_2083720, baseEnd_2083720] using wordTrace_append hprefix tailTrace_2083720
  have hstable : (prefixWord ++ tailWord_2083720).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2083720).length < 2 ^ (prefixWord ++ tailWord_2083720).sum := by decide
  have hdescent : baseEnd_2083720 < baseStart_2083720 := by decide
  rcases family_descends (prefixWord ++ tailWord_2083720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2083744 : List Nat := [2, 1, 1, 4, 1, 1, 3, 3, 6]
def baseStart_2083744 : Nat := 118140960795 + 2083744 * 2 ^ 59
def prefixEnd_2083744 : Nat := 4983230072969 + 3 ^ 40 * 2083744 * 2
def baseEnd_2083744 : Nat := 237769385093866794603787

theorem tailTrace_2083744 : CollatzResearch.WordTrace tailWord_2083744 prefixEnd_2083744 237769385093866794603787 := by
  unfold tailWord_2083744
  simp only [CollatzResearch.WordTrace]
  refine ⟨38000193681479418993821143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50666924908639225325094857 38000193681479418993821143)
  ·
    refine ⟨57000290522219128490731715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38000193681479418993821143 57000290522219128490731715)
    ·
      refine ⟨85500435783328692736097573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57000290522219128490731715 85500435783328692736097573)
      ·
        refine ⟨16031331709374129888018295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85500435783328692736097573 16031331709374129888018295)
        ·
          refine ⟨24046997564061194832027443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16031331709374129888018295 24046997564061194832027443)
          ·
            refine ⟨36070496346091792248041165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24046997564061194832027443 36070496346091792248041165)
            ·
              refine ⟨13526436129784422093015437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36070496346091792248041165 13526436129784422093015437)
              ·
                refine ⟨5072413548669158284880789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13526436129784422093015437 5072413548669158284880789)
                ·
                  refine ⟨237769385093866794603787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5072413548669158284880789 237769385093866794603787)
                  ·
                    rfl

theorem cell22_2083744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 3, 6].length) (baseStart_2083744 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2083744 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2083744 prefixEnd_2083744 := by exact prefixLift 2083744
  have htrace : WordTrace (prefixWord ++ tailWord_2083744) baseStart_2083744 baseEnd_2083744 := by
    simpa [prefixWord, tailWord_2083744, baseEnd_2083744] using wordTrace_append hprefix tailTrace_2083744
  have hstable : (prefixWord ++ tailWord_2083744).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2083744).length < 2 ^ (prefixWord ++ tailWord_2083744).sum := by decide
  have hdescent : baseEnd_2083744 < baseStart_2083744 := by decide
  rcases family_descends (prefixWord ++ tailWord_2083744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2083759 : List Nat := [1, 1, 2, 1, 2, 2, 2, 5, 1, 5]
def baseStart_2083759 : Nat := 118140960795 + 2083759 * 2 ^ 59
def prefixEnd_2083759 : Nat := 4983230072969 + 3 ^ 40 * 2083759 * 2
def baseEnd_2083759 : Nat := 713313290088145344686315

theorem tailTrace_2083759 : CollatzResearch.WordTrace tailWord_2083759 prefixEnd_2083759 713313290088145344686315 := by
  unfold tailWord_2083759
  simp only [CollatzResearch.WordTrace]
  refine ⟨76000934457904495549438331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50667289638602997032958887 76000934457904495549438331)
  ·
    refine ⟨114001401686856743324157497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76000934457904495549438331 114001401686856743324157497)
    ·
      refine ⟨85501051265142557493118123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114001401686856743324157497 85501051265142557493118123)
      ·
        refine ⟨128251576897713836239677185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85501051265142557493118123 128251576897713836239677185)
        ·
          refine ⟨96188682673285377179757889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128251576897713836239677185 96188682673285377179757889)
          ·
            refine ⟨72141512004964032884818417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96188682673285377179757889 72141512004964032884818417)
            ·
              refine ⟨54106134003723024663613813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72141512004964032884818417 54106134003723024663613813)
              ·
                refine ⟨5072450062849033562213795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 54106134003723024663613813 5072450062849033562213795)
                ·
                  refine ⟨7608675094273550343320693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5072450062849033562213795 7608675094273550343320693)
                  ·
                    refine ⟨713313290088145344686315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7608675094273550343320693 713313290088145344686315)
                    ·
                      rfl

theorem cell22_2083759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 5, 1, 5].length) (baseStart_2083759 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2083759 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2083759 prefixEnd_2083759 := by exact prefixLift 2083759
  have htrace : WordTrace (prefixWord ++ tailWord_2083759) baseStart_2083759 baseEnd_2083759 := by
    simpa [prefixWord, tailWord_2083759, baseEnd_2083759] using wordTrace_append hprefix tailTrace_2083759
  have hstable : (prefixWord ++ tailWord_2083759).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2083759).length < 2 ^ (prefixWord ++ tailWord_2083759).sum := by decide
  have hdescent : baseEnd_2083759 < baseStart_2083759 := by decide
  rcases family_descends (prefixWord ++ tailWord_2083759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2083776 : List Nat := [2, 1, 1, 2, 3, 3, 1, 2, 4, 3]
def baseStart_2083776 : Nat := 118140960795 + 2083776 * 2 ^ 59
def prefixEnd_2083776 : Nat := 4983230072969 + 3 ^ 40 * 2083776 * 2
def baseEnd_2083776 : Nat := 713319109535562967011263

theorem tailTrace_2083776 : CollatzResearch.WordTrace tailWord_2083776 prefixEnd_2083776 713319109535562967011263 := by
  unfold tailWord_2083776
  simp only [CollatzResearch.WordTrace]
  refine ⟨38000777249421453726403591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50667702999228604968538121 38000777249421453726403591)
  ·
    refine ⟨57001165874132180589605387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38000777249421453726403591 57001165874132180589605387)
    ·
      refine ⟨85501748811198270884408081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57001165874132180589605387 85501748811198270884408081)
      ·
        refine ⟨64126311608398703163306061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85501748811198270884408081 64126311608398703163306061)
        ·
          refine ⟨24047366853149513686239773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64126311608398703163306061 24047366853149513686239773)
          ·
            refine ⟨9017762569931067632339915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24047366853149513686239773 9017762569931067632339915)
            ·
              refine ⟨13526643854896601448509873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9017762569931067632339915 13526643854896601448509873)
              ·
                refine ⟨10144982891172451086382405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13526643854896601448509873 10144982891172451086382405)
                ·
                  refine ⟨1902184292094834578696701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10144982891172451086382405 1902184292094834578696701)
                  ·
                    refine ⟨713319109535562967011263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1902184292094834578696701 713319109535562967011263)
                    ·
                      rfl

theorem cell22_2083776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 2, 4, 3].length) (baseStart_2083776 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2083776 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2083776 prefixEnd_2083776 := by exact prefixLift 2083776
  have htrace : WordTrace (prefixWord ++ tailWord_2083776) baseStart_2083776 baseEnd_2083776 := by
    simpa [prefixWord, tailWord_2083776, baseEnd_2083776] using wordTrace_append hprefix tailTrace_2083776
  have hstable : (prefixWord ++ tailWord_2083776).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2083776).length < 2 ^ (prefixWord ++ tailWord_2083776).sum := by decide
  have hdescent : baseEnd_2083776 < baseStart_2083776 := by decide
  rcases family_descends (prefixWord ++ tailWord_2083776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2083791 : List Nat := [1, 1, 2, 1, 1, 7, 1, 2, 2, 4]
def baseStart_2083791 : Nat := 118140960795 + 2083791 * 2 ^ 59
def prefixEnd_2083791 : Nat := 4983230072969 + 3 ^ 40 * 2083791 * 2
def baseEnd_2083791 : Nat := 713324244342107927886217

theorem tailTrace_2083791 : CollatzResearch.WordTrace tailWord_2083791 prefixEnd_2083791 713324244342107927886217 := by
  unfold tailWord_2083791
  simp only [CollatzResearch.WordTrace]
  refine ⟨76002101593788565014603227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50668067729192376676402151 76002101593788565014603227)
  ·
    refine ⟨114003152390682847521904841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76002101593788565014603227 114003152390682847521904841)
    ·
      refine ⟨85502364293012135641428631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114003152390682847521904841 85502364293012135641428631)
      ·
        refine ⟨128253546439518203462142947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85502364293012135641428631 128253546439518203462142947)
        ·
          refine ⟨192380319659277305193214421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128253546439518203462142947 192380319659277305193214421)
          ·
            refine ⟨4508913742014311840465963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 192380319659277305193214421 4508913742014311840465963)
            ·
              refine ⟨6763370613021467760698945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4508913742014311840465963 6763370613021467760698945)
              ·
                refine ⟨5072527959766100820524209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6763370613021467760698945 5072527959766100820524209)
                ·
                  refine ⟨3804395969824575615393157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5072527959766100820524209 3804395969824575615393157)
                  ·
                    refine ⟨713324244342107927886217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3804395969824575615393157 713324244342107927886217)
                    ·
                      rfl

theorem cell22_2083791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 1, 2, 2, 4].length) (baseStart_2083791 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2083791 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2083791 prefixEnd_2083791 := by exact prefixLift 2083791
  have htrace : WordTrace (prefixWord ++ tailWord_2083791) baseStart_2083791 baseEnd_2083791 := by
    simpa [prefixWord, tailWord_2083791, baseEnd_2083791] using wordTrace_append hprefix tailTrace_2083791
  have hstable : (prefixWord ++ tailWord_2083791).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2083791).length < 2 ^ (prefixWord ++ tailWord_2083791).sum := by decide
  have hdescent : baseEnd_2083791 < baseStart_2083791 := by decide
  rcases family_descends (prefixWord ++ tailWord_2083791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2083834 : List Nat := [3, 1, 1, 1, 1, 2, 1, 3, 9]
def baseStart_2083834 : Nat := 118140960795 + 2083834 * 2 ^ 59
def prefixEnd_2083834 : Nat := 4983230072969 + 3 ^ 40 * 2083834 * 2
def baseEnd_2083834 : Nat := 237779654706956716353695

theorem tailTrace_2083834 : CollatzResearch.WordTrace tailWord_2083834 prefixEnd_2083834 237779654706956716353695 := by
  unfold tailWord_2083834
  simp only [CollatzResearch.WordTrace]
  refine ⟨19000917483158195839604639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50669113288421855572279037 19000917483158195839604639)
  ·
    refine ⟨28501376224737293759406959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19000917483158195839604639 28501376224737293759406959)
    ·
      refine ⟨42752064337105940639110439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28501376224737293759406959 42752064337105940639110439)
      ·
        refine ⟨64128096505658910958665659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42752064337105940639110439 64128096505658910958665659)
        ·
          refine ⟨96192144758488366437998489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64128096505658910958665659 96192144758488366437998489)
          ·
            refine ⟨72144108568866274828498867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96192144758488366437998489 72144108568866274828498867)
            ·
              refine ⟨108216162853299412242748301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72144108568866274828498867 108216162853299412242748301)
              ·
                refine ⟨40581061069987279591030613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 108216162853299412242748301 40581061069987279591030613)
                ·
                  refine ⟨237779654706956716353695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 40581061069987279591030613 237779654706956716353695)
                  ·
                    rfl

theorem cell22_2083834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 3, 9].length) (baseStart_2083834 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2083834 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2083834 prefixEnd_2083834 := by exact prefixLift 2083834
  have htrace : WordTrace (prefixWord ++ tailWord_2083834) baseStart_2083834 baseEnd_2083834 := by
    simpa [prefixWord, tailWord_2083834, baseEnd_2083834] using wordTrace_append hprefix tailTrace_2083834
  have hstable : (prefixWord ++ tailWord_2083834).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2083834).length < 2 ^ (prefixWord ++ tailWord_2083834).sum := by decide
  have hdescent : baseEnd_2083834 < baseStart_2083834 := by decide
  rcases family_descends (prefixWord ++ tailWord_2083834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2083849 : List Nat := [1, 2, 1, 1, 3, 1, 1, 2, 3, 7]
def baseStart_2083849 : Nat := 118140960795 + 2083849 * 2 ^ 59
def prefixEnd_2083849 : Nat := 4983230072969 + 3 ^ 40 * 2083849 * 2
def baseEnd_2083849 : Nat := 713344098927415109936039

theorem tailTrace_2083849 : CollatzResearch.WordTrace tailWord_2083849 prefixEnd_2083849 713344098927415109936039 := by
  unfold tailWord_2083849
  simp only [CollatzResearch.WordTrace]
  refine ⟨76004217027578440920214601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50669478018385627280143067 76004217027578440920214601)
  ·
    refine ⟨57003162770683830690160951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76004217027578440920214601 57003162770683830690160951)
    ·
      refine ⟨85504744156025746035241427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57003162770683830690160951 85504744156025746035241427)
      ·
        refine ⟨128257116234038619052862141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85504744156025746035241427 128257116234038619052862141)
        ·
          refine ⟨48096418587764482144823303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128257116234038619052862141 48096418587764482144823303)
          ·
            refine ⟨72144627881646723217234955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48096418587764482144823303 72144627881646723217234955)
            ·
              refine ⟨108216941822470084825852433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72144627881646723217234955 108216941822470084825852433)
              ·
                refine ⟨81162706366852563619389325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108216941822470084825852433 81162706366852563619389325)
                ·
                  refine ⟨30436014887569711357270997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 81162706366852563619389325 30436014887569711357270997)
                  ·
                    refine ⟨713344098927415109936039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30436014887569711357270997 713344098927415109936039)
                    ·
                      rfl

theorem cell22_2083849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 2, 3, 7].length) (baseStart_2083849 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2083849 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2083849 prefixEnd_2083849 := by exact prefixLift 2083849
  have htrace : WordTrace (prefixWord ++ tailWord_2083849) baseStart_2083849 baseEnd_2083849 := by
    simpa [prefixWord, tailWord_2083849, baseEnd_2083849] using wordTrace_append hprefix tailTrace_2083849
  have hstable : (prefixWord ++ tailWord_2083849).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2083849).length < 2 ^ (prefixWord ++ tailWord_2083849).sum := by decide
  have hdescent : baseEnd_2083849 < baseStart_2083849 := by decide
  rcases family_descends (prefixWord ++ tailWord_2083849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2083851 : List Nat := [1, 1, 1, 1, 6, 2, 1, 4, 5]
def baseStart_2083851 : Nat := 118140960795 + 2083851 * 2 ^ 59
def prefixEnd_2083851 : Nat := 4983230072969 + 3 ^ 40 * 2083851 * 2
def baseEnd_2083851 : Nat := 237781594522762590462011

theorem tailTrace_2083851 : CollatzResearch.WordTrace tailWord_2083851 prefixEnd_2083851 237781594522762590462011 := by
  unfold tailWord_2083851
  simp only [CollatzResearch.WordTrace]
  refine ⟨76004289973571195261787407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50669526649047463507858271 76004289973571195261787407)
  ·
    refine ⟨114006434960356792892681111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76004289973571195261787407 114006434960356792892681111)
    ·
      refine ⟨171009652440535189339021667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114006434960356792892681111 171009652440535189339021667)
      ·
        refine ⟨256514478660802784008532501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171009652440535189339021667 256514478660802784008532501)
        ·
          refine ⟨12024116187225130500399961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 256514478660802784008532501 12024116187225130500399961)
          ·
            refine ⟨9018087140418847875299971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12024116187225130500399961 9018087140418847875299971)
            ·
              refine ⟨13527130710628271812949957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9018087140418847875299971 13527130710628271812949957)
              ·
                refine ⟨2536337008242800964928117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13527130710628271812949957 2536337008242800964928117)
                ·
                  refine ⟨237781594522762590462011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2536337008242800964928117 237781594522762590462011)
                  ·
                    rfl

theorem cell22_2083851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 4, 5].length) (baseStart_2083851 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2083851 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2083851 prefixEnd_2083851 := by exact prefixLift 2083851
  have htrace : WordTrace (prefixWord ++ tailWord_2083851) baseStart_2083851 baseEnd_2083851 := by
    simpa [prefixWord, tailWord_2083851, baseEnd_2083851] using wordTrace_append hprefix tailTrace_2083851
  have hstable : (prefixWord ++ tailWord_2083851).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2083851).length < 2 ^ (prefixWord ++ tailWord_2083851).sum := by decide
  have hdescent : baseEnd_2083851 < baseStart_2083851 := by decide
  rcases family_descends (prefixWord ++ tailWord_2083851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2083866 : List Nat := [3, 1, 1, 3, 1, 2, 3, 1, 2, 5]
def baseStart_2083866 : Nat := 118140960795 + 2083866 * 2 ^ 59
def prefixEnd_2083866 : Nat := 4983230072969 + 3 ^ 40 * 2083866 * 2
def baseEnd_2083866 : Nat := 713349918374832732260987

theorem tailTrace_2083866 : CollatzResearch.WordTrace tailWord_2083866 prefixEnd_2083866 713349918374832732260987 := by
  unfold tailWord_2083866
  simp only [CollatzResearch.WordTrace]
  refine ⟨19001209267129213205895863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50669891379011235215722301 19001209267129213205895863)
  ·
    refine ⟨28501813900693819808843795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19001209267129213205895863 28501813900693819808843795)
    ·
      refine ⟨42752720851040729713265693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28501813900693819808843795 42752720851040729713265693)
      ·
        refine ⟨16032270319140273642474635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42752720851040729713265693 16032270319140273642474635)
        ·
          refine ⟨24048405478710410463711953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16032270319140273642474635 24048405478710410463711953)
          ·
            refine ⟨18036304109032807847783965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24048405478710410463711953 18036304109032807847783965)
            ·
              refine ⟨6763614040887302942918987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18036304109032807847783965 6763614040887302942918987)
              ·
                refine ⟨10145421061330954414378481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6763614040887302942918987 10145421061330954414378481)
                ·
                  refine ⟨7609065795998215810783861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10145421061330954414378481 7609065795998215810783861)
                  ·
                    refine ⟨713349918374832732260987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7609065795998215810783861 713349918374832732260987)
                    ·
                      rfl

theorem cell22_2083866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3, 1, 2, 5].length) (baseStart_2083866 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2083866 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2083866 prefixEnd_2083866 := by exact prefixLift 2083866
  have htrace : WordTrace (prefixWord ++ tailWord_2083866) baseStart_2083866 baseEnd_2083866 := by
    simpa [prefixWord, tailWord_2083866, baseEnd_2083866] using wordTrace_append hprefix tailTrace_2083866
  have hstable : (prefixWord ++ tailWord_2083866).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2083866).length < 2 ^ (prefixWord ++ tailWord_2083866).sum := by decide
  have hdescent : baseEnd_2083866 < baseStart_2083866 := by decide
  rcases family_descends (prefixWord ++ tailWord_2083866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2083941 : List Nat := [1, 3, 1, 3, 2, 1, 3, 8]
def baseStart_2083941 : Nat := 118140960795 + 2083941 * 2 ^ 59
def prefixEnd_2083941 : Nat := 4983230072969 + 3 ^ 40 * 2083941 * 2
def baseEnd_2083941 : Nat := 79263954711950837403973

theorem tailTrace_2083941 : CollatzResearch.WordTrace tailWord_2083941 prefixEnd_2083941 79263954711950837403973 := by
  unfold tailWord_2083941
  simp only [CollatzResearch.WordTrace]
  refine ⟨76007572543245140632563677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50671715028830093755042451 76007572543245140632563677)
  ·
    refine ⟨28502839703716927737211379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76007572543245140632563677 28502839703716927737211379)
    ·
      refine ⟨42754259555575391605817069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28502839703716927737211379 42754259555575391605817069)
      ·
        refine ⟨16032847333340771852181401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42754259555575391605817069 16032847333340771852181401)
        ·
          refine ⟨12024635500005578889136051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16032847333340771852181401 12024635500005578889136051)
          ·
            refine ⟨18036953250008368333704077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12024635500005578889136051 18036953250008368333704077)
            ·
              refine ⟨6763857468753138125139029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18036953250008368333704077 6763857468753138125139029)
              ·
                refine ⟨79263954711950837403973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6763857468753138125139029 79263954711950837403973)
                ·
                  rfl

theorem cell22_2083941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 3, 8].length) (baseStart_2083941 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2083941 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2083941 prefixEnd_2083941 := by exact prefixLift 2083941
  have htrace : WordTrace (prefixWord ++ tailWord_2083941) baseStart_2083941 baseEnd_2083941 := by
    simpa [prefixWord, tailWord_2083941, baseEnd_2083941] using wordTrace_append hprefix tailTrace_2083941
  have hstable : (prefixWord ++ tailWord_2083941).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2083941).length < 2 ^ (prefixWord ++ tailWord_2083941).sum := by decide
  have hdescent : baseEnd_2083941 < baseStart_2083941 := by decide
  rcases family_descends (prefixWord ++ tailWord_2083941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2083971 : List Nat := [1, 1, 1, 3, 3, 2, 2, 1, 2, 6]
def baseStart_2083971 : Nat := 118140960795 + 2083971 * 2 ^ 59
def prefixEnd_2083971 : Nat := 4983230072969 + 3 ^ 40 * 2083971 * 2
def baseEnd_2083971 : Nat := 713385862020647458385665

theorem tailTrace_2083971 : CollatzResearch.WordTrace tailWord_2083971 prefixEnd_2083971 713385862020647458385665 := by
  unfold tailWord_2083971
  simp only [CollatzResearch.WordTrace]
  refine ⟨76008666733136455756155767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50672444488757637170770511 76008666733136455756155767)
  ·
    refine ⟨114013000099704683634233651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76008666733136455756155767 114013000099704683634233651)
    ·
      refine ⟨171019500149557025451350477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114013000099704683634233651 171019500149557025451350477)
      ·
        refine ⟨64132312556083884544256429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 171019500149557025451350477 64132312556083884544256429)
        ·
          refine ⟨24049617208531456704096161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64132312556083884544256429 24049617208531456704096161)
          ·
            refine ⟨18037212906398592528072121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24049617208531456704096161 18037212906398592528072121)
            ·
              refine ⟨13527909679798944396054091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18037212906398592528072121 13527909679798944396054091)
              ·
                refine ⟨20291864519698416594081137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13527909679798944396054091 20291864519698416594081137)
                ·
                  refine ⟨15218898389773812445560853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20291864519698416594081137 15218898389773812445560853)
                  ·
                    refine ⟨713385862020647458385665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15218898389773812445560853 713385862020647458385665)
                    ·
                      rfl

theorem cell22_2083971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 1, 2, 6].length) (baseStart_2083971 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2083971 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2083971 prefixEnd_2083971 := by exact prefixLift 2083971
  have htrace : WordTrace (prefixWord ++ tailWord_2083971) baseStart_2083971 baseEnd_2083971 := by
    simpa [prefixWord, tailWord_2083971, baseEnd_2083971] using wordTrace_append hprefix tailTrace_2083971
  have hstable : (prefixWord ++ tailWord_2083971).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2083971).length < 2 ^ (prefixWord ++ tailWord_2083971).sum := by decide
  have hdescent : baseEnd_2083971 < baseStart_2083971 := by decide
  rcases family_descends (prefixWord ++ tailWord_2083971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2084050 : List Nat := [3, 2, 2, 2, 1, 1, 2, 4, 1, 4]
def baseStart_2084050 : Nat := 118140960795 + 2084050 * 2 ^ 59
def prefixEnd_2084050 : Nat := 4983230072969 + 3 ^ 40 * 2084050 * 2
def baseEnd_2084050 : Nat := 713412905335117585660423

theorem tailTrace_2084050 : CollatzResearch.WordTrace tailWord_2084050 prefixEnd_2084050 713412905335117585660423 := by
  unfold tailWord_2084050
  simp only [CollatzResearch.WordTrace]
  refine ⟨19002887024962563062070401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50674365399900168165521069 19002887024962563062070401)
  ·
    refine ⟨14252165268721922296552801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19002887024962563062070401 14252165268721922296552801)
    ·
      refine ⟨10689123951541441722414601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14252165268721922296552801 10689123951541441722414601)
      ·
        refine ⟨8016842963656081291810951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10689123951541441722414601 8016842963656081291810951)
        ·
          refine ⟨12025264445484121937716427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8016842963656081291810951 12025264445484121937716427)
          ·
            refine ⟨18037896668226182906574641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12025264445484121937716427 18037896668226182906574641)
            ·
              refine ⟨13528422501169637179930981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18037896668226182906574641 13528422501169637179930981)
              ·
                refine ⟨2536579218969306971237059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13528422501169637179930981 2536579218969306971237059)
                ·
                  refine ⟨3804868828453960456855589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2536579218969306971237059 3804868828453960456855589)
                  ·
                    refine ⟨713412905335117585660423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3804868828453960456855589 713412905335117585660423)
                    ·
                      rfl

theorem cell22_2084050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 4, 1, 4].length) (baseStart_2084050 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2084050 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2084050 prefixEnd_2084050 := by exact prefixLift 2084050
  have htrace : WordTrace (prefixWord ++ tailWord_2084050) baseStart_2084050 baseEnd_2084050 := by
    simpa [prefixWord, tailWord_2084050, baseEnd_2084050] using wordTrace_append hprefix tailTrace_2084050
  have hstable : (prefixWord ++ tailWord_2084050).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2084050).length < 2 ^ (prefixWord ++ tailWord_2084050).sum := by decide
  have hdescent : baseEnd_2084050 < baseStart_2084050 := by decide
  rcases family_descends (prefixWord ++ tailWord_2084050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2084063 : List Nat := [1, 1, 2, 3, 2, 1, 4, 2, 1, 5]
def baseStart_2084063 : Nat := 118140960795 + 2084063 * 2 ^ 59
def prefixEnd_2084063 : Nat := 4983230072969 + 3 ^ 40 * 2084063 * 2
def baseEnd_2084063 : Nat := 713417355500789885085383

theorem tailTrace_2084063 : CollatzResearch.WordTrace tailWord_2084063 prefixEnd_2084063 713417355500789885085383 := by
  unfold tailWord_2084063
  simp only [CollatzResearch.WordTrace]
  refine ⟨76012022248803155468504843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50674681499202103645669895 76012022248803155468504843)
  ·
    refine ⟨114018033373204733202757265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76012022248803155468504843 114018033373204733202757265)
    ·
      refine ⟨85513525029903549902067949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114018033373204733202757265 85513525029903549902067949)
      ·
        refine ⟨32067571886213831213275481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85513525029903549902067949 32067571886213831213275481)
        ·
          refine ⟨24050678914660373409956611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32067571886213831213275481 24050678914660373409956611)
          ·
            refine ⟨36076018371990560114934917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24050678914660373409956611 36076018371990560114934917)
            ·
              refine ⟨6764253444748230021550297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36076018371990560114934917 6764253444748230021550297)
              ·
                refine ⟨5073190083561172516162723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6764253444748230021550297 5073190083561172516162723)
                ·
                  refine ⟨7609785125341758774244085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5073190083561172516162723 7609785125341758774244085)
                  ·
                    refine ⟨713417355500789885085383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7609785125341758774244085 713417355500789885085383)
                    ·
                      rfl

theorem cell22_2084063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4, 2, 1, 5].length) (baseStart_2084063 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2084063 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2084063 prefixEnd_2084063 := by exact prefixLift 2084063
  have htrace : WordTrace (prefixWord ++ tailWord_2084063) baseStart_2084063 baseEnd_2084063 := by
    simpa [prefixWord, tailWord_2084063, baseEnd_2084063] using wordTrace_append hprefix tailTrace_2084063
  have hstable : (prefixWord ++ tailWord_2084063).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2084063).length < 2 ^ (prefixWord ++ tailWord_2084063).sum := by decide
  have hdescent : baseEnd_2084063 < baseStart_2084063 := by decide
  rcases family_descends (prefixWord ++ tailWord_2084063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2084065 : List Nat := [1, 2, 3, 1, 3, 2, 1, 5, 4]
def baseStart_2084065 : Nat := 118140960795 + 2084065 * 2 ^ 59
def prefixEnd_2084065 : Nat := 4983230072969 + 3 ^ 40 * 2084065 * 2
def baseEnd_2084065 : Nat := 237806013380554182178459

theorem tailTrace_2084065 : CollatzResearch.WordTrace tailWord_2084065 prefixEnd_2084065 237806013380554182178459 := by
  unfold tailWord_2084065
  simp only [CollatzResearch.WordTrace]
  refine ⟨76012095194795909810077649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50674730129863939873385099 76012095194795909810077649)
  ·
    refine ⟨57009071396096932357558237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76012095194795909810077649 57009071396096932357558237)
    ·
      refine ⟨21378401773536349634084339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57009071396096932357558237 21378401773536349634084339)
      ·
        refine ⟨32067602660304524451126509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21378401773536349634084339 32067602660304524451126509)
        ·
          refine ⟨12025350997614196669172441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32067602660304524451126509 12025350997614196669172441)
          ·
            refine ⟨9019013248210647501879331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12025350997614196669172441 9019013248210647501879331)
            ·
              refine ⟨13528519872315971252818997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9019013248210647501879331 13528519872315971252818997)
              ·
                refine ⟨1268298738029622304951781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13528519872315971252818997 1268298738029622304951781)
                ·
                  refine ⟨237806013380554182178459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1268298738029622304951781 237806013380554182178459)
                  ·
                    rfl

theorem cell22_2084065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 5, 4].length) (baseStart_2084065 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2084065 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2084065 prefixEnd_2084065 := by exact prefixLift 2084065
  have htrace : WordTrace (prefixWord ++ tailWord_2084065) baseStart_2084065 baseEnd_2084065 := by
    simpa [prefixWord, tailWord_2084065, baseEnd_2084065] using wordTrace_append hprefix tailTrace_2084065
  have hstable : (prefixWord ++ tailWord_2084065).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2084065).length < 2 ^ (prefixWord ++ tailWord_2084065).sum := by decide
  have hdescent : baseEnd_2084065 < baseStart_2084065 := by decide
  rcases family_descends (prefixWord ++ tailWord_2084065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2084110 : List Nat := [4, 1, 1, 2, 1, 3, 4, 6]
def baseStart_2084110 : Nat := 118140960795 + 2084110 * 2 ^ 59
def prefixEnd_2084110 : Nat := 4983230072969 + 3 ^ 40 * 2084110 * 2
def baseEnd_2084110 : Nat := 79270382729033047684471

theorem tailTrace_2084110 : CollatzResearch.WordTrace tailWord_2084110 prefixEnd_2084110 79270382729033047684471 := by
  unfold tailWord_2084110
  simp only [CollatzResearch.WordTrace]
  refine ⟨9501717059954110311933223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50675824319755254996977189 9501717059954110311933223)
  ·
    refine ⟨14252575589931165467899835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9501717059954110311933223 14252575589931165467899835)
    ·
      refine ⟨21378863384896748201849753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14252575589931165467899835 21378863384896748201849753)
      ·
        refine ⟨16034147538672561151387315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21378863384896748201849753 16034147538672561151387315)
        ·
          refine ⟨24051221308008841727080973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16034147538672561151387315 24051221308008841727080973)
          ·
            refine ⟨9019207990503315647655365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24051221308008841727080973 9019207990503315647655365)
            ·
              refine ⟨1691101498219371683935381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9019207990503315647655365 1691101498219371683935381)
              ·
                refine ⟨79270382729033047684471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1691101498219371683935381 79270382729033047684471)
                ·
                  rfl

theorem cell22_2084110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 4, 6].length) (baseStart_2084110 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2084110 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2084110 prefixEnd_2084110 := by exact prefixLift 2084110
  have htrace : WordTrace (prefixWord ++ tailWord_2084110) baseStart_2084110 baseEnd_2084110 := by
    simpa [prefixWord, tailWord_2084110, baseEnd_2084110] using wordTrace_append hprefix tailTrace_2084110
  have hstable : (prefixWord ++ tailWord_2084110).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2084110).length < 2 ^ (prefixWord ++ tailWord_2084110).sum := by decide
  have hdescent : baseEnd_2084110 < baseStart_2084110 := by decide
  rcases family_descends (prefixWord ++ tailWord_2084110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2084185 : List Nat := [1, 2, 1, 2, 2, 2, 2, 5, 1, 4]
def baseStart_2084185 : Nat := 118140960795 + 2084185 * 2 ^ 59
def prefixEnd_2084185 : Nat := 4983230072969 + 3 ^ 40 * 2084185 * 2
def baseEnd_2084185 : Nat := 713459118594022233535009

theorem tailTrace_2084185 : CollatzResearch.WordTrace tailWord_2084185 prefixEnd_2084185 713459118594022233535009 := by
  unfold tailWord_2084185
  simp only [CollatzResearch.WordTrace]
  refine ⟨76016471954361170304446009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50677647969574113536297339 76016471954361170304446009)
  ·
    refine ⟨57012353965770877728334507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76016471954361170304446009 57012353965770877728334507)
    ·
      refine ⟨85518530948656316592501761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57012353965770877728334507 85518530948656316592501761)
      ·
        refine ⟨64138898211492237444376321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85518530948656316592501761 64138898211492237444376321)
        ·
          refine ⟨48104173658619178083282241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64138898211492237444376321 48104173658619178083282241)
          ·
            refine ⟨36078130243964383562461681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48104173658619178083282241 36078130243964383562461681)
            ·
              refine ⟨27058597682973287671846261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36078130243964383562461681 27058597682973287671846261)
              ·
                refine ⟨2536743532778745719235587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27058597682973287671846261 2536743532778745719235587)
                ·
                  refine ⟨3805115299168118578853381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2536743532778745719235587 3805115299168118578853381)
                  ·
                    refine ⟨713459118594022233535009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3805115299168118578853381 713459118594022233535009)
                    ·
                      rfl

theorem cell22_2084185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 5, 1, 4].length) (baseStart_2084185 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2084185 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2084185 prefixEnd_2084185 := by exact prefixLift 2084185
  have htrace : WordTrace (prefixWord ++ tailWord_2084185) baseStart_2084185 baseEnd_2084185 := by
    simpa [prefixWord, tailWord_2084185, baseEnd_2084185] using wordTrace_append hprefix tailTrace_2084185
  have hstable : (prefixWord ++ tailWord_2084185).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2084185).length < 2 ^ (prefixWord ++ tailWord_2084185).sum := by decide
  have hdescent : baseEnd_2084185 < baseStart_2084185 := by decide
  rcases family_descends (prefixWord ++ tailWord_2084185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2084215 : List Nat := [1, 1, 3, 1, 1, 2, 6, 1, 1, 5]
def baseStart_2084215 : Nat := 118140960795 + 2084215 * 2 ^ 59
def prefixEnd_2084215 : Nat := 4983230072969 + 3 ^ 40 * 2084215 * 2
def baseEnd_2084215 : Nat := 713469388207112155284917

theorem tailTrace_2084215 : CollatzResearch.WordTrace tailWord_2084215 prefixEnd_2084215 713469388207112155284917 := by
  unfold tailWord_2084215
  simp only [CollatzResearch.WordTrace]
  refine ⟨76017566144252485428038099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50678377429501656952025399 76017566144252485428038099)
  ·
    refine ⟨114026349216378728142057149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76017566144252485428038099 114026349216378728142057149)
    ·
      refine ⟨42759880956142023053271431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114026349216378728142057149 42759880956142023053271431)
      ·
        refine ⟨64139821434213034579907147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42759880956142023053271431 64139821434213034579907147)
        ·
          refine ⟨96209732151319551869860721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64139821434213034579907147 96209732151319551869860721)
          ·
            refine ⟨72157299113489663902395541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96209732151319551869860721 72157299113489663902395541)
            ·
              refine ⟨3382373395944827995424791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 72157299113489663902395541 3382373395944827995424791)
              ·
                refine ⟨5073560093917241993137187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3382373395944827995424791 5073560093917241993137187)
                ·
                  refine ⟨7610340140875862989705781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5073560093917241993137187 7610340140875862989705781)
                  ·
                    refine ⟨713469388207112155284917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7610340140875862989705781 713469388207112155284917)
                    ·
                      rfl

theorem cell22_2084215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 6, 1, 1, 5].length) (baseStart_2084215 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2084215 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2084215 prefixEnd_2084215 := by exact prefixLift 2084215
  have htrace : WordTrace (prefixWord ++ tailWord_2084215) baseStart_2084215 baseEnd_2084215 := by
    simpa [prefixWord, tailWord_2084215, baseEnd_2084215] using wordTrace_append hprefix tailTrace_2084215
  have hstable : (prefixWord ++ tailWord_2084215).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2084215).length < 2 ^ (prefixWord ++ tailWord_2084215).sum := by decide
  have hdescent : baseEnd_2084215 < baseStart_2084215 := by decide
  rcases family_descends (prefixWord ++ tailWord_2084215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2084243 : List Nat := [1, 1, 1, 2, 1, 2, 1, 1, 3, 9]
def baseStart_2084243 : Nat := 118140960795 + 2084243 * 2 ^ 59
def prefixEnd_2084243 : Nat := 4983230072969 + 3 ^ 40 * 2084243 * 2
def baseEnd_2084243 : Nat := 713478973179329415584831

theorem tailTrace_2084243 : CollatzResearch.WordTrace tailWord_2084243 prefixEnd_2084243 713478973179329415584831 := by
  unfold tailWord_2084243
  simp only [CollatzResearch.WordTrace]
  refine ⟨76018587388151046210057383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50679058258767364140038255 76018587388151046210057383)
  ·
    refine ⟨114027881082226569315086075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76018587388151046210057383 114027881082226569315086075)
    ·
      refine ⟨171041821623339853972629113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114027881082226569315086075 171041821623339853972629113)
      ·
        refine ⟨128281366217504890479471835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171041821623339853972629113 128281366217504890479471835)
        ·
          refine ⟨192422049326257335719207753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128281366217504890479471835 192422049326257335719207753)
          ·
            refine ⟨144316536994693001789405815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 192422049326257335719207753 144316536994693001789405815)
            ·
              refine ⟨216474805492039502684108723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144316536994693001789405815 216474805492039502684108723)
              ·
                refine ⟨324712208238059254026163085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 216474805492039502684108723 324712208238059254026163085)
                ·
                  refine ⟨121767078089272220259811157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 324712208238059254026163085 121767078089272220259811157)
                  ·
                    refine ⟨713478973179329415584831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 121767078089272220259811157 713478973179329415584831)
                    ·
                      rfl

theorem cell22_2084243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 3, 9].length) (baseStart_2084243 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2084243 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2084243 prefixEnd_2084243 := by exact prefixLift 2084243
  have htrace : WordTrace (prefixWord ++ tailWord_2084243) baseStart_2084243 baseEnd_2084243 := by
    simpa [prefixWord, tailWord_2084243, baseEnd_2084243] using wordTrace_append hprefix tailTrace_2084243
  have hstable : (prefixWord ++ tailWord_2084243).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2084243).length < 2 ^ (prefixWord ++ tailWord_2084243).sum := by decide
  have hdescent : baseEnd_2084243 < baseStart_2084243 := by decide
  rcases family_descends (prefixWord ++ tailWord_2084243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2084249 : List Nat := [1, 2, 1, 2, 1, 7, 1, 2, 2, 3]
def baseStart_2084249 : Nat := 118140960795 + 2084249 * 2 ^ 59
def prefixEnd_2084249 : Nat := 4983230072969 + 3 ^ 40 * 2084249 * 2
def baseEnd_2084249 : Nat := 713481027101947399934813

theorem tailTrace_2084249 : CollatzResearch.WordTrace tailWord_2084249 prefixEnd_2084249 713481027101947399934813 := by
  unfold tailWord_2084249
  simp only [CollatzResearch.WordTrace]
  refine ⟨76018806226129309234775801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50679204150752872823183867 76018806226129309234775801)
  ·
    refine ⟨57014104669596981926081851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76018806226129309234775801 57014104669596981926081851)
    ·
      refine ⟨85521157004395472889122777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57014104669596981926081851 85521157004395472889122777)
      ·
        refine ⟨64140867753296604666842083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85521157004395472889122777 64140867753296604666842083)
        ·
          refine ⟨96211301629944907000263125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64140867753296604666842083 96211301629944907000263125)
          ·
            refine ⟨2254952381951833757818667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 96211301629944907000263125 2254952381951833757818667)
            ·
              refine ⟨3382428572927750636728001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2254952381951833757818667 3382428572927750636728001)
              ·
                refine ⟨2536821429695812977546001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3382428572927750636728001 2536821429695812977546001)
                ·
                  refine ⟨1902616072271859733159501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2536821429695812977546001 1902616072271859733159501)
                  ·
                    refine ⟨713481027101947399934813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1902616072271859733159501 713481027101947399934813)
                    ·
                      rfl

theorem cell22_2084249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 1, 2, 2, 3].length) (baseStart_2084249 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2084249 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2084249 prefixEnd_2084249 := by exact prefixLift 2084249
  have htrace : WordTrace (prefixWord ++ tailWord_2084249) baseStart_2084249 baseEnd_2084249 := by
    simpa [prefixWord, tailWord_2084249, baseEnd_2084249] using wordTrace_append hprefix tailTrace_2084249
  have hstable : (prefixWord ++ tailWord_2084249).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2084249).length < 2 ^ (prefixWord ++ tailWord_2084249).sum := by decide
  have hdescent : baseEnd_2084249 < baseStart_2084249 := by decide
  rcases family_descends (prefixWord ++ tailWord_2084249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2084335 : List Nat := [1, 1, 2, 1, 4, 1, 2, 4, 6]
def baseStart_2084335 : Nat := 118140960795 + 2084335 * 2 ^ 59
def prefixEnd_2084335 : Nat := 4983230072969 + 3 ^ 40 * 2084335 * 2
def baseEnd_2084335 : Nat := 237836822219823947428183

theorem tailTrace_2084335 : CollatzResearch.WordTrace tailWord_2084335 prefixEnd_2084335 237836822219823947428183 := by
  unfold tailWord_2084335
  simp only [CollatzResearch.WordTrace]
  refine ⟨76021942903817745922406459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50681295269211830614937639 76021942903817745922406459)
  ·
    refine ⟨114032914355726618883609689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76021942903817745922406459 114032914355726618883609689)
    ·
      refine ⟨85524685766794964162707267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114032914355726618883609689 85524685766794964162707267)
      ·
        refine ⟨128287028650192446244060901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85524685766794964162707267 128287028650192446244060901)
        ·
          refine ⟨24053817871911083670761419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 128287028650192446244060901 24053817871911083670761419)
          ·
            refine ⟨36080726807866625506142129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24053817871911083670761419 36080726807866625506142129)
            ·
              refine ⟨27060545105899969129606597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36080726807866625506142129 27060545105899969129606597)
              ·
                refine ⟨5073852207356244211801237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27060545105899969129606597 5073852207356244211801237)
                ·
                  refine ⟨237836822219823947428183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5073852207356244211801237 237836822219823947428183)
                  ·
                    rfl

theorem cell22_2084335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 4, 6].length) (baseStart_2084335 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2084335 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2084335 prefixEnd_2084335 := by exact prefixLift 2084335
  have htrace : WordTrace (prefixWord ++ tailWord_2084335) baseStart_2084335 baseEnd_2084335 := by
    simpa [prefixWord, tailWord_2084335, baseEnd_2084335] using wordTrace_append hprefix tailTrace_2084335
  have hstable : (prefixWord ++ tailWord_2084335).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2084335).length < 2 ^ (prefixWord ++ tailWord_2084335).sum := by decide
  have hdescent : baseEnd_2084335 < baseStart_2084335 := by decide
  rcases family_descends (prefixWord ++ tailWord_2084335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2084337 : List Nat := [1, 2, 2, 2, 3, 3, 1, 1, 3, 4]
def baseStart_2084337 : Nat := 118140960795 + 2084337 * 2 ^ 59
def prefixEnd_2084337 : Nat := 4983230072969 + 3 ^ 40 * 2084337 * 2
def baseEnd_2084337 : Nat := 713511151300344503734543

theorem tailTrace_2084337 : CollatzResearch.WordTrace tailWord_2084337 prefixEnd_2084337 713511151300344503734543 := by
  unfold tailWord_2084337
  simp only [CollatzResearch.WordTrace]
  refine ⟨76022015849810500263979265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50681343899873666842652843 76022015849810500263979265)
  ·
    refine ⟨57016511887357875197984449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76022015849810500263979265 57016511887357875197984449)
    ·
      refine ⟨42762383915518406398488337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57016511887357875197984449 42762383915518406398488337)
      ·
        refine ⟨32071787936638804798866253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42762383915518406398488337 32071787936638804798866253)
        ·
          refine ⟨12026920476239551799574845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32071787936638804798866253 12026920476239551799574845)
          ·
            refine ⟨4510095178589831924840567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12026920476239551799574845 4510095178589831924840567)
            ·
              refine ⟨6765142767884747887260851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4510095178589831924840567 6765142767884747887260851)
              ·
                refine ⟨10147714151827121830891277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6765142767884747887260851 10147714151827121830891277)
                ·
                  refine ⟨3805392806935170686584229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10147714151827121830891277 3805392806935170686584229)
                  ·
                    refine ⟨713511151300344503734543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3805392806935170686584229 713511151300344503734543)
                    ·
                      rfl

theorem cell22_2084337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 1, 1, 3, 4].length) (baseStart_2084337 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2084337 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2084337 prefixEnd_2084337 := by exact prefixLift 2084337
  have htrace : WordTrace (prefixWord ++ tailWord_2084337) baseStart_2084337 baseEnd_2084337 := by
    simpa [prefixWord, tailWord_2084337, baseEnd_2084337] using wordTrace_append hprefix tailTrace_2084337
  have hstable : (prefixWord ++ tailWord_2084337).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2084337).length < 2 ^ (prefixWord ++ tailWord_2084337).sum := by decide
  have hdescent : baseEnd_2084337 < baseStart_2084337 := by decide
  rcases family_descends (prefixWord ++ tailWord_2084337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2084384 : List Nat := [2, 1, 1, 6, 1, 2, 2, 1, 1, 5]
def baseStart_2084384 : Nat := 118140960795 + 2084384 * 2 ^ 59
def prefixEnd_2084384 : Nat := 4983230072969 + 3 ^ 40 * 2084384 * 2
def baseEnd_2084384 : Nat := 713527240360852047809399

theorem tailTrace_2084384 : CollatzResearch.WordTrace tailWord_2084384 prefixEnd_2084384 713527240360852047809399 := by
  unfold tailWord_2084384
  simp only [CollatzResearch.WordTrace]
  refine ⟨38011865040320113645470103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50682486720426818193960137 38011865040320113645470103)
  ·
    refine ⟨57017797560480170468205155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38011865040320113645470103 57017797560480170468205155)
    ·
      refine ⟨85526696340720255702307733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57017797560480170468205155 85526696340720255702307733)
      ·
        refine ⟨4009063890971261986045675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 85526696340720255702307733 4009063890971261986045675)
        ·
          refine ⟨6013595836456892979068513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4009063890971261986045675 6013595836456892979068513)
          ·
            refine ⟨4510196877342669734301385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6013595836456892979068513 4510196877342669734301385)
            ·
              refine ⟨3382647658007002300726039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4510196877342669734301385 3382647658007002300726039)
              ·
                refine ⟨5073971487010503451089059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3382647658007002300726039 5073971487010503451089059)
                ·
                  refine ⟨7610957230515755176633589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5073971487010503451089059 7610957230515755176633589)
                  ·
                    refine ⟨713527240360852047809399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7610957230515755176633589 713527240360852047809399)
                    ·
                      rfl

theorem cell22_2084384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 2, 1, 1, 5].length) (baseStart_2084384 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2084384 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2084384 prefixEnd_2084384 := by exact prefixLift 2084384
  have htrace : WordTrace (prefixWord ++ tailWord_2084384) baseStart_2084384 baseEnd_2084384 := by
    simpa [prefixWord, tailWord_2084384, baseEnd_2084384] using wordTrace_append hprefix tailTrace_2084384
  have hstable : (prefixWord ++ tailWord_2084384).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2084384).length < 2 ^ (prefixWord ++ tailWord_2084384).sum := by decide
  have hdescent : baseEnd_2084384 < baseStart_2084384 := by decide
  rcases family_descends (prefixWord ++ tailWord_2084384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2084442 : List Nat := [3, 1, 1, 2, 1, 1, 1, 7, 5]
def baseStart_2084442 : Nat := 118140960795 + 2084442 * 2 ^ 59
def prefixEnd_2084442 : Nat := 4983230072969 + 3 ^ 40 * 2084442 * 2
def baseEnd_2084442 : Nat := 237849031648719743286407

theorem tailTrace_2084442 : CollatzResearch.WordTrace tailWord_2084442 prefixEnd_2084442 237849031648719743286407 := by
  unfold tailWord_2084442
  simp only [CollatzResearch.WordTrace]
  refine ⟨19006461378607525799137895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50683897009620068797701053 19006461378607525799137895)
  ·
    refine ⟨28509692067911288698706843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19006461378607525799137895 28509692067911288698706843)
    ·
      refine ⟨42764538101866933048060265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28509692067911288698706843 42764538101866933048060265)
      ·
        refine ⟨32073403576400199786045199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42764538101866933048060265 32073403576400199786045199)
        ·
          refine ⟨48110105364600299679067799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32073403576400199786045199 48110105364600299679067799)
          ·
            refine ⟨72165158046900449518601699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48110105364600299679067799 72165158046900449518601699)
            ·
              refine ⟨108247737070350674277902549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72165158046900449518601699 108247737070350674277902549)
              ·
                refine ⟨2537056337586343928388341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 108247737070350674277902549 2537056337586343928388341)
                ·
                  refine ⟨237849031648719743286407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2537056337586343928388341 237849031648719743286407)
                  ·
                    rfl

theorem cell22_2084442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 7, 5].length) (baseStart_2084442 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2084442 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2084442 prefixEnd_2084442 := by exact prefixLift 2084442
  have htrace : WordTrace (prefixWord ++ tailWord_2084442) baseStart_2084442 baseEnd_2084442 := by
    simpa [prefixWord, tailWord_2084442, baseEnd_2084442] using wordTrace_append hprefix tailTrace_2084442
  have hstable : (prefixWord ++ tailWord_2084442).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2084442).length < 2 ^ (prefixWord ++ tailWord_2084442).sum := by decide
  have hdescent : baseEnd_2084442 < baseStart_2084442 := by decide
  rcases family_descends (prefixWord ++ tailWord_2084442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2084517 : List Nat := [1, 3, 1, 2, 1, 2, 2, 3, 1, 6]
def baseStart_2084517 : Nat := 118140960795 + 2084517 * 2 ^ 59
def prefixEnd_2084517 : Nat := 4983230072969 + 3 ^ 40 * 2084517 * 2
def baseEnd_2084517 : Nat := 713572768978884034233991

theorem tailTrace_2084517 : CollatzResearch.WordTrace tailWord_2084517 prefixEnd_2084517 713572768978884034233991 := by
  unfold tailWord_2084517
  simp only [CollatzResearch.WordTrace]
  refine ⟨76028580989158391005531805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50685720659438927337021203 76028580989158391005531805)
  ·
    refine ⟨28510717870934396627074427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76028580989158391005531805 28510717870934396627074427)
    ·
      refine ⟨42766076806401594940611641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28510717870934396627074427 42766076806401594940611641)
      ·
        refine ⟨32074557604801196205458731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42766076806401594940611641 32074557604801196205458731)
        ·
          refine ⟨48111836407201794308188097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32074557604801196205458731 48111836407201794308188097)
          ·
            refine ⟨36083877305401345731141073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48111836407201794308188097 36083877305401345731141073)
            ·
              refine ⟨27062907979051009298355805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36083877305401345731141073 27062907979051009298355805)
              ·
                refine ⟨10148590492144128486883427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27062907979051009298355805 10148590492144128486883427)
                ·
                  refine ⟨15222885738216192730325141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10148590492144128486883427 15222885738216192730325141)
                  ·
                    refine ⟨713572768978884034233991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15222885738216192730325141 713572768978884034233991)
                    ·
                      rfl

theorem cell22_2084517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 3, 1, 6].length) (baseStart_2084517 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2084517 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2084517 prefixEnd_2084517 := by exact prefixLift 2084517
  have htrace : WordTrace (prefixWord ++ tailWord_2084517) baseStart_2084517 baseEnd_2084517 := by
    simpa [prefixWord, tailWord_2084517, baseEnd_2084517] using wordTrace_append hprefix tailTrace_2084517
  have hstable : (prefixWord ++ tailWord_2084517).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2084517).length < 2 ^ (prefixWord ++ tailWord_2084517).sum := by decide
  have hdescent : baseEnd_2084517 < baseStart_2084517 := by decide
  rcases family_descends (prefixWord ++ tailWord_2084517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2084532 : List Nat := [2, 5, 15]
def baseStart_2084532 : Nat := 118140960795 + 2084532 * 2 ^ 59
def prefixEnd_2084532 : Nat := 4983230072969 + 3 ^ 40 * 2084532 * 2
def baseEnd_2084532 : Nat := 326281620386570185235

theorem tailTrace_2084532 : CollatzResearch.WordTrace tailWord_2084532 prefixEnd_2084532 326281620386570185235 := by
  unfold tailWord_2084532
  simp only [CollatzResearch.WordTrace]
  refine ⟨38014564042052024283663925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50686085389402699044885233 38014564042052024283663925)
  ·
    refine ⟨3563865378942377276593493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 38014564042052024283663925 3563865378942377276593493)
    ·
      refine ⟨326281620386570185235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 15 3563865378942377276593493 326281620386570185235)
      ·
        rfl

theorem cell22_2084532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 15].length) (baseStart_2084532 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2084532 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2084532 prefixEnd_2084532 := by exact prefixLift 2084532
  have htrace : WordTrace (prefixWord ++ tailWord_2084532) baseStart_2084532 baseEnd_2084532 := by
    simpa [prefixWord, tailWord_2084532, baseEnd_2084532] using wordTrace_append hprefix tailTrace_2084532
  have hstable : (prefixWord ++ tailWord_2084532).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2084532).length < 2 ^ (prefixWord ++ tailWord_2084532).sum := by decide
  have hdescent : baseEnd_2084532 < baseStart_2084532 := by decide
  rcases family_descends (prefixWord ++ tailWord_2084532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2084538 : List Nat := [3, 1, 1, 1, 2, 6, 2, 2, 4]
def baseStart_2084538 : Nat := 118140960795 + 2084538 * 2 ^ 59
def prefixEnd_2084538 : Nat := 4983230072969 + 3 ^ 40 * 2084538 * 2
def baseEnd_2084538 : Nat := 237859985902682326486309

theorem tailTrace_2084538 : CollatzResearch.WordTrace tailWord_2084538 prefixEnd_2084538 237859985902682326486309 := by
  unfold tailWord_2084538
  simp only [CollatzResearch.WordTrace]
  refine ⟨19007336730520577898011567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50686231281388207728030845 19007336730520577898011567)
  ·
    refine ⟨28511005095780866847017351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19007336730520577898011567 28511005095780866847017351)
    ·
      refine ⟨42766507643671300270526027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28511005095780866847017351 42766507643671300270526027)
      ·
        refine ⟨64149761465506950405789041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42766507643671300270526027 64149761465506950405789041)
        ·
          refine ⟨48112321099130212804341781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64149761465506950405789041 48112321099130212804341781)
          ·
            refine ⟨2255265051521728725203521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 48112321099130212804341781 2255265051521728725203521)
            ·
              refine ⟨1691448788641296543902641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2255265051521728725203521 1691448788641296543902641)
              ·
                refine ⟨1268586591480972407926981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1691448788641296543902641 1268586591480972407926981)
                ·
                  refine ⟨237859985902682326486309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1268586591480972407926981 237859985902682326486309)
                  ·
                    rfl

theorem cell22_2084538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 2, 2, 4].length) (baseStart_2084538 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2084538 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2084538 prefixEnd_2084538 := by exact prefixLift 2084538
  have htrace : WordTrace (prefixWord ++ tailWord_2084538) baseStart_2084538 baseEnd_2084538 := by
    simpa [prefixWord, tailWord_2084538, baseEnd_2084538] using wordTrace_append hprefix tailTrace_2084538
  have hstable : (prefixWord ++ tailWord_2084538).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2084538).length < 2 ^ (prefixWord ++ tailWord_2084538).sum := by decide
  have hdescent : baseEnd_2084538 < baseStart_2084538 := by decide
  rcases family_descends (prefixWord ++ tailWord_2084538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2084594 : List Nat := [3, 2, 1, 3, 1, 1, 3, 1, 7]
def baseStart_2084594 : Nat := 118140960795 + 2084594 * 2 ^ 59
def prefixEnd_2084594 : Nat := 4983230072969 + 3 ^ 40 * 2084594 * 2
def baseEnd_2084594 : Nat := 237866375884160500019585

theorem tailTrace_2084594 : CollatzResearch.WordTrace tailWord_2084594 prefixEnd_2084594 237866375884160500019585 := by
  unfold tailWord_2084594
  simp only [CollatzResearch.WordTrace]
  refine ⟨19007847352469858289021209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50687592939919622104056557 19007847352469858289021209)
  ·
    refine ⟨14255885514352393716765907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19007847352469858289021209 14255885514352393716765907)
    ·
      refine ⟨21383828271528590575148861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14255885514352393716765907 21383828271528590575148861)
      ·
        refine ⟨8018935601823221465680823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21383828271528590575148861 8018935601823221465680823)
        ·
          refine ⟨12028403402734832198521235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8018935601823221465680823 12028403402734832198521235)
          ·
            refine ⟨18042605104102248297781853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12028403402734832198521235 18042605104102248297781853)
            ·
              refine ⟨6765976914038343111668195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18042605104102248297781853 6765976914038343111668195)
              ·
                refine ⟨10148965371057514667502293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6765976914038343111668195 10148965371057514667502293)
                ·
                  refine ⟨237866375884160500019585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10148965371057514667502293 237866375884160500019585)
                  ·
                    rfl

theorem cell22_2084594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 3, 1, 7].length) (baseStart_2084594 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2084594 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2084594 prefixEnd_2084594 := by exact prefixLift 2084594
  have htrace : WordTrace (prefixWord ++ tailWord_2084594) baseStart_2084594 baseEnd_2084594 := by
    simpa [prefixWord, tailWord_2084594, baseEnd_2084594] using wordTrace_append hprefix tailTrace_2084594
  have hstable : (prefixWord ++ tailWord_2084594).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2084594).length < 2 ^ (prefixWord ++ tailWord_2084594).sum := by decide
  have hdescent : baseEnd_2084594 < baseStart_2084594 := by decide
  rcases family_descends (prefixWord ++ tailWord_2084594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2084598 : List Nat := [5, 1, 1, 1, 1, 4, 2, 1, 3, 3]
def baseStart_2084598 : Nat := 118140960795 + 2084598 * 2 ^ 59
def prefixEnd_2084598 : Nat := 4983230072969 + 3 ^ 40 * 2084598 * 2
def baseEnd_2084598 : Nat := 713600496934226822958743

theorem tailTrace_2084598 : CollatzResearch.WordTrace tailWord_2084598 prefixEnd_2084598 713600496934226822958743 := by
  unfold tailWord_2084598
  simp only [CollatzResearch.WordTrace]
  refine ⟨4751970956366558864951903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 50687690201243294559486965 4751970956366558864951903)
  ·
    refine ⟨7127956434549838297427855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4751970956366558864951903 7127956434549838297427855)
    ·
      refine ⟨10691934651824757446141783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7127956434549838297427855 10691934651824757446141783)
      ·
        refine ⟨16037901977737136169212675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10691934651824757446141783 16037901977737136169212675)
        ·
          refine ⟨24056852966605704253819013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16037901977737136169212675 24056852966605704253819013)
          ·
            refine ⟨4510659931238569547591065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24056852966605704253819013 4510659931238569547591065)
            ·
              refine ⟨3382994948428927160693299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4510659931238569547591065 3382994948428927160693299)
              ·
                refine ⟨5074492422643390741039949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3382994948428927160693299 5074492422643390741039949)
                ·
                  refine ⟨1902934658491271527889981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5074492422643390741039949 1902934658491271527889981)
                  ·
                    refine ⟨713600496934226822958743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1902934658491271527889981 713600496934226822958743)
                    ·
                      rfl

theorem cell22_2084598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 2, 1, 3, 3].length) (baseStart_2084598 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2084598 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2084598 prefixEnd_2084598 := by exact prefixLift 2084598
  have htrace : WordTrace (prefixWord ++ tailWord_2084598) baseStart_2084598 baseEnd_2084598 := by
    simpa [prefixWord, tailWord_2084598, baseEnd_2084598] using wordTrace_append hprefix tailTrace_2084598
  have hstable : (prefixWord ++ tailWord_2084598).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2084598).length < 2 ^ (prefixWord ++ tailWord_2084598).sum := by decide
  have hdescent : baseEnd_2084598 < baseStart_2084598 := by decide
  rcases family_descends (prefixWord ++ tailWord_2084598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2084609 : List Nat := [1, 2, 4, 1, 1, 1, 4, 1, 2, 5]
def baseStart_2084609 : Nat := 118140960795 + 2084609 * 2 ^ 59
def prefixEnd_2084609 : Nat := 4983230072969 + 3 ^ 40 * 2084609 * 2
def baseEnd_2084609 : Nat := 713604262459026460933709

theorem tailTrace_2084609 : CollatzResearch.WordTrace tailWord_2084609 prefixEnd_2084609 713604262459026460933709 := by
  unfold tailWord_2084609
  simp only [CollatzResearch.WordTrace]
  refine ⟨76031936504825090717880881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50687957669883393811920587 76031936504825090717880881)
  ·
    refine ⟨57023952378618818038410661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76031936504825090717880881 57023952378618818038410661)
    ·
      refine ⟨10691991070991028382201999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57023952378618818038410661 10691991070991028382201999)
      ·
        refine ⟨16037986606486542573302999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10691991070991028382201999 16037986606486542573302999)
        ·
          refine ⟨24056979909729813859954499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16037986606486542573302999 24056979909729813859954499)
          ·
            refine ⟨36085469864594720789931749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24056979909729813859954499 36085469864594720789931749)
            ·
              refine ⟨6766025599611510148112203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36085469864594720789931749 6766025599611510148112203)
              ·
                refine ⟨10149038399417265222168305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6766025599611510148112203 10149038399417265222168305)
                ·
                  refine ⟨7611778799562948916626229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10149038399417265222168305 7611778799562948916626229)
                  ·
                    refine ⟨713604262459026460933709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7611778799562948916626229 713604262459026460933709)
                    ·
                      rfl

theorem cell22_2084609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 4, 1, 2, 5].length) (baseStart_2084609 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2084609 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2084609 prefixEnd_2084609 := by exact prefixLift 2084609
  have htrace : WordTrace (prefixWord ++ tailWord_2084609) baseStart_2084609 baseEnd_2084609 := by
    simpa [prefixWord, tailWord_2084609, baseEnd_2084609] using wordTrace_append hprefix tailTrace_2084609
  have hstable : (prefixWord ++ tailWord_2084609).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2084609).length < 2 ^ (prefixWord ++ tailWord_2084609).sum := by decide
  have hdescent : baseEnd_2084609 < baseStart_2084609 := by decide
  rcases family_descends (prefixWord ++ tailWord_2084609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2084641 : List Nat := [1, 2, 3, 2, 1, 3, 2, 3, 1, 4]
def baseStart_2084641 : Nat := 118140960795 + 2084641 * 2 ^ 59
def prefixEnd_2084641 : Nat := 4983230072969 + 3 ^ 40 * 2084641 * 2
def baseEnd_2084641 : Nat := 713615216712989044133611

theorem tailTrace_2084641 : CollatzResearch.WordTrace tailWord_2084641 prefixEnd_2084641 713615216712989044133611 := by
  unfold tailWord_2084641
  simp only [CollatzResearch.WordTrace]
  refine ⟨76033103640709160183045777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50688735760472773455363851 76033103640709160183045777)
  ·
    refine ⟨57024827730531870137284333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76033103640709160183045777 57024827730531870137284333)
    ·
      refine ⟨21384310398949451301481625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57024827730531870137284333 21384310398949451301481625)
      ·
        refine ⟨16038232799212088476111219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21384310398949451301481625 16038232799212088476111219)
        ·
          refine ⟨24057349198818132714166829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16038232799212088476111219 24057349198818132714166829)
          ·
            refine ⟨9021505949556799767812561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24057349198818132714166829 9021505949556799767812561)
            ·
              refine ⟨6766129462167599825859421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9021505949556799767812561 6766129462167599825859421)
              ·
                refine ⟨2537298548312849934697283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6766129462167599825859421 2537298548312849934697283)
                ·
                  refine ⟨3805947822469274902045925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2537298548312849934697283 3805947822469274902045925)
                  ·
                    refine ⟨713615216712989044133611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3805947822469274902045925 713615216712989044133611)
                    ·
                      rfl

theorem cell22_2084641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 2, 3, 1, 4].length) (baseStart_2084641 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2084641 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2084641 prefixEnd_2084641 := by exact prefixLift 2084641
  have htrace : WordTrace (prefixWord ++ tailWord_2084641) baseStart_2084641 baseEnd_2084641 := by
    simpa [prefixWord, tailWord_2084641, baseEnd_2084641] using wordTrace_append hprefix tailTrace_2084641
  have hstable : (prefixWord ++ tailWord_2084641).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2084641).length < 2 ^ (prefixWord ++ tailWord_2084641).sum := by decide
  have hdescent : baseEnd_2084641 < baseStart_2084641 := by decide
  rcases family_descends (prefixWord ++ tailWord_2084641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2084707 : List Nat := [1, 1, 1, 5, 5, 1, 2, 2, 4]
def baseStart_2084707 : Nat := 118140960795 + 2084707 * 2 ^ 59
def prefixEnd_2084707 : Nat := 4983230072969 + 3 ^ 40 * 2084707 * 2
def baseEnd_2084707 : Nat := 237879269953928957327803

theorem tailTrace_2084707 : CollatzResearch.WordTrace tailWord_2084707 prefixEnd_2084707 237879269953928957327803 := by
  unfold tailWord_2084707
  simp only [CollatzResearch.WordTrace]
  refine ⟨76035510858470053454948375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50690340572313368969965583 76035510858470053454948375)
  ·
    refine ⟨114053266287705080182422563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76035510858470053454948375 114053266287705080182422563)
    ·
      refine ⟨171079899431557620273633845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114053266287705080182422563 171079899431557620273633845)
      ·
        refine ⟨16038740571708526900653173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 171079899431557620273633845 16038740571708526900653173)
        ·
          refine ⟨1503631928597674396936235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16038740571708526900653173 1503631928597674396936235)
          ·
            refine ⟨2255447892896511595404353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1503631928597674396936235 2255447892896511595404353)
            ·
              refine ⟨1691585919672383696553265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2255447892896511595404353 1691585919672383696553265)
              ·
                refine ⟨1268689439754287772414949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1691585919672383696553265 1268689439754287772414949)
                ·
                  refine ⟨237879269953928957327803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1268689439754287772414949 237879269953928957327803)
                  ·
                    rfl

theorem cell22_2084707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 2, 2, 4].length) (baseStart_2084707 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2084707 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2084707 prefixEnd_2084707 := by exact prefixLift 2084707
  have htrace : WordTrace (prefixWord ++ tailWord_2084707) baseStart_2084707 baseEnd_2084707 := by
    simpa [prefixWord, tailWord_2084707, baseEnd_2084707] using wordTrace_append hprefix tailTrace_2084707
  have hstable : (prefixWord ++ tailWord_2084707).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2084707).length < 2 ^ (prefixWord ++ tailWord_2084707).sum := by decide
  have hdescent : baseEnd_2084707 < baseStart_2084707 := by decide
  rcases family_descends (prefixWord ++ tailWord_2084707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2084718 : List Nat := [4, 1, 2, 3, 1, 3, 1, 7]
def baseStart_2084718 : Nat := 118140960795 + 2084718 * 2 ^ 59
def prefixEnd_2084718 : Nat := 4983230072969 + 3 ^ 40 * 2084718 * 2
def baseEnd_2084718 : Nat := 79293508376287389995375

theorem tailTrace_2084718 : CollatzResearch.WordTrace tailWord_2084718 prefixEnd_2084718 79293508376287389995375 := by
  unfold tailWord_2084718
  simp only [CollatzResearch.WordTrace]
  refine ⟨9504489007678775291699851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50690608040953468222399205 9504489007678775291699851)
  ·
    refine ⟨14256733511518162937549777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9504489007678775291699851 14256733511518162937549777)
    ·
      refine ⟨10692550133638622203162333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14256733511518162937549777 10692550133638622203162333)
      ·
        refine ⟨4009706300114483326185875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10692550133638622203162333 4009706300114483326185875)
        ·
          refine ⟨6014559450171724989278813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4009706300114483326185875 6014559450171724989278813)
          ·
            refine ⟨2255459793814396870979555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6014559450171724989278813 2255459793814396870979555)
            ·
              refine ⟨3383189690721595306469333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2255459793814396870979555 3383189690721595306469333)
              ·
                refine ⟨79293508376287389995375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3383189690721595306469333 79293508376287389995375)
                ·
                  rfl

theorem cell22_2084718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 1, 7].length) (baseStart_2084718 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2084718 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2084718 prefixEnd_2084718 := by exact prefixLift 2084718
  have htrace : WordTrace (prefixWord ++ tailWord_2084718) baseStart_2084718 baseEnd_2084718 := by
    simpa [prefixWord, tailWord_2084718, baseEnd_2084718] using wordTrace_append hprefix tailTrace_2084718
  have hstable : (prefixWord ++ tailWord_2084718).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2084718).length < 2 ^ (prefixWord ++ tailWord_2084718).sum := by decide
  have hdescent : baseEnd_2084718 < baseStart_2084718 := by decide
  rcases family_descends (prefixWord ++ tailWord_2084718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2084737 : List Nat := [1, 2, 4, 4, 2, 1, 1, 1, 2, 4]
def baseStart_2084737 : Nat := 118140960795 + 2084737 * 2 ^ 59
def prefixEnd_2084737 : Nat := 4983230072969 + 3 ^ 40 * 2084737 * 2
def baseEnd_2084737 : Nat := 713648079474876793733317

theorem tailTrace_2084737 : CollatzResearch.WordTrace tailWord_2084737 prefixEnd_2084737 713648079474876793733317 := by
  unfold tailWord_2084737
  simp only [CollatzResearch.WordTrace]
  refine ⟨76036605048361368578540465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50691070032240912385693643 76036605048361368578540465)
  ·
    refine ⟨57027453786271026433905349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76036605048361368578540465 57027453786271026433905349)
    ·
      refine ⟨10692647584925817456357253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57027453786271026433905349 10692647584925817456357253)
      ·
        refine ⟨2004871422173590773066985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10692647584925817456357253 2004871422173590773066985)
        ·
          refine ⟨1503653566630193079800239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2004871422173590773066985 1503653566630193079800239)
          ·
            refine ⟨2255480349945289619700359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1503653566630193079800239 2255480349945289619700359)
            ·
              refine ⟨3383220524917934429550539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2255480349945289619700359 3383220524917934429550539)
              ·
                refine ⟨5074830787376901644325809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3383220524917934429550539 5074830787376901644325809)
                ·
                  refine ⟨3806123090532676233244357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5074830787376901644325809 3806123090532676233244357)
                  ·
                    refine ⟨713648079474876793733317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3806123090532676233244357 713648079474876793733317)
                    ·
                      rfl

theorem cell22_2084737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 1, 1, 2, 4].length) (baseStart_2084737 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2084737 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2084737 prefixEnd_2084737 := by exact prefixLift 2084737
  have htrace : WordTrace (prefixWord ++ tailWord_2084737) baseStart_2084737 baseEnd_2084737 := by
    simpa [prefixWord, tailWord_2084737, baseEnd_2084737] using wordTrace_append hprefix tailTrace_2084737
  have hstable : (prefixWord ++ tailWord_2084737).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2084737).length < 2 ^ (prefixWord ++ tailWord_2084737).sum := by decide
  have hdescent : baseEnd_2084737 < baseStart_2084737 := by decide
  rcases family_descends (prefixWord ++ tailWord_2084737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2084793 : List Nat := [1, 2, 1, 4, 2, 1, 4, 2, 1, 4]
def baseStart_2084793 : Nat := 118140960795 + 2084793 * 2 ^ 59
def prefixEnd_2084793 : Nat := 4983230072969 + 3 ^ 40 * 2084793 * 2
def baseEnd_2084793 : Nat := 713667249419311314333145

theorem tailTrace_2084793 : CollatzResearch.WordTrace tailWord_2084793 prefixEnd_2084793 713667249419311314333145 := by
  unfold tailWord_2084793
  simp only [CollatzResearch.WordTrace]
  refine ⟨76038647536158490142579033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50692431690772326761719355 76038647536158490142579033)
  ·
    refine ⟨57028985652118867606934275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76038647536158490142579033 57028985652118867606934275)
    ·
      refine ⟨85543478478178301410401413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57028985652118867606934275 85543478478178301410401413)
      ·
        refine ⟨16039402214658431514450265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85543478478178301410401413 16039402214658431514450265)
        ·
          refine ⟨12029551660993823635837699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16039402214658431514450265 12029551660993823635837699)
          ·
            refine ⟨18044327491490735453756549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12029551660993823635837699 18044327491490735453756549)
            ·
              refine ⟨3383311404654512897579353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18044327491490735453756549 3383311404654512897579353)
              ·
                refine ⟨2537483553490884673184515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3383311404654512897579353 2537483553490884673184515)
                ·
                  refine ⟨3806225330236327009776773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2537483553490884673184515 3806225330236327009776773)
                  ·
                    refine ⟨713667249419311314333145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3806225330236327009776773 713667249419311314333145)
                    ·
                      rfl

theorem cell22_2084793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 4, 2, 1, 4].length) (baseStart_2084793 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2084793 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2084793 prefixEnd_2084793 := by exact prefixLift 2084793
  have htrace : WordTrace (prefixWord ++ tailWord_2084793) baseStart_2084793 baseEnd_2084793 := by
    simpa [prefixWord, tailWord_2084793, baseEnd_2084793] using wordTrace_append hprefix tailTrace_2084793
  have hstable : (prefixWord ++ tailWord_2084793).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2084793).length < 2 ^ (prefixWord ++ tailWord_2084793).sum := by decide
  have hdescent : baseEnd_2084793 < baseStart_2084793 := by decide
  rcases family_descends (prefixWord ++ tailWord_2084793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2084823 : List Nat := [1, 1, 3, 2, 1, 1, 4, 4, 2, 3]
def baseStart_2084823 : Nat := 118140960795 + 2084823 * 2 ^ 59
def prefixEnd_2084823 : Nat := 4983230072969 + 3 ^ 40 * 2084823 * 2
def baseEnd_2084823 : Nat := 713677519032401236083053

theorem tailTrace_2084823 : CollatzResearch.WordTrace tailWord_2084823 prefixEnd_2084823 713677519032401236083053 := by
  unfold tailWord_2084823
  simp only [CollatzResearch.WordTrace]
  refine ⟨76039741726049805266171123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50693161150699870177447415 76039741726049805266171123)
  ·
    refine ⟨114059612589074707899256685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76039741726049805266171123 114059612589074707899256685)
    ·
      refine ⟨42772354720903015462221257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114059612589074707899256685 42772354720903015462221257)
      ·
        refine ⟨32079266040677261596665943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42772354720903015462221257 32079266040677261596665943)
        ·
          refine ⟨48118899061015892394998915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32079266040677261596665943 48118899061015892394998915)
          ·
            refine ⟨72178348591523838592498373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48118899061015892394998915 72178348591523838592498373)
            ·
              refine ⟨13533440360910719736093445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 72178348591523838592498373 13533440360910719736093445)
              ·
                refine ⟨2537520067670759950517521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13533440360910719736093445 2537520067670759950517521)
                ·
                  refine ⟨1903140050753069962888141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2537520067670759950517521 1903140050753069962888141)
                  ·
                    refine ⟨713677519032401236083053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1903140050753069962888141 713677519032401236083053)
                    ·
                      rfl

theorem cell22_2084823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 4, 2, 3].length) (baseStart_2084823 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2084823 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2084823 prefixEnd_2084823 := by exact prefixLift 2084823
  have htrace : WordTrace (prefixWord ++ tailWord_2084823) baseStart_2084823 baseEnd_2084823 := by
    simpa [prefixWord, tailWord_2084823, baseEnd_2084823] using wordTrace_append hprefix tailTrace_2084823
  have hstable : (prefixWord ++ tailWord_2084823).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2084823).length < 2 ^ (prefixWord ++ tailWord_2084823).sum := by decide
  have hdescent : baseEnd_2084823 < baseStart_2084823 := by decide
  rcases family_descends (prefixWord ++ tailWord_2084823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2084825 : List Nat := [1, 2, 1, 2, 7, 1, 1, 1, 6]
def baseStart_2084825 : Nat := 118140960795 + 2084825 * 2 ^ 59
def prefixEnd_2084825 : Nat := 4983230072969 + 3 ^ 40 * 2084825 * 2
def baseEnd_2084825 : Nat := 237892734557757965844349

theorem tailTrace_2084825 : CollatzResearch.WordTrace tailWord_2084825 prefixEnd_2084825 237892734557757965844349 := by
  unfold tailWord_2084825
  simp only [CollatzResearch.WordTrace]
  refine ⟨76039814672042559607743929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50693209781361706405162619 76039814672042559607743929)
  ·
    refine ⟨57029861004031919705807947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76039814672042559607743929 57029861004031919705807947)
    ·
      refine ⟨85544791506047879558711921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57029861004031919705807947 85544791506047879558711921)
      ·
        refine ⟨64158593629535909669033941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85544791506047879558711921 64158593629535909669033941)
        ·
          refine ⟨1503717038192247882867983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 64158593629535909669033941 1503717038192247882867983)
          ·
            refine ⟨2255575557288371824301975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1503717038192247882867983 2255575557288371824301975)
            ·
              refine ⟨3383363335932557736452963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2255575557288371824301975 3383363335932557736452963)
              ·
                refine ⟨5075045003898836604679445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3383363335932557736452963 5075045003898836604679445)
                ·
                  refine ⟨237892734557757965844349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5075045003898836604679445 237892734557757965844349)
                  ·
                    rfl

theorem cell22_2084825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 1, 1, 6].length) (baseStart_2084825 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2084825 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2084825 prefixEnd_2084825 := by exact prefixLift 2084825
  have htrace : WordTrace (prefixWord ++ tailWord_2084825) baseStart_2084825 baseEnd_2084825 := by
    simpa [prefixWord, tailWord_2084825, baseEnd_2084825] using wordTrace_append hprefix tailTrace_2084825
  have hstable : (prefixWord ++ tailWord_2084825).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2084825).length < 2 ^ (prefixWord ++ tailWord_2084825).sum := by decide
  have hdescent : baseEnd_2084825 < baseStart_2084825 := by decide
  rcases family_descends (prefixWord ++ tailWord_2084825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2084836 : List Nat := [2, 3, 1, 1, 1, 1, 6, 7]
def baseStart_2084836 : Nat := 118140960795 + 2084836 * 2 ^ 59
def prefixEnd_2084836 : Nat := 4983230072969 + 3 ^ 40 * 2084836 * 2
def baseEnd_2084836 : Nat := 79297996577563726167557

theorem tailTrace_2084836 : CollatzResearch.WordTrace tailWord_2084836 prefixEnd_2084836 79297996577563726167557 := by
  unfold tailWord_2084836
  simp only [CollatzResearch.WordTrace]
  refine ⟨38020107937501354243197181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50693477250001805657596241 38020107937501354243197181)
  ·
    refine ⟨14257540476563007841198943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38020107937501354243197181 14257540476563007841198943)
    ·
      refine ⟨21386310714844511761798415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14257540476563007841198943 21386310714844511761798415)
      ·
        refine ⟨32079466072266767642697623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21386310714844511761798415 32079466072266767642697623)
        ·
          refine ⟨48119199108400151464046435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32079466072266767642697623 48119199108400151464046435)
          ·
            refine ⟨72178798662600227196069653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48119199108400151464046435 72178798662600227196069653)
            ·
              refine ⟨3383381187309385649815765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 72178798662600227196069653 3383381187309385649815765)
              ·
                refine ⟨79297996577563726167557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3383381187309385649815765 79297996577563726167557)
                ·
                  rfl

theorem cell22_2084836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 6, 7].length) (baseStart_2084836 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2084836 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2084836 prefixEnd_2084836 := by exact prefixLift 2084836
  have htrace : WordTrace (prefixWord ++ tailWord_2084836) baseStart_2084836 baseEnd_2084836 := by
    simpa [prefixWord, tailWord_2084836, baseEnd_2084836] using wordTrace_append hprefix tailTrace_2084836
  have hstable : (prefixWord ++ tailWord_2084836).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2084836).length < 2 ^ (prefixWord ++ tailWord_2084836).sum := by decide
  have hdescent : baseEnd_2084836 < baseStart_2084836 := by decide
  rcases family_descends (prefixWord ++ tailWord_2084836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2084898 : List Nat := [3, 3, 1, 1, 1, 2, 1, 5, 5]
def baseStart_2084898 : Nat := 118140960795 + 2084898 * 2 ^ 59
def prefixEnd_2084898 : Nat := 4983230072969 + 3 ^ 40 * 2084898 * 2
def baseEnd_2084898 : Nat := 237901064355042013485941

theorem tailTrace_2084898 : CollatzResearch.WordTrace tailWord_2084898 prefixEnd_2084898 237901064355042013485941 := by
  unfold tailWord_2084898
  simp only [CollatzResearch.WordTrace]
  refine ⟨19010619300194523268787837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50694984800518728716767565 19010619300194523268787837)
  ·
    refine ⟨7128982237572946225795439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19010619300194523268787837 7128982237572946225795439)
    ·
      refine ⟨10693473356359419338693159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7128982237572946225795439 10693473356359419338693159)
      ·
        refine ⟨16040210034539129008039739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10693473356359419338693159 16040210034539129008039739)
        ·
          refine ⟨24060315051808693512059609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16040210034539129008039739 24060315051808693512059609)
          ·
            refine ⟨18045236288856520134044707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24060315051808693512059609 18045236288856520134044707)
            ·
              refine ⟨27067854433284780201067061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18045236288856520134044707 27067854433284780201067061)
              ·
                refine ⟨2537611353120448143850037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27067854433284780201067061 2537611353120448143850037)
                ·
                  refine ⟨237901064355042013485941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2537611353120448143850037 237901064355042013485941)
                  ·
                    rfl

theorem cell22_2084898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 5, 5].length) (baseStart_2084898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2084898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2084898 prefixEnd_2084898 := by exact prefixLift 2084898
  have htrace : WordTrace (prefixWord ++ tailWord_2084898) baseStart_2084898 baseEnd_2084898 := by
    simpa [prefixWord, tailWord_2084898, baseEnd_2084898] using wordTrace_append hprefix tailTrace_2084898
  have hstable : (prefixWord ++ tailWord_2084898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2084898).length < 2 ^ (prefixWord ++ tailWord_2084898).sum := by decide
  have hdescent : baseEnd_2084898 < baseStart_2084898 := by decide
  rcases family_descends (prefixWord ++ tailWord_2084898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2084973 : List Nat := [1, 5, 1, 1, 2, 1, 1, 3, 1, 6]
def baseStart_2084973 : Nat := 118140960795 + 2084973 * 2 ^ 59
def prefixEnd_2084973 : Nat := 4983230072969 + 3 ^ 40 * 2084973 * 2
def baseEnd_2084973 : Nat := 713728867097850844832593

theorem tailTrace_2084973 : CollatzResearch.WordTrace tailWord_2084973 prefixEnd_2084973 713728867097850844832593 := by
  unfold tailWord_2084973
  simp only [CollatzResearch.WordTrace]
  refine ⟨76045212675506380884131573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50696808450337587256087715 76045212675506380884131573)
  ·
    refine ⟨7129238688328723207887335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 76045212675506380884131573 7129238688328723207887335)
    ·
      refine ⟨10693858032493084811831003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7129238688328723207887335 10693858032493084811831003)
      ·
        refine ⟨16040787048739627217746505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10693858032493084811831003 16040787048739627217746505)
        ·
          refine ⟨12030590286554720413309879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16040787048739627217746505 12030590286554720413309879)
          ·
            refine ⟨18045885429832080619964819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12030590286554720413309879 18045885429832080619964819)
            ·
              refine ⟨27068828144748120929947229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18045885429832080619964819 27068828144748120929947229)
              ·
                refine ⟨10150810554280545348730211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27068828144748120929947229 10150810554280545348730211)
                ·
                  refine ⟨15226215831420818023095317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10150810554280545348730211 15226215831420818023095317)
                  ·
                    refine ⟨713728867097850844832593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15226215831420818023095317 713728867097850844832593)
                    ·
                      rfl

theorem cell22_2084973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 3, 1, 6].length) (baseStart_2084973 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2084973 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2084973 prefixEnd_2084973 := by exact prefixLift 2084973
  have htrace : WordTrace (prefixWord ++ tailWord_2084973) baseStart_2084973 baseEnd_2084973 := by
    simpa [prefixWord, tailWord_2084973, baseEnd_2084973] using wordTrace_append hprefix tailTrace_2084973
  have hstable : (prefixWord ++ tailWord_2084973).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2084973).length < 2 ^ (prefixWord ++ tailWord_2084973).sum := by decide
  have hdescent : baseEnd_2084973 < baseStart_2084973 := by decide
  rcases family_descends (prefixWord ++ tailWord_2084973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2084988 : List Nat := [2, 2, 2, 1, 1, 6, 8]
def baseStart_2084988 : Nat := 118140960795 + 2084988 * 2 ^ 59
def prefixEnd_2084988 : Nat := 4983230072969 + 3 ^ 40 * 2084988 * 2
def baseEnd_2084988 : Nat := 26434592663125770581761

theorem tailTrace_2084988 : CollatzResearch.WordTrace tailWord_2084988 prefixEnd_2084988 26434592663125770581761 := by
  unfold tailWord_2084988
  simp only [CollatzResearch.WordTrace]
  refine ⟨38022879885226019222963809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50697173180301358963951745 38022879885226019222963809)
  ·
    refine ⟨28517159913919514417222857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38022879885226019222963809 28517159913919514417222857)
    ·
      refine ⟨21387869935439635812917143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28517159913919514417222857 21387869935439635812917143)
      ·
        refine ⟨32081804903159453719375715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21387869935439635812917143 32081804903159453719375715)
        ·
          refine ⟨48122707354739180579063573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32081804903159453719375715 48122707354739180579063573)
          ·
            refine ⟨2255751907253399089643605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 48122707354739180579063573 2255751907253399089643605)
            ·
              refine ⟨26434592663125770581761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2255751907253399089643605 26434592663125770581761)
              ·
                rfl

theorem cell22_2084988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 8].length) (baseStart_2084988 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2084988 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2084988 prefixEnd_2084988 := by exact prefixLift 2084988
  have htrace : WordTrace (prefixWord ++ tailWord_2084988) baseStart_2084988 baseEnd_2084988 := by
    simpa [prefixWord, tailWord_2084988, baseEnd_2084988] using wordTrace_append hprefix tailTrace_2084988
  have hstable : (prefixWord ++ tailWord_2084988).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2084988).length < 2 ^ (prefixWord ++ tailWord_2084988).sum := by decide
  have hdescent : baseEnd_2084988 < baseStart_2084988 := by decide
  rcases family_descends (prefixWord ++ tailWord_2084988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2085020 : List Nat := [2, 2, 3, 2, 1, 1, 2, 1, 5, 3]
def baseStart_2085020 : Nat := 118140960795 + 2085020 * 2 ^ 59
def prefixEnd_2085020 : Nat := 4983230072969 + 3 ^ 40 * 2085020 * 2
def baseEnd_2085020 : Nat := 713744956158358388907449

theorem tailTrace_2085020 : CollatzResearch.WordTrace tailWord_2085020 prefixEnd_2085020 713744956158358388907449 := by
  unfold tailWord_2085020
  simp only [CollatzResearch.WordTrace]
  refine ⟨38023463453168053955546257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50697951270890738607395009 38023463453168053955546257)
  ·
    refine ⟨28517597589876040466659693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38023463453168053955546257 28517597589876040466659693)
    ·
      refine ⟨10694099096203515174997385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28517597589876040466659693 10694099096203515174997385)
      ·
        refine ⟨8020574322152636381248039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10694099096203515174997385 8020574322152636381248039)
        ·
          refine ⟨12030861483228954571872059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8020574322152636381248039 12030861483228954571872059)
          ·
            refine ⟨18046292224843431857808089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12030861483228954571872059 18046292224843431857808089)
            ·
              refine ⟨13534719168632573893356067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18046292224843431857808089 13534719168632573893356067)
              ·
                refine ⟨20302078752948860840034101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13534719168632573893356067 20302078752948860840034101)
                ·
                  refine ⟨1903319883088955703753197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20302078752948860840034101 1903319883088955703753197)
                  ·
                    refine ⟨713744956158358388907449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1903319883088955703753197 713744956158358388907449)
                    ·
                      rfl

theorem cell22_2085020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 1, 5, 3].length) (baseStart_2085020 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2085020 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2085020 prefixEnd_2085020 := by exact prefixLift 2085020
  have htrace : WordTrace (prefixWord ++ tailWord_2085020) baseStart_2085020 baseEnd_2085020 := by
    simpa [prefixWord, tailWord_2085020, baseEnd_2085020] using wordTrace_append hprefix tailTrace_2085020
  have hstable : (prefixWord ++ tailWord_2085020).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2085020).length < 2 ^ (prefixWord ++ tailWord_2085020).sum := by decide
  have hdescent : baseEnd_2085020 < baseStart_2085020 := by decide
  rcases family_descends (prefixWord ++ tailWord_2085020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2085048 : List Nat := [2, 1, 2, 1, 2, 1, 4, 2, 2, 5]
def baseStart_2085048 : Nat := 118140960795 + 2085048 * 2 ^ 59
def prefixEnd_2085048 : Nat := 4983230072969 + 3 ^ 40 * 2085048 * 2
def baseEnd_2085048 : Nat := 713754541130575649207363

theorem tailTrace_2085048 : CollatzResearch.WordTrace tailWord_2085048 prefixEnd_2085048 713754541130575649207363 := by
  unfold tailWord_2085048
  simp only [CollatzResearch.WordTrace]
  refine ⟨38023974075117334346555899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50698632100156445795407865 38023974075117334346555899)
  ·
    refine ⟨57035961112676001519833849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38023974075117334346555899 57035961112676001519833849)
    ·
      refine ⟨42776970834507001139875387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57035961112676001519833849 42776970834507001139875387)
      ·
        refine ⟨64165456251760501709813081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42776970834507001139875387 64165456251760501709813081)
        ·
          refine ⟨48124092188820376282359811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64165456251760501709813081 48124092188820376282359811)
          ·
            refine ⟨72186138283230564423539717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48124092188820376282359811 72186138283230564423539717)
            ·
              refine ⟨13534900928105730829413697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 72186138283230564423539717 13534900928105730829413697)
              ·
                refine ⟨10151175696079298122060273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13534900928105730829413697 10151175696079298122060273)
                ·
                  refine ⟨7613381772059473591545205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10151175696079298122060273 7613381772059473591545205)
                  ·
                    refine ⟨713754541130575649207363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7613381772059473591545205 713754541130575649207363)
                    ·
                      rfl

theorem cell22_2085048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 2, 2, 5].length) (baseStart_2085048 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2085048 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2085048 prefixEnd_2085048 := by exact prefixLift 2085048
  have htrace : WordTrace (prefixWord ++ tailWord_2085048) baseStart_2085048 baseEnd_2085048 := by
    simpa [prefixWord, tailWord_2085048, baseEnd_2085048] using wordTrace_append hprefix tailTrace_2085048
  have hstable : (prefixWord ++ tailWord_2085048).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2085048).length < 2 ^ (prefixWord ++ tailWord_2085048).sum := by decide
  have hdescent : baseEnd_2085048 < baseStart_2085048 := by decide
  rcases family_descends (prefixWord ++ tailWord_2085048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2085080 : List Nat := [2, 1, 2, 2, 4, 1, 2, 1, 3, 4]
def baseStart_2085080 : Nat := 118140960795 + 2085080 * 2 ^ 59
def prefixEnd_2085080 : Nat := 4983230072969 + 3 ^ 40 * 2085080 * 2
def baseEnd_2085080 : Nat := 713765495384538232407265

theorem tailTrace_2085080 : CollatzResearch.WordTrace tailWord_2085080 prefixEnd_2085080 713765495384538232407265 := by
  unfold tailWord_2085080
  simp only [CollatzResearch.WordTrace]
  refine ⟨38024557643059369079138347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50699410190745825438851129 38024557643059369079138347)
  ·
    refine ⟨57036836464589053618707521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38024557643059369079138347 57036836464589053618707521)
    ·
      refine ⟨42777627348441790214030641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57036836464589053618707521 42777627348441790214030641)
      ·
        refine ⟨32083220511331342660522981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42777627348441790214030641 32083220511331342660522981)
        ·
          refine ⟨6015603845874626748848059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32083220511331342660522981 6015603845874626748848059)
          ·
            refine ⟨9023405768811940123272089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6015603845874626748848059 9023405768811940123272089)
            ·
              refine ⟨6767554326608955092454067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9023405768811940123272089 6767554326608955092454067)
              ·
                refine ⟨10151331489913432638681101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6767554326608955092454067 10151331489913432638681101)
                ·
                  refine ⟨3806749308717537239505413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10151331489913432638681101 3806749308717537239505413)
                  ·
                    refine ⟨713765495384538232407265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3806749308717537239505413 713765495384538232407265)
                    ·
                      rfl

theorem cell22_2085080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 2, 1, 3, 4].length) (baseStart_2085080 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2085080 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2085080 prefixEnd_2085080 := by exact prefixLift 2085080
  have htrace : WordTrace (prefixWord ++ tailWord_2085080) baseStart_2085080 baseEnd_2085080 := by
    simpa [prefixWord, tailWord_2085080, baseEnd_2085080] using wordTrace_append hprefix tailTrace_2085080
  have hstable : (prefixWord ++ tailWord_2085080).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2085080).length < 2 ^ (prefixWord ++ tailWord_2085080).sum := by decide
  have hdescent : baseEnd_2085080 < baseStart_2085080 := by decide
  rcases family_descends (prefixWord ++ tailWord_2085080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2085110 : List Nat := [5, 1, 1, 1, 1, 1, 2, 2, 3, 5]
def baseStart_2085110 : Nat := 118140960795 + 2085110 * 2 ^ 59
def prefixEnd_2085110 : Nat := 4983230072969 + 3 ^ 40 * 2085110 * 2
def baseEnd_2085110 : Nat := 713775764997628154157173

theorem tailTrace_2085110 : CollatzResearch.WordTrace tailWord_2085110 prefixEnd_2085110 713775764997628154157173 := by
  unfold tailWord_2085110
  simp only [CollatzResearch.WordTrace]
  refine ⟨4753138092250628330116799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 50700139650673368854579189 4753138092250628330116799)
  ·
    refine ⟨7129707138375942495175199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4753138092250628330116799 7129707138375942495175199)
    ·
      refine ⟨10694560707563913742762799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7129707138375942495175199 10694560707563913742762799)
      ·
        refine ⟨16041841061345870614144199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10694560707563913742762799 16041841061345870614144199)
        ·
          refine ⟨24062761592018805921216299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16041841061345870614144199 24062761592018805921216299)
          ·
            refine ⟨36094142388028208881824449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24062761592018805921216299 36094142388028208881824449)
            ·
              refine ⟨27070606791021156661368337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36094142388028208881824449 27070606791021156661368337)
              ·
                refine ⟨20302955093265867496026253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27070606791021156661368337 20302955093265867496026253)
                ·
                  refine ⟨7613608159974700311009845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20302955093265867496026253 7613608159974700311009845)
                  ·
                    refine ⟨713775764997628154157173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7613608159974700311009845 713775764997628154157173)
                    ·
                      rfl

theorem cell22_2085110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 2, 3, 5].length) (baseStart_2085110 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2085110 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2085110 prefixEnd_2085110 := by exact prefixLift 2085110
  have htrace : WordTrace (prefixWord ++ tailWord_2085110) baseStart_2085110 baseEnd_2085110 := by
    simpa [prefixWord, tailWord_2085110, baseEnd_2085110] using wordTrace_append hprefix tailTrace_2085110
  have hstable : (prefixWord ++ tailWord_2085110).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2085110).length < 2 ^ (prefixWord ++ tailWord_2085110).sum := by decide
  have hdescent : baseEnd_2085110 < baseStart_2085110 := by decide
  rcases family_descends (prefixWord ++ tailWord_2085110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2085123 : List Nat := [1, 1, 1, 3, 2, 3, 2, 9]
def baseStart_2085123 : Nat := 118140960795 + 2085123 * 2 ^ 59
def prefixEnd_2085123 : Nat := 4983230072969 + 3 ^ 40 * 2085123 * 2
def baseEnd_2085123 : Nat := 79308912795922272620237

theorem tailTrace_2085123 : CollatzResearch.WordTrace tailWord_2085123 prefixEnd_2085123 79308912795922272620237 := by
  unfold tailWord_2085123
  simp only [CollatzResearch.WordTrace]
  refine ⟨76050683624962956502092023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50700455749975304334728015 76050683624962956502092023)
  ·
    refine ⟨114076025437444434753138035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76050683624962956502092023 114076025437444434753138035)
    ·
      refine ⟨171114038156166652129707053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114076025437444434753138035 171114038156166652129707053)
      ·
        refine ⟨64167764308562494548640145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 171114038156166652129707053 64167764308562494548640145)
        ·
          refine ⟨48125823231421870911480109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64167764308562494548640145 48125823231421870911480109)
          ·
            refine ⟨18047183711783201591805041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48125823231421870911480109 18047183711783201591805041)
            ·
              refine ⟨13535387783837401193853781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18047183711783201591805041 13535387783837401193853781)
              ·
                refine ⟨79308912795922272620237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 13535387783837401193853781 79308912795922272620237)
                ·
                  rfl

theorem cell22_2085123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 9].length) (baseStart_2085123 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2085123 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2085123 prefixEnd_2085123 := by exact prefixLift 2085123
  have htrace : WordTrace (prefixWord ++ tailWord_2085123) baseStart_2085123 baseEnd_2085123 := by
    simpa [prefixWord, tailWord_2085123, baseEnd_2085123] using wordTrace_append hprefix tailTrace_2085123
  have hstable : (prefixWord ++ tailWord_2085123).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2085123).length < 2 ^ (prefixWord ++ tailWord_2085123).sum := by decide
  have hdescent : baseEnd_2085123 < baseStart_2085123 := by decide
  rcases family_descends (prefixWord ++ tailWord_2085123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2085146 : List Nat := [3, 1, 1, 3, 5, 1, 1, 3, 4]
def baseStart_2085146 : Nat := 118140960795 + 2085146 * 2 ^ 59
def prefixEnd_2085146 : Nat := 4983230072969 + 3 ^ 40 * 2085146 * 2
def baseEnd_2085146 : Nat := 237929362844445353419021

theorem tailTrace_2085146 : CollatzResearch.WordTrace tailWord_2085146 prefixEnd_2085146 237929362844445353419021 := by
  unfold tailWord_2085146
  simp only [CollatzResearch.WordTrace]
  refine ⟨19012880625969907857544823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50701015002586420953452861 19012880625969907857544823)
  ·
    refine ⟨28519320938954861786317235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19012880625969907857544823 28519320938954861786317235)
    ·
      refine ⟨42778981408432292679475853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28519320938954861786317235 42778981408432292679475853)
      ·
        refine ⟨16042118028162109754803445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42778981408432292679475853 16042118028162109754803445)
        ·
          refine ⟨1503948565140197789512823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16042118028162109754803445 1503948565140197789512823)
          ·
            refine ⟨2255922847710296684269235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1503948565140197789512823 2255922847710296684269235)
            ·
              refine ⟨3383884271565445026403853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2255922847710296684269235 3383884271565445026403853)
              ·
                refine ⟨1268956601837041884901445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3383884271565445026403853 1268956601837041884901445)
                ·
                  refine ⟨237929362844445353419021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1268956601837041884901445 237929362844445353419021)
                  ·
                    rfl

theorem cell22_2085146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 1, 3, 4].length) (baseStart_2085146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2085146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2085146 prefixEnd_2085146 := by exact prefixLift 2085146
  have htrace : WordTrace (prefixWord ++ tailWord_2085146) baseStart_2085146 baseEnd_2085146 := by
    simpa [prefixWord, tailWord_2085146, baseEnd_2085146] using wordTrace_append hprefix tailTrace_2085146
  have hstable : (prefixWord ++ tailWord_2085146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2085146).length < 2 ^ (prefixWord ++ tailWord_2085146).sum := by decide
  have hdescent : baseEnd_2085146 < baseStart_2085146 := by decide
  rcases family_descends (prefixWord ++ tailWord_2085146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2085157 : List Nat := [1, 3, 1, 2, 6, 1, 8]
def baseStart_2085157 : Nat := 118140960795 + 2085157 * 2 ^ 59
def prefixEnd_2085157 : Nat := 4983230072969 + 3 ^ 40 * 2085157 * 2
def baseEnd_2085157 : Nat := 26436735335486507341927

theorem tailTrace_2085157 : CollatzResearch.WordTrace tailWord_2085157 prefixEnd_2085157 26436735335486507341927 := by
  unfold tailWord_2085157
  simp only [CollatzResearch.WordTrace]
  refine ⟨76051923706839780308829725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50701282471226520205886483 76051923706839780308829725)
  ·
    refine ⟨28519471390064917615811147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76051923706839780308829725 28519471390064917615811147)
    ·
      refine ⟨42779207085097376423716721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28519471390064917615811147 42779207085097376423716721)
      ·
        refine ⟨32084405313823032317787541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42779207085097376423716721 32084405313823032317787541)
        ·
          refine ⟨1503956499085454639896291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 32084405313823032317787541 1503956499085454639896291)
          ·
            refine ⟨2255934748628181959844437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1503956499085454639896291 2255934748628181959844437)
            ·
              refine ⟨26436735335486507341927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2255934748628181959844437 26436735335486507341927)
              ·
                rfl

theorem cell22_2085157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 8].length) (baseStart_2085157 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2085157 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2085157 prefixEnd_2085157 := by exact prefixLift 2085157
  have htrace : WordTrace (prefixWord ++ tailWord_2085157) baseStart_2085157 baseEnd_2085157 := by
    simpa [prefixWord, tailWord_2085157, baseEnd_2085157] using wordTrace_append hprefix tailTrace_2085157
  have hstable : (prefixWord ++ tailWord_2085157).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2085157).length < 2 ^ (prefixWord ++ tailWord_2085157).sum := by decide
  have hdescent : baseEnd_2085157 < baseStart_2085157 := by decide
  rcases family_descends (prefixWord ++ tailWord_2085157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2085214 : List Nat := [4, 4, 2, 1, 2, 1, 2, 2, 4]
def baseStart_2085214 : Nat := 118140960795 + 2085214 * 2 ^ 59
def prefixEnd_2085214 : Nat := 4983230072969 + 3 ^ 40 * 2085214 * 2
def baseEnd_2085214 : Nat := 237937122107668849852285

theorem tailTrace_2085214 : CollatzResearch.WordTrace tailWord_2085214 prefixEnd_2085214 237937122107668849852285 := by
  unfold tailWord_2085214
  simp only [CollatzResearch.WordTrace]
  refine ⟨9506750333454159880456837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50702668445088852695769797 9506750333454159880456837)
  ·
    refine ⟨1782515687522654977585657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9506750333454159880456837 1782515687522654977585657)
    ·
      refine ⟨1336886765641991233189243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1782515687522654977585657 1336886765641991233189243)
      ·
        refine ⟨2005330148462986849783865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1336886765641991233189243 2005330148462986849783865)
        ·
          refine ⟨1503997611347240137337899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2005330148462986849783865 1503997611347240137337899)
          ·
            refine ⟨2255996417020860206006849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1503997611347240137337899 2255996417020860206006849)
            ·
              refine ⟨1691997312765645154505137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2255996417020860206006849 1691997312765645154505137)
              ·
                refine ⟨1268997984574233865878853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1691997312765645154505137 1268997984574233865878853)
                ·
                  refine ⟨237937122107668849852285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1268997984574233865878853 237937122107668849852285)
                  ·
                    rfl

theorem cell22_2085214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 2, 2, 4].length) (baseStart_2085214 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2085214 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2085214 prefixEnd_2085214 := by exact prefixLift 2085214
  have htrace : WordTrace (prefixWord ++ tailWord_2085214) baseStart_2085214 baseEnd_2085214 := by
    simpa [prefixWord, tailWord_2085214, baseEnd_2085214] using wordTrace_append hprefix tailTrace_2085214
  have hstable : (prefixWord ++ tailWord_2085214).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2085214).length < 2 ^ (prefixWord ++ tailWord_2085214).sum := by decide
  have hdescent : baseEnd_2085214 < baseStart_2085214 := by decide
  rcases family_descends (prefixWord ++ tailWord_2085214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2085223 : List Nat := [1, 1, 5, 1, 3, 3, 2, 2, 1, 3]
def baseStart_2085223 : Nat := 118140960795 + 2085223 * 2 ^ 59
def prefixEnd_2085223 : Nat := 4983230072969 + 3 ^ 40 * 2085223 * 2
def baseEnd_2085223 : Nat := 713814447206933526081827

theorem tailTrace_2085223 : CollatzResearch.WordTrace tailWord_2085223 prefixEnd_2085223 713814447206933526081827 := by
  unfold tailWord_2085223
  simp only [CollatzResearch.WordTrace]
  refine ⟨76054330924600673580732323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50702887283067115720488215 76054330924600673580732323)
  ·
    refine ⟨114081496386901010371098485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76054330924600673580732323 114081496386901010371098485)
    ·
      refine ⟨10695140286271969722290483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 114081496386901010371098485 10695140286271969722290483)
      ·
        refine ⟨16042710429407954583435725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10695140286271969722290483 16042710429407954583435725)
        ·
          refine ⟨6016016411027982968788397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16042710429407954583435725 6016016411027982968788397)
          ·
            refine ⟨2256006154135493613295649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6016016411027982968788397 2256006154135493613295649)
            ·
              refine ⟨1692004615601620209971737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2256006154135493613295649 1692004615601620209971737)
              ·
                refine ⟨1269003461701215157478803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1692004615601620209971737 1269003461701215157478803)
                ·
                  refine ⟨1903505192551822736218205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1269003461701215157478803 1903505192551822736218205)
                  ·
                    refine ⟨713814447206933526081827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1903505192551822736218205 713814447206933526081827)
                    ·
                      rfl

theorem cell22_2085223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 2, 2, 1, 3].length) (baseStart_2085223 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2085223 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2085223 prefixEnd_2085223 := by exact prefixLift 2085223
  have htrace : WordTrace (prefixWord ++ tailWord_2085223) baseStart_2085223 baseEnd_2085223 := by
    simpa [prefixWord, tailWord_2085223, baseEnd_2085223] using wordTrace_append hprefix tailTrace_2085223
  have hstable : (prefixWord ++ tailWord_2085223).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2085223).length < 2 ^ (prefixWord ++ tailWord_2085223).sum := by decide
  have hdescent : baseEnd_2085223 < baseStart_2085223 := by decide
  rcases family_descends (prefixWord ++ tailWord_2085223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2085270 : List Nat := [5, 3, 1, 2, 1, 2, 1, 2, 5]
def baseStart_2085270 : Nat := 118140960795 + 2085270 * 2 ^ 59
def prefixEnd_2085270 : Nat := 4983230072969 + 3 ^ 40 * 2085270 * 2
def baseEnd_2085270 : Nat := 237943512089147023385561

theorem tailTrace_2085270 : CollatzResearch.WordTrace tailWord_2085270 prefixEnd_2085270 237943512089147023385561 := by
  unfold tailWord_2085270
  simp only [CollatzResearch.WordTrace]
  refine ⟨4753502822214400037980829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 50704030103620267071795509 4753502822214400037980829)
  ·
    refine ⟨1782563558330400014242811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4753502822214400037980829 1782563558330400014242811)
    ·
      refine ⟨2673845337495600021364217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1782563558330400014242811 2673845337495600021364217)
      ·
        refine ⟨2005384003121700016023163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2673845337495600021364217 2005384003121700016023163)
        ·
          refine ⟨3008076004682550024034745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2005384003121700016023163 3008076004682550024034745)
          ·
            refine ⟨2256057003511912518026059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3008076004682550024034745 2256057003511912518026059)
            ·
              refine ⟨3384085505267868777039089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2256057003511912518026059 3384085505267868777039089)
              ·
                refine ⟨2538064128950901582779317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3384085505267868777039089 2538064128950901582779317)
                ·
                  refine ⟨237943512089147023385561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2538064128950901582779317 237943512089147023385561)
                  ·
                    rfl

theorem cell22_2085270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 1, 2, 5].length) (baseStart_2085270 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2085270 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2085270 prefixEnd_2085270 := by exact prefixLift 2085270
  have htrace : WordTrace (prefixWord ++ tailWord_2085270) baseStart_2085270 baseEnd_2085270 := by
    simpa [prefixWord, tailWord_2085270, baseEnd_2085270] using wordTrace_append hprefix tailTrace_2085270
  have hstable : (prefixWord ++ tailWord_2085270).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2085270).length < 2 ^ (prefixWord ++ tailWord_2085270).sum := by decide
  have hdescent : baseEnd_2085270 < baseStart_2085270 := by decide
  rcases family_descends (prefixWord ++ tailWord_2085270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2085309 : List Nat := [1, 4, 1, 2, 2, 4, 2, 6]
def baseStart_2085309 : Nat := 118140960795 + 2085309 * 2 ^ 59
def prefixEnd_2085309 : Nat := 4983230072969 + 3 ^ 40 * 2085309 * 2
def baseEnd_2085309 : Nat := 79315987418273107603507

theorem tailTrace_2085309 : CollatzResearch.WordTrace tailWord_2085309 prefixEnd_2085309 79315987418273107603507 := by
  unfold tailWord_2085309
  simp only [CollatzResearch.WordTrace]
  refine ⟨76057467602289110268362981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50704978401526073512241987 76057467602289110268362981)
  ·
    refine ⟨14260775175429208175318059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76057467602289110268362981 14260775175429208175318059)
    ·
      refine ⟨21391162763143812262977089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14260775175429208175318059 21391162763143812262977089)
      ·
        refine ⟨16043372072357859197232817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21391162763143812262977089 16043372072357859197232817)
        ·
          refine ⟨12032529054268394397924613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16043372072357859197232817 12032529054268394397924613)
          ·
            refine ⟨2256099197675323949610865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12032529054268394397924613 2256099197675323949610865)
            ·
              refine ⟨1692074398256492962208149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2256099197675323949610865 1692074398256492962208149)
              ·
                refine ⟨79315987418273107603507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1692074398256492962208149 79315987418273107603507)
                ·
                  rfl

theorem cell22_2085309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 2, 6].length) (baseStart_2085309 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2085309 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2085309 prefixEnd_2085309 := by exact prefixLift 2085309
  have htrace : WordTrace (prefixWord ++ tailWord_2085309) baseStart_2085309 baseEnd_2085309 := by
    simpa [prefixWord, tailWord_2085309, baseEnd_2085309] using wordTrace_append hprefix tailTrace_2085309
  have hstable : (prefixWord ++ tailWord_2085309).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2085309).length < 2 ^ (prefixWord ++ tailWord_2085309).sum := by decide
  have hdescent : baseEnd_2085309 < baseStart_2085309 := by decide
  rcases family_descends (prefixWord ++ tailWord_2085309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2085337 : List Nat := [1, 2, 1, 2, 4, 1, 2, 4, 5]
def baseStart_2085337 : Nat := 118140960795 + 2085337 * 2 ^ 59
def prefixEnd_2085337 : Nat := 4983230072969 + 3 ^ 40 * 2085337 * 2
def baseEnd_2085337 : Nat := 237951157245558409577159

theorem tailTrace_2085337 : CollatzResearch.WordTrace tailWord_2085337 prefixEnd_2085337 237951157245558409577159 := by
  unfold tailWord_2085337
  simp only [CollatzResearch.WordTrace]
  refine ⟨76058488846187671050382265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50705659230791780700254843 76058488846187671050382265)
  ·
    refine ⟨57043866634640753287786699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76058488846187671050382265 57043866634640753287786699)
    ·
      refine ⟨85565799951961129931680049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57043866634640753287786699 85565799951961129931680049)
      ·
        refine ⟨64174349963970847448760037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85565799951961129931680049 64174349963970847448760037)
        ·
          refine ⟨12032690618244533896642507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64174349963970847448760037 12032690618244533896642507)
          ·
            refine ⟨18049035927366800844963761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12032690618244533896642507 18049035927366800844963761)
            ·
              refine ⟨13536776945525100633722821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18049035927366800844963761 13536776945525100633722821)
              ·
                refine ⟨2538145677285956368823029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13536776945525100633722821 2538145677285956368823029)
                ·
                  refine ⟨237951157245558409577159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2538145677285956368823029 237951157245558409577159)
                  ·
                    rfl

theorem cell22_2085337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 4, 5].length) (baseStart_2085337 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2085337 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2085337 prefixEnd_2085337 := by exact prefixLift 2085337
  have htrace : WordTrace (prefixWord ++ tailWord_2085337) baseStart_2085337 baseEnd_2085337 := by
    simpa [prefixWord, tailWord_2085337, baseEnd_2085337] using wordTrace_append hprefix tailTrace_2085337
  have hstable : (prefixWord ++ tailWord_2085337).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2085337).length < 2 ^ (prefixWord ++ tailWord_2085337).sum := by decide
  have hdescent : baseEnd_2085337 < baseStart_2085337 := by decide
  rcases family_descends (prefixWord ++ tailWord_2085337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2085354 : List Nat := [3, 1, 3, 1, 3, 2, 1, 3, 5]
def baseStart_2085354 : Nat := 118140960795 + 2085354 * 2 ^ 59
def prefixEnd_2085354 : Nat := 4983230072969 + 3 ^ 40 * 2085354 * 2
def baseEnd_2085354 : Nat := 237953097061364283685475

theorem tailTrace_2085354 : CollatzResearch.WordTrace tailWord_2085354 prefixEnd_2085354 237953097061364283685475 := by
  unfold tailWord_2085354
  simp only [CollatzResearch.WordTrace]
  refine ⟨19014777221781520738437779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50706072591417388635834077 19014777221781520738437779)
  ·
    refine ⟨28522165832672281107656669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19014777221781520738437779 28522165832672281107656669)
    ·
      refine ⟨10695812187252105415371251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28522165832672281107656669 10695812187252105415371251)
      ·
        refine ⟨16043718280878158123056877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10695812187252105415371251 16043718280878158123056877)
        ·
          refine ⟨6016394355329309296146329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16043718280878158123056877 6016394355329309296146329)
          ·
            refine ⟨4512295766496981972109747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6016394355329309296146329 4512295766496981972109747)
            ·
              refine ⟨6768443649745472958164621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4512295766496981972109747 6768443649745472958164621)
              ·
                refine ⟨2538166368654552359311733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6768443649745472958164621 2538166368654552359311733)
                ·
                  refine ⟨237953097061364283685475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2538166368654552359311733 237953097061364283685475)
                  ·
                    rfl

theorem cell22_2085354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 1, 3, 5].length) (baseStart_2085354 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2085354 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2085354 prefixEnd_2085354 := by exact prefixLift 2085354
  have htrace : WordTrace (prefixWord ++ tailWord_2085354) baseStart_2085354 baseEnd_2085354 := by
    simpa [prefixWord, tailWord_2085354, baseEnd_2085354] using wordTrace_append hprefix tailTrace_2085354
  have hstable : (prefixWord ++ tailWord_2085354).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2085354).length < 2 ^ (prefixWord ++ tailWord_2085354).sum := by decide
  have hdescent : baseEnd_2085354 < baseStart_2085354 := by decide
  rcases family_descends (prefixWord ++ tailWord_2085354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2085397 : List Nat := [1, 3, 2, 1, 3, 1, 1, 2, 3, 5]
def baseStart_2085397 : Nat := 118140960795 + 2085397 * 2 ^ 59
def prefixEnd_2085397 : Nat := 4983230072969 + 3 ^ 40 * 2085397 * 2
def baseEnd_2085397 : Nat := 713874010962855072231293

theorem tailTrace_2085397 : CollatzResearch.WordTrace tailWord_2085397 prefixEnd_2085397 713874010962855072231293 := by
  unfold tailWord_2085397
  simp only [CollatzResearch.WordTrace]
  refine ⟨76060677225970301297566445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50707118150646867531710963 76060677225970301297566445)
  ·
    refine ⟨28522753959738862986587417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76060677225970301297566445 28522753959738862986587417)
    ·
      refine ⟨21392065469804147239940563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28522753959738862986587417 21392065469804147239940563)
      ·
        refine ⟨32088098204706220859910845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21392065469804147239940563 32088098204706220859910845)
        ·
          refine ⟨12033036826764832822466567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32088098204706220859910845 12033036826764832822466567)
          ·
            refine ⟨18049555240147249233699851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12033036826764832822466567 18049555240147249233699851)
            ·
              refine ⟨27074332860220873850549777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18049555240147249233699851 27074332860220873850549777)
              ·
                refine ⟨20305749645165655387912333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27074332860220873850549777 20305749645165655387912333)
                ·
                  refine ⟨7614656116937120770467125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20305749645165655387912333 7614656116937120770467125)
                  ·
                    refine ⟨713874010962855072231293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7614656116937120770467125 713874010962855072231293)
                    ·
                      rfl

theorem cell22_2085397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 2, 3, 5].length) (baseStart_2085397 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2085397 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2085397 prefixEnd_2085397 := by exact prefixLift 2085397
  have htrace : WordTrace (prefixWord ++ tailWord_2085397) baseStart_2085397 baseEnd_2085397 := by
    simpa [prefixWord, tailWord_2085397, baseEnd_2085397] using wordTrace_append hprefix tailTrace_2085397
  have hstable : (prefixWord ++ tailWord_2085397).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2085397).length < 2 ^ (prefixWord ++ tailWord_2085397).sum := by decide
  have hdescent : baseEnd_2085397 < baseStart_2085397 := by decide
  rcases family_descends (prefixWord ++ tailWord_2085397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2085487 : List Nat := [1, 1, 2, 1, 3, 2, 2, 2, 1, 7]
def baseStart_2085487 : Nat := 118140960795 + 2085487 * 2 ^ 59
def prefixEnd_2085487 : Nat := 4983230072969 + 3 ^ 40 * 2085487 * 2
def baseEnd_2085487 : Nat := 713904819802124837481017

theorem tailTrace_2085487 : CollatzResearch.WordTrace tailWord_2085487 prefixEnd_2085487 713904819802124837481017 := by
  unfold tailWord_2085487
  simp only [CollatzResearch.WordTrace]
  refine ⟨76063959795644246668342715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50709306530429497778895143 76063959795644246668342715)
  ·
    refine ⟨114095939693466370002514073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76063959795644246668342715 114095939693466370002514073)
    ·
      refine ⟨85571954770099777501885555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114095939693466370002514073 85571954770099777501885555)
      ·
        refine ⟨128357932155149666252828333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85571954770099777501885555 128357932155149666252828333)
        ·
          refine ⟨48134224558181124844810625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128357932155149666252828333 48134224558181124844810625)
          ·
            refine ⟨36100668418635843633607969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48134224558181124844810625 36100668418635843633607969)
            ·
              refine ⟨27075501313976882725205977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36100668418635843633607969 27075501313976882725205977)
              ·
                refine ⟨20306625985482662043904483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27075501313976882725205977 20306625985482662043904483)
                ·
                  refine ⟨30459938978223993065856725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20306625985482662043904483 30459938978223993065856725)
                  ·
                    refine ⟨713904819802124837481017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30459938978223993065856725 713904819802124837481017)
                    ·
                      rfl

theorem cell22_2085487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 2, 1, 7].length) (baseStart_2085487 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2085487 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2085487 prefixEnd_2085487 := by exact prefixLift 2085487
  have htrace : WordTrace (prefixWord ++ tailWord_2085487) baseStart_2085487 baseEnd_2085487 := by
    simpa [prefixWord, tailWord_2085487, baseEnd_2085487] using wordTrace_append hprefix tailTrace_2085487
  have hstable : (prefixWord ++ tailWord_2085487).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2085487).length < 2 ^ (prefixWord ++ tailWord_2085487).sum := by decide
  have hdescent : baseEnd_2085487 < baseStart_2085487 := by decide
  rcases family_descends (prefixWord ++ tailWord_2085487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2085536 : List Nat := [2, 1, 1, 4, 4, 1, 1, 1, 3, 4]
def baseStart_2085536 : Nat := 118140960795 + 2085536 * 2 ^ 59
def prefixEnd_2085536 : Nat := 4983230072969 + 3 ^ 40 * 2085536 * 2
def baseEnd_2085536 : Nat := 713921593503505043005867

theorem tailTrace_2085536 : CollatzResearch.WordTrace tailWord_2085536 prefixEnd_2085536 713921593503505043005867 := by
  unfold tailWord_2085536
  simp only [CollatzResearch.WordTrace]
  refine ⟨38032873486233364018438231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50710497981644485357917641 38032873486233364018438231)
  ·
    refine ⟨57049310229350046027657347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38032873486233364018438231 57049310229350046027657347)
    ·
      refine ⟨85573965344025069041486021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57049310229350046027657347 85573965344025069041486021)
      ·
        refine ⟨16045118502004700445278629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85573965344025069041486021 16045118502004700445278629)
        ·
          refine ⟨3008459719125881333489743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16045118502004700445278629 3008459719125881333489743)
          ·
            refine ⟨4512689578688822000234615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3008459719125881333489743 4512689578688822000234615)
            ·
              refine ⟨6769034368033233000351923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4512689578688822000234615 6769034368033233000351923)
              ·
                refine ⟨10153551552049849500527885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6769034368033233000351923 10153551552049849500527885)
                ·
                  refine ⟨3807581832018693562697957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10153551552049849500527885 3807581832018693562697957)
                  ·
                    refine ⟨713921593503505043005867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3807581832018693562697957 713921593503505043005867)
                    ·
                      rfl

theorem cell22_2085536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 1, 1, 3, 4].length) (baseStart_2085536 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2085536 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2085536 prefixEnd_2085536 := by exact prefixLift 2085536
  have htrace : WordTrace (prefixWord ++ tailWord_2085536) baseStart_2085536 baseEnd_2085536 := by
    simpa [prefixWord, tailWord_2085536, baseEnd_2085536] using wordTrace_append hprefix tailTrace_2085536
  have hstable : (prefixWord ++ tailWord_2085536).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2085536).length < 2 ^ (prefixWord ++ tailWord_2085536).sum := by decide
  have hdescent : baseEnd_2085536 < baseStart_2085536 := by decide
  rcases family_descends (prefixWord ++ tailWord_2085536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2085568 : List Nat := [2, 1, 1, 2, 4, 2, 4, 2, 4]
def baseStart_2085568 : Nat := 118140960795 + 2085568 * 2 ^ 59
def prefixEnd_2085568 : Nat := 4983230072969 + 3 ^ 40 * 2085568 * 2
def baseEnd_2085568 : Nat := 237977515919155875401923

theorem tailTrace_2085568 : CollatzResearch.WordTrace tailWord_2085568 prefixEnd_2085568 237977515919155875401923 := by
  unfold tailWord_2085568
  simp only [CollatzResearch.WordTrace]
  refine ⟨38033457054175398751020679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50711276072233865001360905 38033457054175398751020679)
  ·
    refine ⟨57050185581263098126531019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38033457054175398751020679 57050185581263098126531019)
    ·
      refine ⟨85575278371894647189796529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57050185581263098126531019 85575278371894647189796529)
      ·
        refine ⟨64181458778920985392347397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85575278371894647189796529 64181458778920985392347397)
        ·
          refine ⟨12034023521047684761065137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64181458778920985392347397 12034023521047684761065137)
          ·
            refine ⟨9025517640785763570798853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12034023521047684761065137 9025517640785763570798853)
            ·
              refine ⟨1692284557647330669524785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9025517640785763570798853 1692284557647330669524785)
              ·
                refine ⟨1269213418235498002143589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1692284557647330669524785 1269213418235498002143589)
                ·
                  refine ⟨237977515919155875401923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1269213418235498002143589 237977515919155875401923)
                  ·
                    rfl

theorem cell22_2085568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 4, 2, 4].length) (baseStart_2085568 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2085568 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2085568 prefixEnd_2085568 := by exact prefixLift 2085568
  have htrace : WordTrace (prefixWord ++ tailWord_2085568) baseStart_2085568 baseEnd_2085568 := by
    simpa [prefixWord, tailWord_2085568, baseEnd_2085568] using wordTrace_append hprefix tailTrace_2085568
  have hstable : (prefixWord ++ tailWord_2085568).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2085568).length < 2 ^ (prefixWord ++ tailWord_2085568).sum := by decide
  have hdescent : baseEnd_2085568 < baseStart_2085568 := by decide
  rcases family_descends (prefixWord ++ tailWord_2085568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2085624 : List Nat := [2, 1, 2, 1, 1, 2, 5, 1, 7]
def baseStart_2085624 : Nat := 118140960795 + 2085624 * 2 ^ 59
def prefixEnd_2085624 : Nat := 4983230072969 + 3 ^ 40 * 2085624 * 2
def baseEnd_2085624 : Nat := 237983905900634048935199

theorem tailTrace_2085624 : CollatzResearch.WordTrace tailWord_2085624 prefixEnd_2085624 237983905900634048935199 := by
  unfold tailWord_2085624
  simp only [CollatzResearch.WordTrace]
  refine ⟨38034478298073959533039963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50712637730765279377386617 38034478298073959533039963)
  ·
    refine ⟨57051717447110939299559945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38034478298073959533039963 57051717447110939299559945)
    ·
      refine ⟨42788788085333204474669959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57051717447110939299559945 42788788085333204474669959)
      ·
        refine ⟨64183182127999806712004939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42788788085333204474669959 64183182127999806712004939)
        ·
          refine ⟨96274773191999710068007409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64183182127999806712004939 96274773191999710068007409)
          ·
            refine ⟨72206079893999782551005557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96274773191999710068007409 72206079893999782551005557)
            ·
              refine ⟨6769319990062479614156771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 72206079893999782551005557 6769319990062479614156771)
              ·
                refine ⟨10153979985093719421235157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6769319990062479614156771 10153979985093719421235157)
                ·
                  refine ⟨237983905900634048935199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10153979985093719421235157 237983905900634048935199)
                  ·
                    rfl

theorem cell22_2085624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5, 1, 7].length) (baseStart_2085624 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2085624 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2085624 prefixEnd_2085624 := by exact prefixLift 2085624
  have htrace : WordTrace (prefixWord ++ tailWord_2085624) baseStart_2085624 baseEnd_2085624 := by
    simpa [prefixWord, tailWord_2085624, baseEnd_2085624] using wordTrace_append hprefix tailTrace_2085624
  have hstable : (prefixWord ++ tailWord_2085624).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2085624).length < 2 ^ (prefixWord ++ tailWord_2085624).sum := by decide
  have hdescent : baseEnd_2085624 < baseStart_2085624 := by decide
  rcases family_descends (prefixWord ++ tailWord_2085624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2085628 : List Nat := [2, 2, 2, 1, 3, 3, 2, 1, 3, 3]
def baseStart_2085628 : Nat := 118140960795 + 2085628 * 2 ^ 59
def prefixEnd_2085628 : Nat := 4983230072969 + 3 ^ 40 * 2085628 * 2
def baseEnd_2085628 : Nat := 713953086983647469705585

theorem tailTrace_2085628 : CollatzResearch.WordTrace tailWord_2085628 prefixEnd_2085628 713953086983647469705585 := by
  unfold tailWord_2085628
  simp only [CollatzResearch.WordTrace]
  refine ⟨38034551244066713874612769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50712734992088951832817025 38034551244066713874612769)
  ·
    refine ⟨28525913433050035405959577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38034551244066713874612769 28525913433050035405959577)
    ·
      refine ⟨21394435074787526554469683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28525913433050035405959577 21394435074787526554469683)
      ·
        refine ⟨32091652612181289831704525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21394435074787526554469683 32091652612181289831704525)
        ·
          refine ⟨12034369729567983686889197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32091652612181289831704525 12034369729567983686889197)
          ·
            refine ⟨4512888648587993882583449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12034369729567983686889197 4512888648587993882583449)
            ·
              refine ⟨3384666486440995411937587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4512888648587993882583449 3384666486440995411937587)
              ·
                refine ⟨5076999729661493117906381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3384666486440995411937587 5076999729661493117906381)
                ·
                  refine ⟨1903874898623059919214893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5076999729661493117906381 1903874898623059919214893)
                  ·
                    refine ⟨713953086983647469705585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1903874898623059919214893 713953086983647469705585)
                    ·
                      rfl

theorem cell22_2085628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 2, 1, 3, 3].length) (baseStart_2085628 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2085628 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2085628 prefixEnd_2085628 := by exact prefixLift 2085628
  have htrace : WordTrace (prefixWord ++ tailWord_2085628) baseStart_2085628 baseEnd_2085628 := by
    simpa [prefixWord, tailWord_2085628, baseEnd_2085628] using wordTrace_append hprefix tailTrace_2085628
  have hstable : (prefixWord ++ tailWord_2085628).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2085628).length < 2 ^ (prefixWord ++ tailWord_2085628).sum := by decide
  have hdescent : baseEnd_2085628 < baseStart_2085628 := by decide
  rcases family_descends (prefixWord ++ tailWord_2085628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2085701 : List Nat := [1, 3, 1, 1, 1, 2, 2, 2, 6, 3]
def baseStart_2085701 : Nat := 118140960795 + 2085701 * 2 ^ 59
def prefixEnd_2085701 : Nat := 4983230072969 + 3 ^ 40 * 2085701 * 2
def baseEnd_2085701 : Nat := 713978076375499612630361

theorem tailTrace_2085701 : CollatzResearch.WordTrace tailWord_2085701 prefixEnd_2085701 713978076375499612630361 := by
  unfold tailWord_2085701
  simp only [CollatzResearch.WordTrace]
  refine ⟨76071765016868961216632957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50714510011245974144421971 76071765016868961216632957)
  ·
    refine ⟨28526911881325860456237359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76071765016868961216632957 28526911881325860456237359)
    ·
      refine ⟨42790367821988790684356039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28526911881325860456237359 42790367821988790684356039)
      ·
        refine ⟨64185551732983186026534059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42790367821988790684356039 64185551732983186026534059)
        ·
          refine ⟨96278327599474779039801089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64185551732983186026534059 96278327599474779039801089)
          ·
            refine ⟨72208745699606084279850817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96278327599474779039801089 72208745699606084279850817)
            ·
              refine ⟨54156559274704563209888113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72208745699606084279850817 54156559274704563209888113)
              ·
                refine ⟨40617419456028422407416085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54156559274704563209888113 40617419456028422407416085)
                ·
                  refine ⟨1903941537001332300347629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 40617419456028422407416085 1903941537001332300347629)
                  ·
                    refine ⟨713978076375499612630361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1903941537001332300347629 713978076375499612630361)
                    ·
                      rfl

theorem cell22_2085701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 2, 6, 3].length) (baseStart_2085701 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2085701 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2085701 prefixEnd_2085701 := by exact prefixLift 2085701
  have htrace : WordTrace (prefixWord ++ tailWord_2085701) baseStart_2085701 baseEnd_2085701 := by
    simpa [prefixWord, tailWord_2085701, baseEnd_2085701] using wordTrace_append hprefix tailTrace_2085701
  have hstable : (prefixWord ++ tailWord_2085701).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2085701).length < 2 ^ (prefixWord ++ tailWord_2085701).sum := by decide
  have hdescent : baseEnd_2085701 < baseStart_2085701 := by decide
  rcases family_descends (prefixWord ++ tailWord_2085701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2085735 : List Nat := [1, 1, 5, 1, 2, 3, 2, 2, 2, 3]
def baseStart_2085735 : Nat := 118140960795 + 2085735 * 2 ^ 59
def prefixEnd_2085735 : Nat := 4983230072969 + 3 ^ 40 * 2085735 * 2
def baseEnd_2085735 : Nat := 713989715270334857280257

theorem tailTrace_2085735 : CollatzResearch.WordTrace tailWord_2085735 prefixEnd_2085735 713989715270334857280257 := by
  unfold tailWord_2085735
  simp only [CollatzResearch.WordTrace]
  refine ⟨76073005098745785023370659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50715336732497190015580439 76073005098745785023370659)
  ·
    refine ⟨114109507648118677535055989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76073005098745785023370659 114109507648118677535055989)
    ·
      refine ⟨10697766342011126018911499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 114109507648118677535055989 10697766342011126018911499)
      ·
        refine ⟨16046649513016689028367249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10697766342011126018911499 16046649513016689028367249)
        ·
          refine ⟨12034987134762516771275437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16046649513016689028367249 12034987134762516771275437)
          ·
            refine ⟨4513120175535943789228289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12034987134762516771275437 4513120175535943789228289)
            ·
              refine ⟨3384840131651957841921217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4513120175535943789228289 3384840131651957841921217)
              ·
                refine ⟨2538630098738968381440913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3384840131651957841921217 2538630098738968381440913)
                ·
                  refine ⟨1903972574054226286080685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2538630098738968381440913 1903972574054226286080685)
                  ·
                    refine ⟨713989715270334857280257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1903972574054226286080685 713989715270334857280257)
                    ·
                      rfl

theorem cell22_2085735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 2, 2, 2, 3].length) (baseStart_2085735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2085735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2085735 prefixEnd_2085735 := by exact prefixLift 2085735
  have htrace : WordTrace (prefixWord ++ tailWord_2085735) baseStart_2085735 baseEnd_2085735 := by
    simpa [prefixWord, tailWord_2085735, baseEnd_2085735] using wordTrace_append hprefix tailTrace_2085735
  have hstable : (prefixWord ++ tailWord_2085735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2085735).length < 2 ^ (prefixWord ++ tailWord_2085735).sum := by decide
  have hdescent : baseEnd_2085735 < baseStart_2085735 := by decide
  rcases family_descends (prefixWord ++ tailWord_2085735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2085763 : List Nat := [1, 1, 1, 3, 4, 1, 3, 2, 3, 3]
def baseStart_2085763 : Nat := 118140960795 + 2085763 * 2 ^ 59
def prefixEnd_2085763 : Nat := 4983230072969 + 3 ^ 40 * 2085763 * 2
def baseEnd_2085763 : Nat := 713999300242552117580171

theorem tailTrace_2085763 : CollatzResearch.WordTrace tailWord_2085763 prefixEnd_2085763 713999300242552117580171 := by
  unfold tailWord_2085763
  simp only [CollatzResearch.WordTrace]
  refine ⟨76074026342644345805389943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50716017561762897203593295 76074026342644345805389943)
  ·
    refine ⟨114111039513966518708084915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76074026342644345805389943 114111039513966518708084915)
    ·
      refine ⟨171166559270949778062127373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114111039513966518708084915 171166559270949778062127373)
      ·
        refine ⟨64187459726606166773297765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 171166559270949778062127373 64187459726606166773297765)
        ·
          refine ⟨12035148698738656269993331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64187459726606166773297765 12035148698738656269993331)
          ·
            refine ⟨18052723048107984404989997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12035148698738656269993331 18052723048107984404989997)
            ·
              refine ⟨6769771143040494151871249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18052723048107984404989997 6769771143040494151871249)
              ·
                refine ⟨5077328357280370613903437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6769771143040494151871249 5077328357280370613903437)
                ·
                  refine ⟨1903998133980138980213789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5077328357280370613903437 1903998133980138980213789)
                  ·
                    refine ⟨713999300242552117580171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1903998133980138980213789 713999300242552117580171)
                    ·
                      rfl

theorem cell22_2085763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 3, 2, 3, 3].length) (baseStart_2085763 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2085763 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2085763 prefixEnd_2085763 := by exact prefixLift 2085763
  have htrace : WordTrace (prefixWord ++ tailWord_2085763) baseStart_2085763 baseEnd_2085763 := by
    simpa [prefixWord, tailWord_2085763, baseEnd_2085763] using wordTrace_append hprefix tailTrace_2085763
  have hstable : (prefixWord ++ tailWord_2085763).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2085763).length < 2 ^ (prefixWord ++ tailWord_2085763).sum := by decide
  have hdescent : baseEnd_2085763 < baseStart_2085763 := by decide
  rcases family_descends (prefixWord ++ tailWord_2085763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2085793 : List Nat := [1, 2, 3, 4, 1, 2, 1, 1, 7]
def baseStart_2085793 : Nat := 118140960795 + 2085793 * 2 ^ 59
def prefixEnd_2085793 : Nat := 4983230072969 + 3 ^ 40 * 2085793 * 2
def baseEnd_2085793 : Nat := 238003189951880679776693

theorem tailTrace_2085793 : CollatzResearch.WordTrace tailWord_2085793 prefixEnd_2085793 238003189951880679776693 := by
  unfold tailWord_2085793
  simp only [CollatzResearch.WordTrace]
  refine ⟨76075120532535660928982033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50716747021690440619321355 76075120532535660928982033)
  ·
    refine ⟨57056340399401745696736525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76075120532535660928982033 57056340399401745696736525)
    ·
      refine ⟨21396127649775654636276197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57056340399401745696736525 21396127649775654636276197)
      ·
        refine ⟨4011773934332935244301787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21396127649775654636276197 4011773934332935244301787)
        ·
          refine ⟨6017660901499402866452681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4011773934332935244301787 6017660901499402866452681)
          ·
            refine ⟨4513245676124552149839511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6017660901499402866452681 4513245676124552149839511)
            ·
              refine ⟨6769868514186828224759267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4513245676124552149839511 6769868514186828224759267)
              ·
                refine ⟨10154802771280242337138901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6769868514186828224759267 10154802771280242337138901)
                ·
                  refine ⟨238003189951880679776693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10154802771280242337138901 238003189951880679776693)
                  ·
                    rfl

theorem cell22_2085793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 1, 1, 7].length) (baseStart_2085793 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2085793 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2085793 prefixEnd_2085793 := by exact prefixLift 2085793
  have htrace : WordTrace (prefixWord ++ tailWord_2085793) baseStart_2085793 baseEnd_2085793 := by
    simpa [prefixWord, tailWord_2085793, baseEnd_2085793] using wordTrace_append hprefix tailTrace_2085793
  have hstable : (prefixWord ++ tailWord_2085793).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2085793).length < 2 ^ (prefixWord ++ tailWord_2085793).sum := by decide
  have hdescent : baseEnd_2085793 < baseStart_2085793 := by decide
  rcases family_descends (prefixWord ++ tailWord_2085793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2085855 : List Nat := [1, 1, 2, 3, 5, 2, 1, 1, 6]
def baseStart_2085855 : Nat := 118140960795 + 2085855 * 2 ^ 59
def prefixEnd_2085855 : Nat := 4983230072969 + 3 ^ 40 * 2085855 * 2
def baseEnd_2085855 : Nat := 238010264574231514759963

theorem tailTrace_2085855 : CollatzResearch.WordTrace tailWord_2085855 prefixEnd_2085855 238010264574231514759963 := by
  unfold tailWord_2085855
  simp only [CollatzResearch.WordTrace]
  refine ⟨76077381858311045517739019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50718254572207363678492679 76077381858311045517739019)
  ·
    refine ⟨114116072787466568276608529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76077381858311045517739019 114116072787466568276608529)
    ·
      refine ⟨85587054590599926207456397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114116072787466568276608529 85587054590599926207456397)
      ·
        refine ⟨32095145471474972327796149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85587054590599926207456397 32095145471474972327796149)
        ·
          refine ⟨3008919887950778655730889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 32095145471474972327796149 3008919887950778655730889)
          ·
            refine ⟨2256689915963083991798167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3008919887950778655730889 2256689915963083991798167)
            ·
              refine ⟨3385034873944625987697251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2256689915963083991798167 3385034873944625987697251)
              ·
                refine ⟨5077552310916938981545877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3385034873944625987697251 5077552310916938981545877)
                ·
                  refine ⟨238010264574231514759963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5077552310916938981545877 238010264574231514759963)
                  ·
                    rfl

theorem cell22_2085855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 1, 1, 6].length) (baseStart_2085855 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2085855 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2085855 prefixEnd_2085855 := by exact prefixLift 2085855
  have htrace : WordTrace (prefixWord ++ tailWord_2085855) baseStart_2085855 baseEnd_2085855 := by
    simpa [prefixWord, tailWord_2085855, baseEnd_2085855] using wordTrace_append hprefix tailTrace_2085855
  have hstable : (prefixWord ++ tailWord_2085855).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2085855).length < 2 ^ (prefixWord ++ tailWord_2085855).sum := by decide
  have hdescent : baseEnd_2085855 < baseStart_2085855 := by decide
  rcases family_descends (prefixWord ++ tailWord_2085855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2085874 : List Nat := [3, 2, 1, 5, 1, 2, 1, 2, 1, 4]
def baseStart_2085874 : Nat := 118140960795 + 2085874 * 2 ^ 59
def prefixEnd_2085874 : Nat := 4983230072969 + 3 ^ 40 * 2085874 * 2
def baseEnd_2085874 : Nat := 714037297810984828054831

theorem tailTrace_2085874 : CollatzResearch.WordTrace tailWord_2085874 prefixEnd_2085874 714037297810984828054831 := by
  unfold tailWord_2085874
  simp only [CollatzResearch.WordTrace]
  refine ⟨19019518711310552940670169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50718716563494807841787117 19019518711310552940670169)
  ·
    refine ⟨14264639033482914705502627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19019518711310552940670169 14264639033482914705502627)
    ·
      refine ⟨21396958550224372058253941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14264639033482914705502627 21396958550224372058253941)
      ·
        refine ⟨2005964864083534880461307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 21396958550224372058253941 2005964864083534880461307)
        ·
          refine ⟨3008947296125302320691961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2005964864083534880461307 3008947296125302320691961)
          ·
            refine ⟨2256710472093976740518971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3008947296125302320691961 2256710472093976740518971)
            ·
              refine ⟨3385065708140965110778457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2256710472093976740518971 3385065708140965110778457)
              ·
                refine ⟨2538799281105723833083843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3385065708140965110778457 2538799281105723833083843)
                ·
                  refine ⟨3808198921658585749625765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2538799281105723833083843 3808198921658585749625765)
                  ·
                    refine ⟨714037297810984828054831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3808198921658585749625765 714037297810984828054831)
                    ·
                      rfl

theorem cell22_2085874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 1, 2, 1, 4].length) (baseStart_2085874 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2085874 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2085874 prefixEnd_2085874 := by exact prefixLift 2085874
  have htrace : WordTrace (prefixWord ++ tailWord_2085874) baseStart_2085874 baseEnd_2085874 := by
    simpa [prefixWord, tailWord_2085874, baseEnd_2085874] using wordTrace_append hprefix tailTrace_2085874
  have hstable : (prefixWord ++ tailWord_2085874).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2085874).length < 2 ^ (prefixWord ++ tailWord_2085874).sum := by decide
  have hdescent : baseEnd_2085874 < baseStart_2085874 := by decide
  rcases family_descends (prefixWord ++ tailWord_2085874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2085906 : List Nat := [3, 2, 5, 1, 1, 1, 1, 4, 4]
def baseStart_2085906 : Nat := 118140960795 + 2085906 * 2 ^ 59
def prefixEnd_2085906 : Nat := 4983230072969 + 3 ^ 40 * 2085906 * 2
def baseEnd_2085906 : Nat := 238016084021649137084911

theorem tailTrace_2085906 : CollatzResearch.WordTrace tailWord_2085906 prefixEnd_2085906 238016084021649137084911 := by
  unfold tailWord_2085906
  simp only [CollatzResearch.WordTrace]
  refine ⟨19019810495281570306961393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50719494654084187485230381 19019810495281570306961393)
  ·
    refine ⟨14264857871461177730221045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19019810495281570306961393 14264857871461177730221045)
    ·
      refine ⟨1337330425449485412208223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14264857871461177730221045 1337330425449485412208223)
      ·
        refine ⟨2005995638174228118312335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1337330425449485412208223 2005995638174228118312335)
        ·
          refine ⟨3008993457261342177468503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2005995638174228118312335 3008993457261342177468503)
          ·
            refine ⟨4513490185892013266202755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3008993457261342177468503 4513490185892013266202755)
            ·
              refine ⟨6770235278838019899304133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4513490185892013266202755 6770235278838019899304133)
              ·
                refine ⟨1269419114782128731119525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6770235278838019899304133 1269419114782128731119525)
                ·
                  refine ⟨238016084021649137084911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1269419114782128731119525 238016084021649137084911)
                  ·
                    rfl

theorem cell22_2085906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 1, 4, 4].length) (baseStart_2085906 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2085906 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2085906 prefixEnd_2085906 := by exact prefixLift 2085906
  have htrace : WordTrace (prefixWord ++ tailWord_2085906) baseStart_2085906 baseEnd_2085906 := by
    simpa [prefixWord, tailWord_2085906, baseEnd_2085906] using wordTrace_append hprefix tailTrace_2085906
  have hstable : (prefixWord ++ tailWord_2085906).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2085906).length < 2 ^ (prefixWord ++ tailWord_2085906).sum := by decide
  have hdescent : baseEnd_2085906 < baseStart_2085906 := by decide
  rcases family_descends (prefixWord ++ tailWord_2085906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2085917 : List Nat := [1, 4, 2, 2, 4, 1, 1, 7]
def baseStart_2085917 : Nat := 118140960795 + 2085917 * 2 ^ 59
def prefixEnd_2085917 : Nat := 4983230072969 + 3 ^ 40 * 2085917 * 2
def baseEnd_2085917 : Nat := 79339113065527449914411

theorem tailTrace_2085917 : CollatzResearch.WordTrace tailWord_2085917 prefixEnd_2085917 79339113065527449914411 := by
  unfold tailWord_2085917
  simp only [CollatzResearch.WordTrace]
  refine ⟨76079643184086430106496005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50719762122724286737664003 76079643184086430106496005)
  ·
    refine ⟨14264933097016205644968001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76079643184086430106496005 14264933097016205644968001)
    ·
      refine ⟨10698699822762154233726001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14264933097016205644968001 10698699822762154233726001)
      ·
        refine ⟨8024024867071615675294501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10698699822762154233726001 8024024867071615675294501)
        ·
          refine ⟨1504504662575927939117719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8024024867071615675294501 1504504662575927939117719)
          ·
            refine ⟨2256756993863891908676579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1504504662575927939117719 2256756993863891908676579)
            ·
              refine ⟨3385135490795837863014869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2256756993863891908676579 3385135490795837863014869)
              ·
                refine ⟨79339113065527449914411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3385135490795837863014869 79339113065527449914411)
                ·
                  rfl

theorem cell22_2085917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 1, 7].length) (baseStart_2085917 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2085917 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2085917 prefixEnd_2085917 := by exact prefixLift 2085917
  have htrace : WordTrace (prefixWord ++ tailWord_2085917) baseStart_2085917 baseEnd_2085917 := by
    simpa [prefixWord, tailWord_2085917, baseEnd_2085917] using wordTrace_append hprefix tailTrace_2085917
  have hstable : (prefixWord ++ tailWord_2085917).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2085917).length < 2 ^ (prefixWord ++ tailWord_2085917).sum := by decide
  have hdescent : baseEnd_2085917 < baseStart_2085917 := by decide
  rcases family_descends (prefixWord ++ tailWord_2085917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2085949 : List Nat := [1, 4, 1, 3, 1, 3, 2, 3, 1, 3]
def baseStart_2085949 : Nat := 118140960795 + 2085949 * 2 ^ 59
def prefixEnd_2085949 : Nat := 4983230072969 + 3 ^ 40 * 2085949 * 2
def baseEnd_2085949 : Nat := 714062971843709632429601

theorem tailTrace_2085949 : CollatzResearch.WordTrace tailWord_2085949 prefixEnd_2085949 714062971843709632429601 := by
  unfold tailWord_2085949
  simp only [CollatzResearch.WordTrace]
  refine ⟨76080810319970499571660901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50720540213313666381107267 76080810319970499571660901)
  ·
    refine ⟨14265151934994468669686419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76080810319970499571660901 14265151934994468669686419)
    ·
      refine ⟨21397727902491703004529629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14265151934994468669686419 21397727902491703004529629)
      ·
        refine ⟨8024147963434388626698611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21397727902491703004529629 8024147963434388626698611)
        ·
          refine ⟨12036221945151582940047917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8024147963434388626698611 12036221945151582940047917)
          ·
            refine ⟨4513583229431843602517969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12036221945151582940047917 4513583229431843602517969)
            ·
              refine ⟨3385187422073882701888477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4513583229431843602517969 3385187422073882701888477)
              ·
                refine ⟨1269445283277706013208179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3385187422073882701888477 1269445283277706013208179)
                ·
                  refine ⟨1904167924916559019812269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1269445283277706013208179 1904167924916559019812269)
                  ·
                    refine ⟨714062971843709632429601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1904167924916559019812269 714062971843709632429601)
                    ·
                      rfl

theorem cell22_2085949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 2, 3, 1, 3].length) (baseStart_2085949 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2085949 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2085949 prefixEnd_2085949 := by exact prefixLift 2085949
  have htrace : WordTrace (prefixWord ++ tailWord_2085949) baseStart_2085949 baseEnd_2085949 := by
    simpa [prefixWord, tailWord_2085949, baseEnd_2085949] using wordTrace_append hprefix tailTrace_2085949
  have hstable : (prefixWord ++ tailWord_2085949).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2085949).length < 2 ^ (prefixWord ++ tailWord_2085949).sum := by decide
  have hdescent : baseEnd_2085949 < baseStart_2085949 := by decide
  rcases family_descends (prefixWord ++ tailWord_2085949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2086003 : List Nat := [1, 1, 1, 2, 2, 1, 1, 1, 8, 4]
def baseStart_2086003 : Nat := 118140960795 + 2086003 * 2 ^ 59
def prefixEnd_2086003 : Nat := 4983230072969 + 3 ^ 40 * 2086003 * 2
def baseEnd_2086003 : Nat := 714081457147271491579435

theorem tailTrace_2086003 : CollatzResearch.WordTrace tailWord_2086003 prefixEnd_2086003 714081457147271491579435 := by
  unfold tailWord_2086003
  simp only [CollatzResearch.WordTrace]
  refine ⟨76082779861774866794126663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50721853241183244529417775 76082779861774866794126663)
  ·
    refine ⟨114124169792662300191189995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76082779861774866794126663 114124169792662300191189995)
    ·
      refine ⟨171186254688993450286784993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114124169792662300191189995 171186254688993450286784993)
      ·
        refine ⟨128389691016745087715088745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171186254688993450286784993 128389691016745087715088745)
        ·
          refine ⟨96292268262558815786316559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128389691016745087715088745 96292268262558815786316559)
          ·
            refine ⟨144438402393838223679474839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96292268262558815786316559 144438402393838223679474839)
            ·
              refine ⟨216657603590757335519212259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144438402393838223679474839 216657603590757335519212259)
              ·
                refine ⟨324986405386136003278818389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 216657603590757335519212259 324986405386136003278818389)
                ·
                  refine ⟨3808434438118781288423653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 324986405386136003278818389 3808434438118781288423653)
                  ·
                    refine ⟨714081457147271491579435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3808434438118781288423653 714081457147271491579435)
                    ·
                      rfl

theorem cell22_2086003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 8, 4].length) (baseStart_2086003 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2086003 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2086003 prefixEnd_2086003 := by exact prefixLift 2086003
  have htrace : WordTrace (prefixWord ++ tailWord_2086003) baseStart_2086003 baseEnd_2086003 := by
    simpa [prefixWord, tailWord_2086003, baseEnd_2086003] using wordTrace_append hprefix tailTrace_2086003
  have hstable : (prefixWord ++ tailWord_2086003).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2086003).length < 2 ^ (prefixWord ++ tailWord_2086003).sum := by decide
  have hdescent : baseEnd_2086003 < baseStart_2086003 := by decide
  rcases family_descends (prefixWord ++ tailWord_2086003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2086020 : List Nat := [2, 3, 2, 1, 2, 2, 1, 1, 4, 4]
def baseStart_2086020 : Nat := 118140960795 + 2086020 * 2 ^ 59
def prefixEnd_2086020 : Nat := 4983230072969 + 3 ^ 40 * 2086020 * 2
def baseEnd_2086020 : Nat := 714087276594689113904383

theorem tailTrace_2086020 : CollatzResearch.WordTrace tailWord_2086020 prefixEnd_2086020 714087276594689113904383 := by
  unfold tailWord_2086020
  simp only [CollatzResearch.WordTrace]
  refine ⟨38041699951356639348747757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50722266601808852464997009 38041699951356639348747757)
  ·
    refine ⟨14265637481758739755780409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38041699951356639348747757 14265637481758739755780409)
    ·
      refine ⟨10699228111319054816835307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14265637481758739755780409 10699228111319054816835307)
      ·
        refine ⟨16048842166978582225252961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10699228111319054816835307 16048842166978582225252961)
        ·
          refine ⟨12036631625233936668939721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16048842166978582225252961 12036631625233936668939721)
          ·
            refine ⟨9027473718925452501704791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12036631625233936668939721 9027473718925452501704791)
            ·
              refine ⟨13541210578388178752557187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9027473718925452501704791 13541210578388178752557187)
              ·
                refine ⟨20311815867582268128835781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13541210578388178752557187 20311815867582268128835781)
                ·
                  refine ⟨3808465475171675274156709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20311815867582268128835781 3808465475171675274156709)
                  ·
                    refine ⟨714087276594689113904383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3808465475171675274156709 714087276594689113904383)
                    ·
                      rfl

theorem cell22_2086020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 1, 4, 4].length) (baseStart_2086020 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2086020 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2086020 prefixEnd_2086020 := by exact prefixLift 2086020
  have htrace : WordTrace (prefixWord ++ tailWord_2086020) baseStart_2086020 baseEnd_2086020 := by
    simpa [prefixWord, tailWord_2086020, baseEnd_2086020] using wordTrace_append hprefix tailTrace_2086020
  have hstable : (prefixWord ++ tailWord_2086020).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2086020).length < 2 ^ (prefixWord ++ tailWord_2086020).sum := by decide
  have hdescent : baseEnd_2086020 < baseStart_2086020 := by decide
  rcases family_descends (prefixWord ++ tailWord_2086020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2086024 : List Nat := [2, 1, 3, 4, 3, 1, 1, 1, 6]
def baseStart_2086024 : Nat := 118140960795 + 2086024 * 2 ^ 59
def prefixEnd_2086024 : Nat := 4983230072969 + 3 ^ 40 * 2086024 * 2
def baseEnd_2086024 : Nat := 238029548625478145601457

theorem tailTrace_2086024 : CollatzResearch.WordTrace tailWord_2086024 prefixEnd_2086024 238029548625478145601457 := by
  unfold tailWord_2086024
  simp only [CollatzResearch.WordTrace]
  refine ⟨38041772897349393690320563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50722363863132524920427417 38041772897349393690320563)
  ·
    refine ⟨57062659346024090535480845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38041772897349393690320563 57062659346024090535480845)
    ·
      refine ⟨21398497254759033950805317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57062659346024090535480845 21398497254759033950805317)
      ·
        refine ⟨4012218235267318865775997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21398497254759033950805317 4012218235267318865775997)
        ·
          refine ⟨1504581838225244574665999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4012218235267318865775997 1504581838225244574665999)
          ·
            refine ⟨2256872757337866861998999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1504581838225244574665999 2256872757337866861998999)
            ·
              refine ⟨3385309136006800292998499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2256872757337866861998999 3385309136006800292998499)
              ·
                refine ⟨5077963704010200439497749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3385309136006800292998499 5077963704010200439497749)
                ·
                  refine ⟨238029548625478145601457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5077963704010200439497749 238029548625478145601457)
                  ·
                    rfl

theorem cell22_2086024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 1, 1, 6].length) (baseStart_2086024 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2086024 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2086024 prefixEnd_2086024 := by exact prefixLift 2086024
  have htrace : WordTrace (prefixWord ++ tailWord_2086024) baseStart_2086024 baseEnd_2086024 := by
    simpa [prefixWord, tailWord_2086024, baseEnd_2086024] using wordTrace_append hprefix tailTrace_2086024
  have hstable : (prefixWord ++ tailWord_2086024).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2086024).length < 2 ^ (prefixWord ++ tailWord_2086024).sum := by decide
  have hdescent : baseEnd_2086024 < baseStart_2086024 := by decide
  rcases family_descends (prefixWord ++ tailWord_2086024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2086039 : List Nat := [1, 1, 3, 3, 3, 1, 4, 1, 2, 3]
def baseStart_2086039 : Nat := 118140960795 + 2086039 * 2 ^ 59
def prefixEnd_2086039 : Nat := 4983230072969 + 3 ^ 40 * 2086039 * 2
def baseEnd_2086039 : Nat := 714093780682979397679325

theorem tailTrace_2086039 : CollatzResearch.WordTrace tailWord_2086039 prefixEnd_2086039 714093780682979397679325 := by
  unfold tailWord_2086039
  simp only [CollatzResearch.WordTrace]
  refine ⟨76084092889644444942437171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50722728593096296628291447 76084092889644444942437171)
  ·
    refine ⟨114126139334466667413655757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76084092889644444942437171 114126139334466667413655757)
    ·
      refine ⟨42797302250425000280120909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114126139334466667413655757 42797302250425000280120909)
      ·
        refine ⟨16048988343909375105045341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42797302250425000280120909 16048988343909375105045341)
        ·
          refine ⟨6018370628966015664392003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16048988343909375105045341 6018370628966015664392003)
          ·
            refine ⟨9027555943449023496588005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6018370628966015664392003 9027555943449023496588005)
            ·
              refine ⟨1692666739396691905610251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9027555943449023496588005 1692666739396691905610251)
              ·
                refine ⟨2539000109095037858415377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1692666739396691905610251 2539000109095037858415377)
                ·
                  refine ⟨1904250081821278393811533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2539000109095037858415377 1904250081821278393811533)
                  ·
                    refine ⟨714093780682979397679325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1904250081821278393811533 714093780682979397679325)
                    ·
                      rfl

theorem cell22_2086039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 4, 1, 2, 3].length) (baseStart_2086039 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2086039 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2086039 prefixEnd_2086039 := by exact prefixLift 2086039
  have htrace : WordTrace (prefixWord ++ tailWord_2086039) baseStart_2086039 baseEnd_2086039 := by
    simpa [prefixWord, tailWord_2086039, baseEnd_2086039] using wordTrace_append hprefix tailTrace_2086039
  have hstable : (prefixWord ++ tailWord_2086039).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2086039).length < 2 ^ (prefixWord ++ tailWord_2086039).sum := by decide
  have hdescent : baseEnd_2086039 < baseStart_2086039 := by decide
  rcases family_descends (prefixWord ++ tailWord_2086039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2086063 : List Nat := [1, 1, 2, 1, 2, 3, 2, 1, 9]
def baseStart_2086063 : Nat := 118140960795 + 2086063 * 2 ^ 59
def prefixEnd_2086063 : Nat := 4983230072969 + 3 ^ 40 * 2086063 * 2
def baseEnd_2086063 : Nat := 238033998791150445026417

theorem tailTrace_2086063 : CollatzResearch.WordTrace tailWord_2086063 prefixEnd_2086063 238033998791150445026417 := by
  unfold tailWord_2086063
  simp only [CollatzResearch.WordTrace]
  refine ⟨76084968241557497041310843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50723312161038331360873895 76084968241557497041310843)
  ·
    refine ⟨114127452362336245561966265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76084968241557497041310843 114127452362336245561966265)
    ·
      refine ⟨85595589271752184171474699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114127452362336245561966265 85595589271752184171474699)
      ·
        refine ⟨128393383907628276257212049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85595589271752184171474699 128393383907628276257212049)
        ·
          refine ⟨96295037930721207192909037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128393383907628276257212049 96295037930721207192909037)
          ·
            refine ⟨36110639224020452697340889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96295037930721207192909037 36110639224020452697340889)
            ·
              refine ⟨27082979418015339523005667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36110639224020452697340889 27082979418015339523005667)
              ·
                refine ⟨40624469127023009284508501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27082979418015339523005667 40624469127023009284508501)
                ·
                  refine ⟨238033998791150445026417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 40624469127023009284508501 238033998791150445026417)
                  ·
                    rfl

theorem cell22_2086063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 1, 9].length) (baseStart_2086063 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2086063 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2086063 prefixEnd_2086063 := by exact prefixLift 2086063
  have htrace : WordTrace (prefixWord ++ tailWord_2086063) baseStart_2086063 baseEnd_2086063 := by
    simpa [prefixWord, tailWord_2086063, baseEnd_2086063] using wordTrace_append hprefix tailTrace_2086063
  have hstable : (prefixWord ++ tailWord_2086063).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2086063).length < 2 ^ (prefixWord ++ tailWord_2086063).sum := by decide
  have hdescent : baseEnd_2086063 < baseStart_2086063 := by decide
  rcases family_descends (prefixWord ++ tailWord_2086063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2086142 : List Nat := [4, 2, 2, 1, 1, 2, 1, 3, 6]
def baseStart_2086142 : Nat := 118140960795 + 2086142 * 2 ^ 59
def prefixEnd_2086142 : Nat := 4983230072969 + 3 ^ 40 * 2086142 * 2
def baseEnd_2086142 : Nat := 238043013229307154118003

theorem tailTrace_2086142 : CollatzResearch.WordTrace tailWord_2086142 prefixEnd_2086142 238043013229307154118003 := by
  unfold tailWord_2086142
  simp only [CollatzResearch.WordTrace]
  refine ⟨9510981201033911691679585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50725233072180862355624453 9510981201033911691679585)
  ·
    refine ⟨7133235900775433768759689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9510981201033911691679585 7133235900775433768759689)
    ·
      refine ⟨5349926925581575326569767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7133235900775433768759689 5349926925581575326569767)
      ·
        refine ⟨8024890388372362989854651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5349926925581575326569767 8024890388372362989854651)
        ·
          refine ⟨12037335582558544484781977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8024890388372362989854651 12037335582558544484781977)
          ·
            refine ⟨9028001686918908363586483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12037335582558544484781977 9028001686918908363586483)
            ·
              refine ⟨13542002530378362545379725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9028001686918908363586483 13542002530378362545379725)
              ·
                refine ⟨5078250948891885954517397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13542002530378362545379725 5078250948891885954517397)
                ·
                  refine ⟨238043013229307154118003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5078250948891885954517397 238043013229307154118003)
                  ·
                    rfl

theorem cell22_2086142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 3, 6].length) (baseStart_2086142 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2086142 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2086142 prefixEnd_2086142 := by exact prefixLift 2086142
  have htrace : WordTrace (prefixWord ++ tailWord_2086142) baseStart_2086142 baseEnd_2086142 := by
    simpa [prefixWord, tailWord_2086142, baseEnd_2086142] using wordTrace_append hprefix tailTrace_2086142
  have hstable : (prefixWord ++ tailWord_2086142).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2086142).length < 2 ^ (prefixWord ++ tailWord_2086142).sum := by decide
  have hdescent : baseEnd_2086142 < baseStart_2086142 := by decide
  rcases family_descends (prefixWord ++ tailWord_2086142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2086155 : List Nat := [1, 1, 1, 1, 5, 3, 1, 2, 1, 6]
def baseStart_2086155 : Nat := 118140960795 + 2086155 * 2 ^ 59
def prefixEnd_2086155 : Nat := 4983230072969 + 3 ^ 40 * 2086155 * 2
def baseEnd_2086155 : Nat := 714133489853593761778969

theorem tailTrace_2086155 : CollatzResearch.WordTrace tailWord_2086155 prefixEnd_2086155 714133489853593761778969 := by
  unfold tailWord_2086155
  simp only [CollatzResearch.WordTrace]
  refine ⟨76088323757224196753659919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50725549171482797835773279 76088323757224196753659919)
  ·
    refine ⟨114132485635836295130489879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76088323757224196753659919 114132485635836295130489879)
    ·
      refine ⟨171198728453754442695734819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114132485635836295130489879 171198728453754442695734819)
      ·
        refine ⟨256798092680631664043602229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171198728453754442695734819 256798092680631664043602229)
        ·
          refine ⟨24074821188809218504087709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 256798092680631664043602229 24074821188809218504087709)
          ·
            refine ⟨9028057945803456939032891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24074821188809218504087709 9028057945803456939032891)
            ·
              refine ⟨13542086918705185408549337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9028057945803456939032891 13542086918705185408549337)
              ·
                refine ⟨10156565189028889056412003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13542086918705185408549337 10156565189028889056412003)
                ·
                  refine ⟨15234847783543333584618005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10156565189028889056412003 15234847783543333584618005)
                  ·
                    refine ⟨714133489853593761778969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15234847783543333584618005 714133489853593761778969)
                    ·
                      rfl

theorem cell22_2086155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 2, 1, 6].length) (baseStart_2086155 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2086155 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2086155 prefixEnd_2086155 := by exact prefixLift 2086155
  have htrace : WordTrace (prefixWord ++ tailWord_2086155) baseStart_2086155 baseEnd_2086155 := by
    simpa [prefixWord, tailWord_2086155, baseEnd_2086155] using wordTrace_append hprefix tailTrace_2086155
  have hstable : (prefixWord ++ tailWord_2086155).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2086155).length < 2 ^ (prefixWord ++ tailWord_2086155).sum := by decide
  have hdescent : baseEnd_2086155 < baseStart_2086155 := by decide
  rcases family_descends (prefixWord ++ tailWord_2086155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2086176 : List Nat := [2, 1, 1, 5, 3, 2, 1, 3, 4]
def baseStart_2086176 : Nat := 118140960795 + 2086176 * 2 ^ 59
def prefixEnd_2086176 : Nat := 4983230072969 + 3 ^ 40 * 2086176 * 2
def baseEnd_2086176 : Nat := 238046892860918902334635

theorem tailTrace_2086176 : CollatzResearch.WordTrace tailWord_2086176 prefixEnd_2086176 238046892860918902334635 := by
  unfold tailWord_2086176
  simp only [CollatzResearch.WordTrace]
  refine ⟨38044544845074058670087191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50726059793432078226782921 38044544845074058670087191)
  ·
    refine ⟨57066817267611088005130787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38044544845074058670087191 57066817267611088005130787)
    ·
      refine ⟨85600225901416632007696181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57066817267611088005130787 85600225901416632007696181)
      ·
        refine ⟨8025021178257809250721517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 85600225901416632007696181 8025021178257809250721517)
        ·
          refine ⟨3009382941846678469020569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8025021178257809250721517 3009382941846678469020569)
          ·
            refine ⟨2257037206385008851765427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3009382941846678469020569 2257037206385008851765427)
            ·
              refine ⟨3385555809577513277648141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2257037206385008851765427 3385555809577513277648141)
              ·
                refine ⟨1269583428591567479118053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3385555809577513277648141 1269583428591567479118053)
                ·
                  refine ⟨238046892860918902334635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1269583428591567479118053 238046892860918902334635)
                  ·
                    rfl

theorem cell22_2086176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 1, 3, 4].length) (baseStart_2086176 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2086176 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2086176 prefixEnd_2086176 := by exact prefixLift 2086176
  have htrace : WordTrace (prefixWord ++ tailWord_2086176) baseStart_2086176 baseEnd_2086176 := by
    simpa [prefixWord, tailWord_2086176, baseEnd_2086176] using wordTrace_append hprefix tailTrace_2086176
  have hstable : (prefixWord ++ tailWord_2086176).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2086176).length < 2 ^ (prefixWord ++ tailWord_2086176).sum := by decide
  have hdescent : baseEnd_2086176 < baseStart_2086176 := by decide
  rcases family_descends (prefixWord ++ tailWord_2086176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2086189 : List Nat := [1, 5, 3, 1, 1, 1, 1, 1, 4, 4]
def baseStart_2086189 : Nat := 118140960795 + 2086189 * 2 ^ 59
def prefixEnd_2086189 : Nat := 4983230072969 + 3 ^ 40 * 2086189 * 2
def baseEnd_2086189 : Nat := 714145128748429006428865

theorem tailTrace_2086189 : CollatzResearch.WordTrace tailWord_2086189 prefixEnd_2086189 714145128748429006428865 := by
  unfold tailWord_2086189
  simp only [CollatzResearch.WordTrace]
  refine ⟨76089563839101020560397621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50726375892734013706931747 76089563839101020560397621)
  ·
    refine ⟨7133396609915720677537277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 76089563839101020560397621 7133396609915720677537277)
    ·
      refine ⟨2675023728718395254076479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7133396609915720677537277 2675023728718395254076479)
      ·
        refine ⟨4012535593077592881114719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2675023728718395254076479 4012535593077592881114719)
        ·
          refine ⟨6018803389616389321672079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4012535593077592881114719 6018803389616389321672079)
          ·
            refine ⟨9028205084424583982508119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6018803389616389321672079 9028205084424583982508119)
            ·
              refine ⟨13542307626636875973762179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9028205084424583982508119 13542307626636875973762179)
              ·
                refine ⟨20313461439955313960643269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13542307626636875973762179 20313461439955313960643269)
                ·
                  refine ⟨3808774019991621367620613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20313461439955313960643269 3808774019991621367620613)
                  ·
                    refine ⟨714145128748429006428865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3808774019991621367620613 714145128748429006428865)
                    ·
                      rfl

theorem cell22_2086189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_2086189 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2086189 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2086189 prefixEnd_2086189 := by exact prefixLift 2086189
  have htrace : WordTrace (prefixWord ++ tailWord_2086189) baseStart_2086189 baseEnd_2086189 := by
    simpa [prefixWord, tailWord_2086189, baseEnd_2086189] using wordTrace_append hprefix tailTrace_2086189
  have hstable : (prefixWord ++ tailWord_2086189).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2086189).length < 2 ^ (prefixWord ++ tailWord_2086189).sum := by decide
  have hdescent : baseEnd_2086189 < baseStart_2086189 := by decide
  rcases family_descends (prefixWord ++ tailWord_2086189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2086200 : List Nat := [2, 1, 2, 1, 3, 1, 1, 3, 2, 6]
def baseStart_2086200 : Nat := 118140960795 + 2086200 * 2 ^ 59
def prefixEnd_2086200 : Nat := 4983230072969 + 3 ^ 40 * 2086200 * 2
def baseEnd_2086200 : Nat := 714148894273228644403831

theorem tailTrace_2086200 : CollatzResearch.WordTrace tailWord_2086200 prefixEnd_2086200 714148894273228644403831 := by
  unfold tailWord_2086200
  simp only [CollatzResearch.WordTrace]
  refine ⟨38044982521030584719524027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50726643361374112959365369 38044982521030584719524027)
  ·
    refine ⟨57067473781545877079286041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38044982521030584719524027 57067473781545877079286041)
    ·
      refine ⟨42800605336159407809464531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57067473781545877079286041 42800605336159407809464531)
      ·
        refine ⟨64200908004239111714196797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42800605336159407809464531 64200908004239111714196797)
        ·
          refine ⟨24075340501589666892823799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64200908004239111714196797 24075340501589666892823799)
          ·
            refine ⟨36113010752384500339235699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24075340501589666892823799 36113010752384500339235699)
            ·
              refine ⟨54169516128576750508853549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36113010752384500339235699 54169516128576750508853549)
              ·
                refine ⟨20313568548216281440820081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54169516128576750508853549 20313568548216281440820081)
                ·
                  refine ⟨15235176411162211080615061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20313568548216281440820081 15235176411162211080615061)
                  ·
                    refine ⟨714148894273228644403831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15235176411162211080615061 714148894273228644403831)
                    ·
                      rfl

theorem cell22_2086200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 3, 2, 6].length) (baseStart_2086200 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2086200 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2086200 prefixEnd_2086200 := by exact prefixLift 2086200
  have htrace : WordTrace (prefixWord ++ tailWord_2086200) baseStart_2086200 baseEnd_2086200 := by
    simpa [prefixWord, tailWord_2086200, baseEnd_2086200] using wordTrace_append hprefix tailTrace_2086200
  have hstable : (prefixWord ++ tailWord_2086200).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2086200).length < 2 ^ (prefixWord ++ tailWord_2086200).sum := by decide
  have hdescent : baseEnd_2086200 < baseStart_2086200 := by decide
  rcases family_descends (prefixWord ++ tailWord_2086200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2086253 : List Nat := [1, 5, 1, 1, 1, 3, 4, 2, 1, 3]
def baseStart_2086253 : Nat := 118140960795 + 2086253 * 2 ^ 59
def prefixEnd_2086253 : Nat := 4983230072969 + 3 ^ 40 * 2086253 * 2
def baseEnd_2086253 : Nat := 714167037256354172828669

theorem tailTrace_2086253 : CollatzResearch.WordTrace tailWord_2086253 prefixEnd_2086253 714167037256354172828669 := by
  unfold tailWord_2086253
  simp only [CollatzResearch.WordTrace]
  refine ⟨76091898110869159490727413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50727932073912772993818275 76091898110869159490727413)
  ·
    refine ⟨7133615447893983702255695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 76091898110869159490727413 7133615447893983702255695)
    ·
      refine ⟨10700423171840975553383543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7133615447893983702255695 10700423171840975553383543)
      ·
        refine ⟨16050634757761463330075315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10700423171840975553383543 16050634757761463330075315)
        ·
          refine ⟨24075952136642194995112973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16050634757761463330075315 24075952136642194995112973)
          ·
            refine ⟨9028482051240823123167365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24075952136642194995112973 9028482051240823123167365)
            ·
              refine ⟨1692840384607654335593881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9028482051240823123167365 1692840384607654335593881)
              ·
                refine ⟨1269630288455740751695411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1692840384607654335593881 1269630288455740751695411)
                ·
                  refine ⟨1904445432683611127543117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1269630288455740751695411 1904445432683611127543117)
                  ·
                    refine ⟨714167037256354172828669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1904445432683611127543117 714167037256354172828669)
                    ·
                      rfl

theorem cell22_2086253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 4, 2, 1, 3].length) (baseStart_2086253 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2086253 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2086253 prefixEnd_2086253 := by exact prefixLift 2086253
  have htrace : WordTrace (prefixWord ++ tailWord_2086253) baseStart_2086253 baseEnd_2086253 := by
    simpa [prefixWord, tailWord_2086253, baseEnd_2086253] using wordTrace_append hprefix tailTrace_2086253
  have hstable : (prefixWord ++ tailWord_2086253).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2086253).length < 2 ^ (prefixWord ++ tailWord_2086253).sum := by decide
  have hdescent : baseEnd_2086253 < baseStart_2086253 := by decide
  rcases family_descends (prefixWord ++ tailWord_2086253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2086296 : List Nat := [2, 1, 2, 5, 2, 1, 1, 3, 1, 4]
def baseStart_2086296 : Nat := 118140960795 + 2086296 * 2 ^ 59
def prefixEnd_2086296 : Nat := 4983230072969 + 3 ^ 40 * 2086296 * 2
def baseEnd_2086296 : Nat := 714181757035116394003537

theorem tailTrace_2086296 : CollatzResearch.WordTrace tailWord_2086296 prefixEnd_2086296 714181757035116394003537 := by
  unfold tailWord_2086296
  simp only [CollatzResearch.WordTrace]
  refine ⟨38046733224856688917271371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50728977633142251889695161 38046733224856688917271371)
  ·
    refine ⟨57070099837285033375907057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38046733224856688917271371 57070099837285033375907057)
    ·
      refine ⟨42802574877963775031930293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57070099837285033375907057 42802574877963775031930293)
      ·
        refine ⟨4012741394809103909243465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 42802574877963775031930293 4012741394809103909243465)
        ·
          refine ⟨3009556046106827931932599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4012741394809103909243465 3009556046106827931932599)
          ·
            refine ⟨4514334069160241897898899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3009556046106827931932599 4514334069160241897898899)
            ·
              refine ⟨6771501103740362846848349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4514334069160241897898899 6771501103740362846848349)
              ·
                refine ⟨2539312913902636067568131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6771501103740362846848349 2539312913902636067568131)
                ·
                  refine ⟨3808969370853954101352197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2539312913902636067568131 3808969370853954101352197)
                  ·
                    refine ⟨714181757035116394003537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3808969370853954101352197 714181757035116394003537)
                    ·
                      rfl

theorem cell22_2086296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 1, 3, 1, 4].length) (baseStart_2086296 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2086296 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2086296 prefixEnd_2086296 := by exact prefixLift 2086296
  have htrace : WordTrace (prefixWord ++ tailWord_2086296) baseStart_2086296 baseEnd_2086296 := by
    simpa [prefixWord, tailWord_2086296, baseEnd_2086296] using wordTrace_append hprefix tailTrace_2086296
  have hstable : (prefixWord ++ tailWord_2086296).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2086296).length < 2 ^ (prefixWord ++ tailWord_2086296).sum := by decide
  have hdescent : baseEnd_2086296 < baseStart_2086296 := by decide
  rcases family_descends (prefixWord ++ tailWord_2086296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2086307 : List Nat := [1, 1, 1, 4, 1, 3, 2, 1, 4, 4]
def baseStart_2086307 : Nat := 118140960795 + 2086307 * 2 ^ 59
def prefixEnd_2086307 : Nat := 4983230072969 + 3 ^ 40 * 2086307 * 2
def baseEnd_2086307 : Nat := 714185522559916031978503

theorem tailTrace_2086307 : CollatzResearch.WordTrace tailWord_2086307 prefixEnd_2086307 714185522559916031978503 := by
  unfold tailWord_2086307
  simp only [CollatzResearch.WordTrace]
  refine ⟨76093867652673526713193175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50729245101782351142128783 76093867652673526713193175)
  ·
    refine ⟨114140801479010290069789763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76093867652673526713193175 114140801479010290069789763)
    ·
      refine ⟨171211202218515435104684645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114140801479010290069789763 171211202218515435104684645)
      ·
        refine ⟨32102100415971644082128371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 171211202218515435104684645 32102100415971644082128371)
        ·
          refine ⟨48153150623957466123192557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32102100415971644082128371 48153150623957466123192557)
          ·
            refine ⟨18057431483984049796197209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48153150623957466123192557 18057431483984049796197209)
            ·
              refine ⟨13543073612988037347147907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18057431483984049796197209 13543073612988037347147907)
              ·
                refine ⟨20314610419482056020721861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13543073612988037347147907 20314610419482056020721861)
                ·
                  refine ⟨3808989453652885503885349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20314610419482056020721861 3808989453652885503885349)
                  ·
                    refine ⟨714185522559916031978503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3808989453652885503885349 714185522559916031978503)
                    ·
                      rfl

theorem cell22_2086307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 1, 4, 4].length) (baseStart_2086307 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2086307 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2086307 prefixEnd_2086307 := by exact prefixLift 2086307
  have htrace : WordTrace (prefixWord ++ tailWord_2086307) baseStart_2086307 baseEnd_2086307 := by
    simpa [prefixWord, tailWord_2086307, baseEnd_2086307] using wordTrace_append hprefix tailTrace_2086307
  have hstable : (prefixWord ++ tailWord_2086307).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2086307).length < 2 ^ (prefixWord ++ tailWord_2086307).sum := by decide
  have hdescent : baseEnd_2086307 < baseStart_2086307 := by decide
  rcases family_descends (prefixWord ++ tailWord_2086307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2086309 : List Nat := [1, 3, 1, 2, 1, 1, 2, 6, 2, 3]
def baseStart_2086309 : Nat := 118140960795 + 2086309 * 2 ^ 59
def prefixEnd_2086309 : Nat := 4983230072969 + 3 ^ 40 * 2086309 * 2
def baseEnd_2086309 : Nat := 714186207200788693428497

theorem tailTrace_2086309 : CollatzResearch.WordTrace tailWord_2086309 prefixEnd_2086309 714186207200788693428497 := by
  unfold tailWord_2086309
  simp only [CollatzResearch.WordTrace]
  refine ⟨76093940598666281054765981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50729293732444187369843987 76093940598666281054765981)
  ·
    refine ⟨28535227724499855395537243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76093940598666281054765981 28535227724499855395537243)
    ·
      refine ⟨42802841586749783093305865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28535227724499855395537243 42802841586749783093305865)
      ·
        refine ⟨32102131190062337319979399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42802841586749783093305865 32102131190062337319979399)
        ·
          refine ⟨48153196785093505979969099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32102131190062337319979399 48153196785093505979969099)
          ·
            refine ⟨72229795177640258969953649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48153196785093505979969099 72229795177640258969953649)
            ·
              refine ⟨54172346383230194227465237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72229795177640258969953649 54172346383230194227465237)
              ·
                refine ⟨2539328736713915354412433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 54172346383230194227465237 2539328736713915354412433)
                ·
                  refine ⟨1904496552535436515809325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2539328736713915354412433 1904496552535436515809325)
                  ·
                    refine ⟨714186207200788693428497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1904496552535436515809325 714186207200788693428497)
                    ·
                      rfl

theorem cell22_2086309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 6, 2, 3].length) (baseStart_2086309 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2086309 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2086309 prefixEnd_2086309 := by exact prefixLift 2086309
  have htrace : WordTrace (prefixWord ++ tailWord_2086309) baseStart_2086309 baseEnd_2086309 := by
    simpa [prefixWord, tailWord_2086309, baseEnd_2086309] using wordTrace_append hprefix tailTrace_2086309
  have hstable : (prefixWord ++ tailWord_2086309).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2086309).length < 2 ^ (prefixWord ++ tailWord_2086309).sum := by decide
  have hdescent : baseEnd_2086309 < baseStart_2086309 := by decide
  rcases family_descends (prefixWord ++ tailWord_2086309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2086356 : List Nat := [2, 4, 1, 2, 4, 1, 8]
def baseStart_2086356 : Nat := 118140960795 + 2086356 * 2 ^ 59
def prefixEnd_2086356 : Nat := 4983230072969 + 3 ^ 40 * 2086356 * 2
def baseEnd_2086356 : Nat := 26451936898566527314939

theorem tailTrace_2086356 : CollatzResearch.WordTrace tailWord_2086356 prefixEnd_2086356 26451936898566527314939 := by
  unfold tailWord_2086356
  simp only [CollatzResearch.WordTrace]
  refine ⟨38047827414748004040863461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50730436552997338721151281 38047827414748004040863461)
  ·
    refine ⟨7133967640265250757661899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38047827414748004040863461 7133967640265250757661899)
    ·
      refine ⟨10700951460397876136492849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7133967640265250757661899 10700951460397876136492849)
      ·
        refine ⟨8025713595298407102369637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10700951460397876136492849 8025713595298407102369637)
        ·
          refine ⟨1504821299118451331694307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8025713595298407102369637 1504821299118451331694307)
          ·
            refine ⟨2257231948677676997541461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1504821299118451331694307 2257231948677676997541461)
            ·
              refine ⟨26451936898566527314939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2257231948677676997541461 26451936898566527314939)
              ·
                rfl

theorem cell22_2086356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 8].length) (baseStart_2086356 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2086356 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2086356 prefixEnd_2086356 := by exact prefixLift 2086356
  have htrace : WordTrace (prefixWord ++ tailWord_2086356) baseStart_2086356 baseEnd_2086356 := by
    simpa [prefixWord, tailWord_2086356, baseEnd_2086356] using wordTrace_append hprefix tailTrace_2086356
  have hstable : (prefixWord ++ tailWord_2086356).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2086356).length < 2 ^ (prefixWord ++ tailWord_2086356).sum := by decide
  have hdescent : baseEnd_2086356 < baseStart_2086356 := by decide
  rcases family_descends (prefixWord ++ tailWord_2086356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2086367 : List Nat := [1, 1, 2, 3, 3, 1, 1, 3, 7]
def baseStart_2086367 : Nat := 118140960795 + 2086367 * 2 ^ 59
def prefixEnd_2086367 : Nat := 4983230072969 + 3 ^ 40 * 2086367 * 2
def baseEnd_2086367 : Nat := 238068687262031958492773

theorem tailTrace_2086367 : CollatzResearch.WordTrace tailWord_2086367 prefixEnd_2086367 238068687262031958492773 := by
  unfold tailWord_2086367
  simp only [CollatzResearch.WordTrace]
  refine ⟨76096056032456156960377355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50730704021637437973584903 76096056032456156960377355)
  ·
    refine ⟨114144084048684235440566033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76096056032456156960377355 114144084048684235440566033)
    ·
      refine ⟨85608063036513176580424525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114144084048684235440566033 85608063036513176580424525)
      ·
        refine ⟨32103023638692441217659197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85608063036513176580424525 32103023638692441217659197)
        ·
          refine ⟨12038633864509665456622199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32103023638692441217659197 12038633864509665456622199)
          ·
            refine ⟨18057950796764498184933299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12038633864509665456622199 18057950796764498184933299)
            ·
              refine ⟨27086926195146747277399949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18057950796764498184933299 27086926195146747277399949)
              ·
                refine ⟨10157597323180030229024981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27086926195146747277399949 10157597323180030229024981)
                ·
                  refine ⟨238068687262031958492773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10157597323180030229024981 238068687262031958492773)
                  ·
                    rfl

theorem cell22_2086367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 3, 7].length) (baseStart_2086367 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2086367 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2086367 prefixEnd_2086367 := by exact prefixLift 2086367
  have htrace : WordTrace (prefixWord ++ tailWord_2086367) baseStart_2086367 baseEnd_2086367 := by
    simpa [prefixWord, tailWord_2086367, baseEnd_2086367] using wordTrace_append hprefix tailTrace_2086367
  have hstable : (prefixWord ++ tailWord_2086367).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2086367).length < 2 ^ (prefixWord ++ tailWord_2086367).sum := by decide
  have hdescent : baseEnd_2086367 < baseStart_2086367 := by decide
  rcases family_descends (prefixWord ++ tailWord_2086367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2086371 : List Nat := [1, 1, 1, 6, 2, 1, 3, 1, 3, 3]
def baseStart_2086371 : Nat := 118140960795 + 2086371 * 2 ^ 59
def prefixEnd_2086371 : Nat := 4983230072969 + 3 ^ 40 * 2086371 * 2
def baseEnd_2086371 : Nat := 714207431067841198378307

theorem tailTrace_2086371 : CollatzResearch.WordTrace tailWord_2086371 prefixEnd_2086371 714207431067841198378307 := by
  unfold tailWord_2086371
  simp only [CollatzResearch.WordTrace]
  refine ⟨76096201924441665643522967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50730801282961110429015311 76096201924441665643522967)
  ·
    refine ⟨114144302886662498465284451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76096201924441665643522967 114144302886662498465284451)
    ·
      refine ⟨171216454329993747697926677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114144302886662498465284451 171216454329993747697926677)
      ·
        refine ⟨8025771296718456923340313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 171216454329993747697926677 8025771296718456923340313)
        ·
          refine ⟨6019328472538842692505235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8025771296718456923340313 6019328472538842692505235)
          ·
            refine ⟨9028992708808264038757853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6019328472538842692505235 9028992708808264038757853)
            ·
              refine ⟨3385872265803099014534195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9028992708808264038757853 3385872265803099014534195)
              ·
                refine ⟨5078808398704648521801293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3385872265803099014534195 5078808398704648521801293)
                ·
                  refine ⟨1904553149514243195675485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5078808398704648521801293 1904553149514243195675485)
                  ·
                    refine ⟨714207431067841198378307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1904553149514243195675485 714207431067841198378307)
                    ·
                      rfl

theorem cell22_2086371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 3, 1, 3, 3].length) (baseStart_2086371 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2086371 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2086371 prefixEnd_2086371 := by exact prefixLift 2086371
  have htrace : WordTrace (prefixWord ++ tailWord_2086371) baseStart_2086371 baseEnd_2086371 := by
    simpa [prefixWord, tailWord_2086371, baseEnd_2086371] using wordTrace_append hprefix tailTrace_2086371
  have hstable : (prefixWord ++ tailWord_2086371).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2086371).length < 2 ^ (prefixWord ++ tailWord_2086371).sum := by decide
  have hdescent : baseEnd_2086371 < baseStart_2086371 := by decide
  rcases family_descends (prefixWord ++ tailWord_2086371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2086384 : List Nat := [2, 1, 1, 1, 3, 5, 1, 3, 5]
def baseStart_2086384 : Nat := 118140960795 + 2086384 * 2 ^ 59
def prefixEnd_2086384 : Nat := 4983230072969 + 3 ^ 40 * 2086384 * 2
def baseEnd_2086384 : Nat := 238070627077837832601089

theorem tailTrace_2086384 : CollatzResearch.WordTrace tailWord_2086384 prefixEnd_2086384 238070627077837832601089 := by
  unfold tailWord_2086384
  simp only [CollatzResearch.WordTrace]
  refine ⟨38048338036697284431873103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50731117382263045909164137 38048338036697284431873103)
  ·
    refine ⟨57072507055045926647809655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38048338036697284431873103 57072507055045926647809655)
    ·
      refine ⟨85608760582568889971714483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57072507055045926647809655 85608760582568889971714483)
      ·
        refine ⟨128413140873853334957571725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85608760582568889971714483 128413140873853334957571725)
        ·
          refine ⟨48154927827695000609089397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128413140873853334957571725 48154927827695000609089397)
          ·
            refine ⟨4514524483846406307102131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 48154927827695000609089397 4514524483846406307102131)
            ·
              refine ⟨6771786725769609460653197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4514524483846406307102131 6771786725769609460653197)
              ·
                refine ⟨2539420022163603547744949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6771786725769609460653197 2539420022163603547744949)
                ·
                  refine ⟨238070627077837832601089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2539420022163603547744949 238070627077837832601089)
                  ·
                    rfl

theorem cell22_2086384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 1, 3, 5].length) (baseStart_2086384 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2086384 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2086384 prefixEnd_2086384 := by exact prefixLift 2086384
  have htrace : WordTrace (prefixWord ++ tailWord_2086384) baseStart_2086384 baseEnd_2086384 := by
    simpa [prefixWord, tailWord_2086384, baseEnd_2086384] using wordTrace_append hprefix tailTrace_2086384
  have hstable : (prefixWord ++ tailWord_2086384).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2086384).length < 2 ^ (prefixWord ++ tailWord_2086384).sum := by decide
  have hdescent : baseEnd_2086384 < baseStart_2086384 := by decide
  rcases family_descends (prefixWord ++ tailWord_2086384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2086429 : List Nat := [1, 4, 2, 2, 1, 1, 2, 3, 6]
def baseStart_2086429 : Nat := 118140960795 + 2086429 * 2 ^ 59
def prefixEnd_2086429 : Nat := 4983230072969 + 3 ^ 40 * 2086429 * 2
def baseEnd_2086429 : Nat := 238075761884382793476043

theorem tailTrace_2086429 : CollatzResearch.WordTrace tailWord_2086429 prefixEnd_2086429 238075761884382793476043 := by
  unfold tailWord_2086429
  simp only [CollatzResearch.WordTrace]
  refine ⟨76098317358231541549134341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50732211572154361032756227 76098317358231541549134341)
  ·
    refine ⟨14268434504668414040462689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76098317358231541549134341 14268434504668414040462689)
    ·
      refine ⟨10701325878501310530347017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14268434504668414040462689 10701325878501310530347017)
      ·
        refine ⟨8025994408875982897760263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10701325878501310530347017 8025994408875982897760263)
        ·
          refine ⟨12038991613313974346640395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8025994408875982897760263 12038991613313974346640395)
          ·
            refine ⟨18058487419970961519960593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12038991613313974346640395 18058487419970961519960593)
            ·
              refine ⟨13543865564978221139970445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18058487419970961519960593 13543865564978221139970445)
              ·
                refine ⟨5078949586866832927488917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13543865564978221139970445 5078949586866832927488917)
                ·
                  refine ⟨238075761884382793476043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5078949586866832927488917 238075761884382793476043)
                  ·
                    rfl

theorem cell22_2086429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 3, 6].length) (baseStart_2086429 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2086429 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2086429 prefixEnd_2086429 := by exact prefixLift 2086429
  have htrace : WordTrace (prefixWord ++ tailWord_2086429) baseStart_2086429 baseEnd_2086429 := by
    simpa [prefixWord, tailWord_2086429, baseEnd_2086429] using wordTrace_append hprefix tailTrace_2086429
  have hstable : (prefixWord ++ tailWord_2086429).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2086429).length < 2 ^ (prefixWord ++ tailWord_2086429).sum := by decide
  have hdescent : baseEnd_2086429 < baseStart_2086429 := by decide
  rcases family_descends (prefixWord ++ tailWord_2086429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2086444 : List Nat := [2, 2, 1, 1, 1, 2, 1, 1, 8, 3]
def baseStart_2086444 : Nat := 118140960795 + 2086444 * 2 ^ 59
def prefixEnd_2086444 : Nat := 4983230072969 + 3 ^ 40 * 2086444 * 2
def baseEnd_2086444 : Nat := 714232420459693341303083

theorem tailTrace_2086444 : CollatzResearch.WordTrace tailWord_2086444 prefixEnd_2086444 714232420459693341303083 := by
  unfold tailWord_2086444
  simp only [CollatzResearch.WordTrace]
  refine ⟨38049432226588599555465193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50732576302118132740620257 38049432226588599555465193)
  ·
    refine ⟨28537074169941449666598895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38049432226588599555465193 28537074169941449666598895)
    ·
      refine ⟨42805611254912174499898343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28537074169941449666598895 42805611254912174499898343)
      ·
        refine ⟨64208416882368261749847515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42805611254912174499898343 64208416882368261749847515)
        ·
          refine ⟨96312625323552392624771273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64208416882368261749847515 96312625323552392624771273)
          ·
            refine ⟨72234468992664294468578455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96312625323552392624771273 72234468992664294468578455)
            ·
              refine ⟨108351703488996441702867683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72234468992664294468578455 108351703488996441702867683)
              ·
                refine ⟨162527555233494662554301525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108351703488996441702867683 162527555233494662554301525)
                ·
                  refine ⟨1904619787892515576808221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 162527555233494662554301525 1904619787892515576808221)
                  ·
                    refine ⟨714232420459693341303083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1904619787892515576808221 714232420459693341303083)
                    ·
                      rfl

theorem cell22_2086444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 3].length) (baseStart_2086444 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2086444 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2086444 prefixEnd_2086444 := by exact prefixLift 2086444
  have htrace : WordTrace (prefixWord ++ tailWord_2086444) baseStart_2086444 baseEnd_2086444 := by
    simpa [prefixWord, tailWord_2086444, baseEnd_2086444] using wordTrace_append hprefix tailTrace_2086444
  have hstable : (prefixWord ++ tailWord_2086444).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2086444).length < 2 ^ (prefixWord ++ tailWord_2086444).sum := by decide
  have hdescent : baseEnd_2086444 < baseStart_2086444 := by decide
  rcases family_descends (prefixWord ++ tailWord_2086444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2086446 : List Nat := [4, 1, 3, 1, 2, 2, 1, 2, 6]
def baseStart_2086446 : Nat := 118140960795 + 2086446 * 2 ^ 59
def prefixEnd_2086446 : Nat := 4983230072969 + 3 ^ 40 * 2086446 * 2
def baseEnd_2086446 : Nat := 238077701700188667584359

theorem tailTrace_2086446 : CollatzResearch.WordTrace tailWord_2086446 prefixEnd_2086446 238077701700188667584359 := by
  unfold tailWord_2086446
  simp only [CollatzResearch.WordTrace]
  refine ⟨9512367174896244181562899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50732624932779968968335461 9512367174896244181562899)
  ·
    refine ⟨14268550762344366272344349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9512367174896244181562899 14268550762344366272344349)
    ·
      refine ⟨5350706535879137352129131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14268550762344366272344349 5350706535879137352129131)
      ·
        refine ⟨8026059803818706028193697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5350706535879137352129131 8026059803818706028193697)
        ·
          refine ⟨6019544852864029521145273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8026059803818706028193697 6019544852864029521145273)
          ·
            refine ⟨4514658639648022140858955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6019544852864029521145273 4514658639648022140858955)
            ·
              refine ⟨6771987959472033211288433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4514658639648022140858955 6771987959472033211288433)
              ·
                refine ⟨5078990969604024908466325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6771987959472033211288433 5078990969604024908466325)
                ·
                  refine ⟨238077701700188667584359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5078990969604024908466325 238077701700188667584359)
                  ·
                    rfl

theorem cell22_2086446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 1, 2, 6].length) (baseStart_2086446 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2086446 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2086446 prefixEnd_2086446 := by exact prefixLift 2086446
  have htrace : WordTrace (prefixWord ++ tailWord_2086446) baseStart_2086446 baseEnd_2086446 := by
    simpa [prefixWord, tailWord_2086446, baseEnd_2086446] using wordTrace_append hprefix tailTrace_2086446
  have hstable : (prefixWord ++ tailWord_2086446).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2086446).length < 2 ^ (prefixWord ++ tailWord_2086446).sum := by decide
  have hdescent : baseEnd_2086446 < baseStart_2086446 := by decide
  rcases family_descends (prefixWord ++ tailWord_2086446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2086540 : List Nat := [2, 2, 1, 2, 1, 1, 7, 2, 1, 3]
def baseStart_2086540 : Nat := 118140960795 + 2086540 * 2 ^ 59
def prefixEnd_2086540 : Nat := 4983230072969 + 3 ^ 40 * 2086540 * 2
def baseEnd_2086540 : Nat := 714265283221581090902789

theorem tailTrace_2086540 : CollatzResearch.WordTrace tailWord_2086540 prefixEnd_2086540 714265283221581090902789 := by
  unfold tailWord_2086540
  simp only [CollatzResearch.WordTrace]
  refine ⟨38051182930414703753212537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50734910573886271670950049 38051182930414703753212537)
  ·
    refine ⟨28538387197811027814909403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38051182930414703753212537 28538387197811027814909403)
    ·
      refine ⟨42807580796716541722364105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28538387197811027814909403 42807580796716541722364105)
      ·
        refine ⟨32105685597537406291773079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42807580796716541722364105 32105685597537406291773079)
        ·
          refine ⟨48158528396306109437659619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32105685597537406291773079 48158528396306109437659619)
          ·
            refine ⟨72237792594459164156489429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48158528396306109437659619 72237792594459164156489429)
            ·
              refine ⟨1693073263932636659917721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 72237792594459164156489429 1693073263932636659917721)
              ·
                refine ⟨1269804947949477494938291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1693073263932636659917721 1269804947949477494938291)
                ·
                  refine ⟨1904707421924216242407437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1269804947949477494938291 1904707421924216242407437)
                  ·
                    refine ⟨714265283221581090902789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1904707421924216242407437 714265283221581090902789)
                    ·
                      rfl

theorem cell22_2086540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 7, 2, 1, 3].length) (baseStart_2086540 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2086540 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2086540 prefixEnd_2086540 := by exact prefixLift 2086540
  have htrace : WordTrace (prefixWord ++ tailWord_2086540) baseStart_2086540 baseEnd_2086540 := by
    simpa [prefixWord, tailWord_2086540, baseEnd_2086540] using wordTrace_append hprefix tailTrace_2086540
  have hstable : (prefixWord ++ tailWord_2086540).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2086540).length < 2 ^ (prefixWord ++ tailWord_2086540).sum := by decide
  have hdescent : baseEnd_2086540 < baseStart_2086540 := by decide
  rcases family_descends (prefixWord ++ tailWord_2086540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2086596 : List Nat := [2, 3, 3, 1, 1, 1, 1, 2, 3, 5]
def baseStart_2086596 : Nat := 118140960795 + 2086596 * 2 ^ 59
def prefixEnd_2086596 : Nat := 4983230072969 + 3 ^ 40 * 2086596 * 2
def baseEnd_2086596 : Nat := 714284453166015611502617

theorem tailTrace_2086596 : CollatzResearch.WordTrace tailWord_2086596 prefixEnd_2086596 714284453166015611502617 := by
  unfold tailWord_2086596
  simp only [CollatzResearch.WordTrace]
  refine ⟨38052204174313264535231821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50736272232417686046975761 38052204174313264535231821)
  ·
    refine ⟨14269576565367474200711933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38052204174313264535231821 14269576565367474200711933)
    ·
      refine ⟨5351091212012802825266975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14269576565367474200711933 5351091212012802825266975)
      ·
        refine ⟨8026636818019204237900463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5351091212012802825266975 8026636818019204237900463)
        ·
          refine ⟨12039955227028806356850695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8026636818019204237900463 12039955227028806356850695)
          ·
            refine ⟨18059932840543209535276043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12039955227028806356850695 18059932840543209535276043)
            ·
              refine ⟨27089899260814814302914065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18059932840543209535276043 27089899260814814302914065)
              ·
                refine ⟨20317424445611110727185549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27089899260814814302914065 20317424445611110727185549)
                ·
                  refine ⟨7619034167104166522694581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20317424445611110727185549 7619034167104166522694581)
                  ·
                    refine ⟨714284453166015611502617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7619034167104166522694581 714284453166015611502617)
                    ·
                      rfl

theorem cell22_2086596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 2, 3, 5].length) (baseStart_2086596 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2086596 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2086596 prefixEnd_2086596 := by exact prefixLift 2086596
  have htrace : WordTrace (prefixWord ++ tailWord_2086596) baseStart_2086596 baseEnd_2086596 := by
    simpa [prefixWord, tailWord_2086596, baseEnd_2086596] using wordTrace_append hprefix tailTrace_2086596
  have hstable : (prefixWord ++ tailWord_2086596).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2086596).length < 2 ^ (prefixWord ++ tailWord_2086596).sum := by decide
  have hdescent : baseEnd_2086596 < baseStart_2086596 := by decide
  rcases family_descends (prefixWord ++ tailWord_2086596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2086692 : List Nat := [2, 3, 1, 3, 2, 1, 3, 3, 1, 3]
def baseStart_2086692 : Nat := 118140960795 + 2086692 * 2 ^ 59
def prefixEnd_2086692 : Nat := 4983230072969 + 3 ^ 40 * 2086692 * 2
def baseEnd_2086692 : Nat := 714317315927903361102323

theorem tailTrace_2086692 : CollatzResearch.WordTrace tailWord_2086692 prefixEnd_2086692 714317315927903361102323 := by
  unfold tailWord_2086692
  simp only [CollatzResearch.WordTrace]
  refine ⟨38053954878139368732979165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50738606504185824977305553 38053954878139368732979165)
  ·
    refine ⟨14270233079302263274867187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38053954878139368732979165 14270233079302263274867187)
    ·
      refine ⟨21405349618953394912300781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14270233079302263274867187 21405349618953394912300781)
      ·
        refine ⟨8027006107107523092112793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21405349618953394912300781 8027006107107523092112793)
        ·
          refine ⟨6020254580330642319084595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8027006107107523092112793 6020254580330642319084595)
          ·
            refine ⟨9030381870495963478626893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6020254580330642319084595 9030381870495963478626893)
            ·
              refine ⟨3386393201435986304485085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9030381870495963478626893 3386393201435986304485085)
              ·
                refine ⟨1269897450538494864181907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3386393201435986304485085 1269897450538494864181907)
                ·
                  refine ⟨1904846175807742296272861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1269897450538494864181907 1904846175807742296272861)
                  ·
                    refine ⟨714317315927903361102323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1904846175807742296272861 714317315927903361102323)
                    ·
                      rfl

theorem cell22_2086692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 3, 3, 1, 3].length) (baseStart_2086692 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2086692 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2086692 prefixEnd_2086692 := by exact prefixLift 2086692
  have htrace : WordTrace (prefixWord ++ tailWord_2086692) baseStart_2086692 baseEnd_2086692 := by
    simpa [prefixWord, tailWord_2086692, baseEnd_2086692] using wordTrace_append hprefix tailTrace_2086692
  have hstable : (prefixWord ++ tailWord_2086692).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2086692).length < 2 ^ (prefixWord ++ tailWord_2086692).sum := by decide
  have hdescent : baseEnd_2086692 < baseStart_2086692 := by decide
  rcases family_descends (prefixWord ++ tailWord_2086692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2086709 : List Nat := [1, 3, 3, 1, 4, 1, 3, 2, 1, 3]
def baseStart_2086709 : Nat := 118140960795 + 2086709 * 2 ^ 59
def prefixEnd_2086709 : Nat := 4983230072969 + 3 ^ 40 * 2086709 * 2
def baseEnd_2086709 : Nat := 714323135375320983427271

theorem tailTrace_2086709 : CollatzResearch.WordTrace tailWord_2086709 prefixEnd_2086709 714323135375320983427271 := by
  unfold tailWord_2086709
  simp only [CollatzResearch.WordTrace]
  refine ⟨76108529797217149369327181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50739019864811432912884787 76108529797217149369327181)
  ·
    refine ⟨28540698673956431013497693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76108529797217149369327181 28540698673956431013497693)
    ·
      refine ⟨10702762002733661630061635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28540698673956431013497693 10702762002733661630061635)
      ·
        refine ⟨16054143004100492445092453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10702762002733661630061635 16054143004100492445092453)
        ·
          refine ⟨3010151813268842333454835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16054143004100492445092453 3010151813268842333454835)
          ·
            refine ⟨4515227719903263500182253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3010151813268842333454835 4515227719903263500182253)
            ·
              refine ⟨1693210394963723812568345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4515227719903263500182253 1693210394963723812568345)
              ·
                refine ⟨1269907796222792859426259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1693210394963723812568345 1269907796222792859426259)
                ·
                  refine ⟨1904861694334189289139389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1269907796222792859426259 1904861694334189289139389)
                  ·
                    refine ⟨714323135375320983427271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1904861694334189289139389 714323135375320983427271)
                    ·
                      rfl

theorem cell22_2086709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 3, 2, 1, 3].length) (baseStart_2086709 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2086709 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2086709 prefixEnd_2086709 := by exact prefixLift 2086709
  have htrace : WordTrace (prefixWord ++ tailWord_2086709) baseStart_2086709 baseEnd_2086709 := by
    simpa [prefixWord, tailWord_2086709, baseEnd_2086709] using wordTrace_append hprefix tailTrace_2086709
  have hstable : (prefixWord ++ tailWord_2086709).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2086709).length < 2 ^ (prefixWord ++ tailWord_2086709).sum := by decide
  have hdescent : baseEnd_2086709 < baseStart_2086709 := by decide
  rcases family_descends (prefixWord ++ tailWord_2086709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2086765 : List Nat := [1, 5, 1, 1, 1, 1, 3, 4, 2, 3]
def baseStart_2086765 : Nat := 118140960795 + 2086765 * 2 ^ 59
def prefixEnd_2086765 : Nat := 4983230072969 + 3 ^ 40 * 2086765 * 2
def baseEnd_2086765 : Nat := 714342305319755504027099

theorem tailTrace_2086765 : CollatzResearch.WordTrace tailWord_2086765 prefixEnd_2086765 714342305319755504027099 := by
  unfold tailWord_2086765
  simp only [CollatzResearch.WordTrace]
  refine ⟨76110572285014270933365749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50740381523342847288910499 76110572285014270933365749)
  ·
    refine ⟨7135366151720087900003039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 76110572285014270933365749 7135366151720087900003039)
    ·
      refine ⟨10703049227580131850004559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7135366151720087900003039 10703049227580131850004559)
      ·
        refine ⟨16054573841370197775006839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10703049227580131850004559 16054573841370197775006839)
        ·
          refine ⟨24081860762055296662510259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16054573841370197775006839 24081860762055296662510259)
          ·
            refine ⟨36122791143082944993765389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24081860762055296662510259 36122791143082944993765389)
            ·
              refine ⟨13546046678656104372662021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36122791143082944993765389 13546046678656104372662021)
              ·
                refine ⟨2539883752248019569874129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13546046678656104372662021 2539883752248019569874129)
                ·
                  refine ⟨1904912814186014677405597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2539883752248019569874129 1904912814186014677405597)
                  ·
                    refine ⟨714342305319755504027099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1904912814186014677405597 714342305319755504027099)
                    ·
                      rfl

theorem cell22_2086765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 4, 2, 3].length) (baseStart_2086765 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2086765 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2086765 prefixEnd_2086765 := by exact prefixLift 2086765
  have htrace : WordTrace (prefixWord ++ tailWord_2086765) baseStart_2086765 baseEnd_2086765 := by
    simpa [prefixWord, tailWord_2086765, baseEnd_2086765] using wordTrace_append hprefix tailTrace_2086765
  have hstable : (prefixWord ++ tailWord_2086765).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2086765).length < 2 ^ (prefixWord ++ tailWord_2086765).sum := by decide
  have hdescent : baseEnd_2086765 < baseStart_2086765 := by decide
  rcases family_descends (prefixWord ++ tailWord_2086765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2086782 : List Nat := [4, 2, 3, 1, 1, 2, 2, 1, 1, 5]
def baseStart_2086782 : Nat := 118140960795 + 2086782 * 2 ^ 59
def prefixEnd_2086782 : Nat := 4983230072969 + 3 ^ 40 * 2086782 * 2
def baseEnd_2086782 : Nat := 714348124767173126352047

theorem tailTrace_2086782 : CollatzResearch.WordTrace tailWord_2086782 prefixEnd_2086782 714348124767173126352047 := by
  unfold tailWord_2086782
  simp only [CollatzResearch.WordTrace]
  refine ⟨9513899040744085354591825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50740794883968455224489733 9513899040744085354591825)
  ·
    refine ⟨7135424280558064015943869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9513899040744085354591825 7135424280558064015943869)
    ·
      refine ⟨2675784105209274005978951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7135424280558064015943869 2675784105209274005978951)
      ·
        refine ⟨4013676157813911008968427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2675784105209274005978951 4013676157813911008968427)
        ·
          refine ⟨6020514236720866513452641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4013676157813911008968427 6020514236720866513452641)
          ·
            refine ⟨4515385677540649885089481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6020514236720866513452641 4515385677540649885089481)
            ·
              refine ⟨3386539258155487413817111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4515385677540649885089481 3386539258155487413817111)
              ·
                refine ⟨5079808887233231120725667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3386539258155487413817111 5079808887233231120725667)
                ·
                  refine ⟨7619713330849846681088501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5079808887233231120725667 7619713330849846681088501)
                  ·
                    refine ⟨714348124767173126352047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7619713330849846681088501 714348124767173126352047)
                    ·
                      rfl

theorem cell22_2086782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_2086782 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2086782 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2086782 prefixEnd_2086782 := by exact prefixLift 2086782
  have htrace : WordTrace (prefixWord ++ tailWord_2086782) baseStart_2086782 baseEnd_2086782 := by
    simpa [prefixWord, tailWord_2086782, baseEnd_2086782] using wordTrace_append hprefix tailTrace_2086782
  have hstable : (prefixWord ++ tailWord_2086782).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2086782).length < 2 ^ (prefixWord ++ tailWord_2086782).sum := by decide
  have hdescent : baseEnd_2086782 < baseStart_2086782 := by decide
  rcases family_descends (prefixWord ++ tailWord_2086782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2086840 : List Nat := [2, 1, 2, 1, 2, 3, 5, 1, 5]
def baseStart_2086840 : Nat := 118140960795 + 2086840 * 2 ^ 59
def prefixEnd_2086840 : Nat := 4983230072969 + 3 ^ 40 * 2086840 * 2
def baseEnd_2086840 : Nat := 238122659784160102800623

theorem tailTrace_2086840 : CollatzResearch.WordTrace tailWord_2086840 prefixEnd_2086840 238122659784160102800623 := by
  unfold tailWord_2086840
  simp only [CollatzResearch.WordTrace]
  refine ⟨38056653879871279371172987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50742205173161705828230649 38056653879871279371172987)
  ·
    refine ⟨57084980819806919056759481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38056653879871279371172987 57084980819806919056759481)
    ·
      refine ⟨42813735614855189292569611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57084980819806919056759481 42813735614855189292569611)
      ·
        refine ⟨64220603422282783938854417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42813735614855189292569611 64220603422282783938854417)
        ·
          refine ⟨48165452566712087954140813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64220603422282783938854417 48165452566712087954140813)
          ·
            refine ⟨18062044712517032982802805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48165452566712087954140813 18062044712517032982802805)
            ·
              refine ⟨1693316691798471842137763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18062044712517032982802805 1693316691798471842137763)
              ·
                refine ⟨2539975037697707763206645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1693316691798471842137763 2539975037697707763206645)
                ·
                  refine ⟨238122659784160102800623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2539975037697707763206645 238122659784160102800623)
                  ·
                    rfl

theorem cell22_2086840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 5, 1, 5].length) (baseStart_2086840 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2086840 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2086840 prefixEnd_2086840 := by exact prefixLift 2086840
  have htrace : WordTrace (prefixWord ++ tailWord_2086840) baseStart_2086840 baseEnd_2086840 := by
    simpa [prefixWord, tailWord_2086840, baseEnd_2086840] using wordTrace_append hprefix tailTrace_2086840
  have hstable : (prefixWord ++ tailWord_2086840).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2086840).length < 2 ^ (prefixWord ++ tailWord_2086840).sum := by decide
  have hdescent : baseEnd_2086840 < baseStart_2086840 := by decide
  rcases family_descends (prefixWord ++ tailWord_2086840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2086913 : List Nat := [1, 2, 4, 1, 2, 1, 1, 10]
def baseStart_2086913 : Nat := 118140960795 + 2086913 * 2 ^ 59
def prefixEnd_2086913 : Nat := 4983230072969 + 3 ^ 40 * 2086913 * 2
def baseEnd_2086913 : Nat := 79376996527148050147405

theorem tailTrace_2086913 : CollatzResearch.WordTrace tailWord_2086913 prefixEnd_2086913 79376996527148050147405 := by
  unfold tailWord_2086913
  simp only [CollatzResearch.WordTrace]
  refine ⟨76115970288478092209753393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50743980192318728139835595 76115970288478092209753393)
  ·
    refine ⟨57086977716358569157315045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76115970288478092209753393 57086977716358569157315045)
    ·
      refine ⟨10703808321817231716996571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57086977716358569157315045 10703808321817231716996571)
      ·
        refine ⟨16055712482725847575494857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10703808321817231716996571 16055712482725847575494857)
        ·
          refine ⟨12041784362044385681621143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16055712482725847575494857 12041784362044385681621143)
          ·
            refine ⟨18062676543066578522431715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12041784362044385681621143 18062676543066578522431715)
            ·
              refine ⟨27094014814599867783647573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18062676543066578522431715 27094014814599867783647573)
              ·
                refine ⟨79376996527148050147405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 27094014814599867783647573 79376996527148050147405)
                ·
                  rfl

theorem cell22_2086913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 10].length) (baseStart_2086913 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2086913 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2086913 prefixEnd_2086913 := by exact prefixLift 2086913
  have htrace : WordTrace (prefixWord ++ tailWord_2086913) baseStart_2086913 baseEnd_2086913 := by
    simpa [prefixWord, tailWord_2086913, baseEnd_2086913] using wordTrace_append hprefix tailTrace_2086913
  have hstable : (prefixWord ++ tailWord_2086913).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2086913).length < 2 ^ (prefixWord ++ tailWord_2086913).sum := by decide
  have hdescent : baseEnd_2086913 < baseStart_2086913 := by decide
  rcases family_descends (prefixWord ++ tailWord_2086913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2086930 : List Nat := [3, 2, 5, 12]
def baseStart_2086930 : Nat := 118140960795 + 2086930 * 2 ^ 59
def prefixEnd_2086930 : Nat := 4983230072969 + 3 ^ 40 * 2086930 * 2
def baseEnd_2086930 : Nat := 979970902869341664817

theorem tailTrace_2086930 : CollatzResearch.WordTrace tailWord_2086930 prefixEnd_2086930 979970902869341664817 := by
  unfold tailWord_2086930
  simp only [CollatzResearch.WordTrace]
  refine ⟨19029147582354126028280561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50744393552944336075414829 19029147582354126028280561)
  ·
    refine ⟨14271860686765594521210421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19029147582354126028280561 14271860686765594521210421)
    ·
      refine ⟨1337986939384274486363477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14271860686765594521210421 1337986939384274486363477)
      ·
        refine ⟨979970902869341664817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 12 1337986939384274486363477 979970902869341664817)
        ·
          rfl

theorem cell22_2086930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 12].length) (baseStart_2086930 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2086930 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2086930 prefixEnd_2086930 := by exact prefixLift 2086930
  have htrace : WordTrace (prefixWord ++ tailWord_2086930) baseStart_2086930 baseEnd_2086930 := by
    simpa [prefixWord, tailWord_2086930, baseEnd_2086930] using wordTrace_append hprefix tailTrace_2086930
  have hstable : (prefixWord ++ tailWord_2086930).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2086930).length < 2 ^ (prefixWord ++ tailWord_2086930).sum := by decide
  have hdescent : baseEnd_2086930 < baseStart_2086930 := by decide
  rcases family_descends (prefixWord ++ tailWord_2086930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2086943 : List Nat := [1, 1, 2, 4, 1, 2, 1, 1, 1, 8]
def baseStart_2086943 : Nat := 118140960795 + 2086943 * 2 ^ 59
def prefixEnd_2086943 : Nat := 4983230072969 + 3 ^ 40 * 2086943 * 2
def baseEnd_2086943 : Nat := 714403238357422373076553

theorem tailTrace_2086943 : CollatzResearch.WordTrace tailWord_2086943 prefixEnd_2086943 714403238357422373076553 := by
  unfold tailWord_2086943
  simp only [CollatzResearch.WordTrace]
  refine ⟨76117064478369407333345483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50744709652246271555563655 76117064478369407333345483)
  ·
    refine ⟨114175596717554111000018225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76117064478369407333345483 114175596717554111000018225)
    ·
      refine ⟨85631697538165583250013669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114175596717554111000018225 85631697538165583250013669)
      ·
        refine ⟨16055943288406046859377563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85631697538165583250013669 16055943288406046859377563)
        ·
          refine ⟨24083914932609070289066345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16055943288406046859377563 24083914932609070289066345)
          ·
            refine ⟨18062936199456802716799759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24083914932609070289066345 18062936199456802716799759)
            ·
              refine ⟨27094404299185204075199639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18062936199456802716799759 27094404299185204075199639)
              ·
                refine ⟨40641606448777806112799459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27094404299185204075199639 40641606448777806112799459)
                ·
                  refine ⟨60962409673166709169199189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40641606448777806112799459 60962409673166709169199189)
                  ·
                    refine ⟨714403238357422373076553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 60962409673166709169199189 714403238357422373076553)
                    ·
                      rfl

theorem cell22_2086943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 1, 1, 8].length) (baseStart_2086943 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2086943 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2086943 prefixEnd_2086943 := by exact prefixLift 2086943
  have htrace : WordTrace (prefixWord ++ tailWord_2086943) baseStart_2086943 baseEnd_2086943 := by
    simpa [prefixWord, tailWord_2086943, baseEnd_2086943] using wordTrace_append hprefix tailTrace_2086943
  have hstable : (prefixWord ++ tailWord_2086943).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2086943).length < 2 ^ (prefixWord ++ tailWord_2086943).sum := by decide
  have hdescent : baseEnd_2086943 < baseStart_2086943 := by decide
  rcases family_descends (prefixWord ++ tailWord_2086943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2086962 : List Nat := [3, 2, 1, 1, 2, 4, 1, 2, 3, 3]
def baseStart_2086962 : Nat := 118140960795 + 2086962 * 2 ^ 59
def prefixEnd_2086962 : Nat := 4983230072969 + 3 ^ 40 * 2086962 * 2
def baseEnd_2086962 : Nat := 714409742445712656851495

theorem tailTrace_2086962 : CollatzResearch.WordTrace tailWord_2086962 prefixEnd_2086962 714409742445712656851495 := by
  unfold tailWord_2086962
  simp only [CollatzResearch.WordTrace]
  refine ⟨19029439366325143394571785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50745171643533715718858093 19029439366325143394571785)
  ·
    refine ⟨14272079524743857545928839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19029439366325143394571785 14272079524743857545928839)
    ·
      refine ⟨21408119287115786318893259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14272079524743857545928839 21408119287115786318893259)
      ·
        refine ⟨32112178930673679478339889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21408119287115786318893259 32112178930673679478339889)
        ·
          refine ⟨24084134198005259608754917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32112178930673679478339889 24084134198005259608754917)
          ·
            refine ⟨4515775162125986176641547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24084134198005259608754917 4515775162125986176641547)
            ·
              refine ⟨6773662743188979264962321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4515775162125986176641547 6773662743188979264962321)
              ·
                refine ⟨5080247057391734448721741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6773662743188979264962321 5080247057391734448721741)
                ·
                  refine ⟨1905092646521900418270653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5080247057391734448721741 1905092646521900418270653)
                  ·
                    refine ⟨714409742445712656851495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1905092646521900418270653 714409742445712656851495)
                    ·
                      rfl

theorem cell22_2086962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 1, 2, 3, 3].length) (baseStart_2086962 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2086962 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2086962 prefixEnd_2086962 := by exact prefixLift 2086962
  have htrace : WordTrace (prefixWord ++ tailWord_2086962) baseStart_2086962 baseEnd_2086962 := by
    simpa [prefixWord, tailWord_2086962, baseEnd_2086962] using wordTrace_append hprefix tailTrace_2086962
  have hstable : (prefixWord ++ tailWord_2086962).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2086962).length < 2 ^ (prefixWord ++ tailWord_2086962).sum := by decide
  have hdescent : baseEnd_2086962 < baseStart_2086962 := by decide
  rcases family_descends (prefixWord ++ tailWord_2086962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2086964 : List Nat := [2, 5, 1, 2, 2, 1, 3, 6]
def baseStart_2086964 : Nat := 118140960795 + 2086964 * 2 ^ 59
def prefixEnd_2086964 : Nat := 4983230072969 + 3 ^ 40 * 2086964 * 2
def baseEnd_2086964 : Nat := 79378936342953924255721

theorem tailTrace_2086964 : CollatzResearch.WordTrace tailWord_2086964 prefixEnd_2086964 79378936342953924255721 := by
  unfold tailWord_2086964
  simp only [CollatzResearch.WordTrace]
  refine ⟨38058915205646663959929973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50745220274195551946573297 38058915205646663959929973)
  ·
    refine ⟨3568023300529374746243435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 38058915205646663959929973 3568023300529374746243435)
    ·
      refine ⟨5352034950794062119365153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3568023300529374746243435 5352034950794062119365153)
      ·
        refine ⟨4014026213095546589523865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5352034950794062119365153 4014026213095546589523865)
        ·
          refine ⟨3010519659821659942142899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4014026213095546589523865 3010519659821659942142899)
          ·
            refine ⟨4515779489732489913214349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3010519659821659942142899 4515779489732489913214349)
            ·
              refine ⟨1693417308649683717455381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4515779489732489913214349 1693417308649683717455381)
              ·
                refine ⟨79378936342953924255721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1693417308649683717455381 79378936342953924255721)
                ·
                  rfl

theorem cell22_2086964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 3, 6].length) (baseStart_2086964 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2086964 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2086964 prefixEnd_2086964 := by exact prefixLift 2086964
  have htrace : WordTrace (prefixWord ++ tailWord_2086964) baseStart_2086964 baseEnd_2086964 := by
    simpa [prefixWord, tailWord_2086964, baseEnd_2086964] using wordTrace_append hprefix tailTrace_2086964
  have hstable : (prefixWord ++ tailWord_2086964).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2086964).length < 2 ^ (prefixWord ++ tailWord_2086964).sum := by decide
  have hdescent : baseEnd_2086964 < baseStart_2086964 := by decide
  rcases family_descends (prefixWord ++ tailWord_2086964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2086990 : List Nat := [4, 1, 1, 1, 1, 4, 1, 2, 2, 5]
def baseStart_2086990 : Nat := 118140960795 + 2086990 * 2 ^ 59
def prefixEnd_2086990 : Nat := 4983230072969 + 3 ^ 40 * 2086990 * 2
def baseEnd_2086990 : Nat := 714419327417929917151409

theorem tailTrace_2086990 : CollatzResearch.WordTrace tailWord_2086990 prefixEnd_2086990 714419327417929917151409 := by
  unfold tailWord_2086990
  simp only [CollatzResearch.WordTrace]
  refine ⟨9514847338649891795038303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50745852472799422906870949 9514847338649891795038303)
  ·
    refine ⟨14272271007974837692557455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9514847338649891795038303 14272271007974837692557455)
    ·
      refine ⟨21408406511962256538836183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14272271007974837692557455 21408406511962256538836183)
      ·
        refine ⟨32112609767943384808254275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21408406511962256538836183 32112609767943384808254275)
        ·
          refine ⟨48168914651915077212381413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32112609767943384808254275 48168914651915077212381413)
          ·
            refine ⟨9031671497234076977321515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48168914651915077212381413 9031671497234076977321515)
            ·
              refine ⟨13547507245851115465982273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9031671497234076977321515 13547507245851115465982273)
              ·
                refine ⟨10160630434388336599486705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13547507245851115465982273 10160630434388336599486705)
                ·
                  refine ⟨7620472825791252449615029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10160630434388336599486705 7620472825791252449615029)
                  ·
                    refine ⟨714419327417929917151409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7620472825791252449615029 714419327417929917151409)
                    ·
                      rfl

theorem cell22_2086990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 2, 2, 5].length) (baseStart_2086990 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2086990 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2086990 prefixEnd_2086990 := by exact prefixLift 2086990
  have htrace : WordTrace (prefixWord ++ tailWord_2086990) baseStart_2086990 baseEnd_2086990 := by
    simpa [prefixWord, tailWord_2086990, baseEnd_2086990] using wordTrace_append hprefix tailTrace_2086990
  have hstable : (prefixWord ++ tailWord_2086990).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2086990).length < 2 ^ (prefixWord ++ tailWord_2086990).sum := by decide
  have hdescent : baseEnd_2086990 < baseStart_2086990 := by decide
  rcases family_descends (prefixWord ++ tailWord_2086990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2087020 : List Nat := [2, 2, 1, 1, 3, 3, 2, 2, 6]
def baseStart_2087020 : Nat := 118140960795 + 2087020 * 2 ^ 59
def prefixEnd_2087020 : Nat := 4983230072969 + 3 ^ 40 * 2087020 * 2
def baseEnd_2087020 : Nat := 238143199010339946300439

theorem tailTrace_2087020 : CollatzResearch.WordTrace tailWord_2087020 prefixEnd_2087020 238143199010339946300439 := by
  unfold tailWord_2087020
  simp only [CollatzResearch.WordTrace]
  refine ⟨38059936449545224741949257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50746581932726966322599009 38059936449545224741949257)
  ·
    refine ⟨28544952337158918556461943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38059936449545224741949257 28544952337158918556461943)
    ·
      refine ⟨42817428505738377834692915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28544952337158918556461943 42817428505738377834692915)
      ·
        refine ⟨64226142758607566752039373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42817428505738377834692915 64226142758607566752039373)
        ·
          refine ⟨24084803534477837532014765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64226142758607566752039373 24084803534477837532014765)
          ·
            refine ⟨9031801325429189074505537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24084803534477837532014765 9031801325429189074505537)
            ·
              refine ⟨6773850994071891805879153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9031801325429189074505537 6773850994071891805879153)
              ·
                refine ⟨5080388245553918854409365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6773850994071891805879153 5080388245553918854409365)
                ·
                  refine ⟨238143199010339946300439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5080388245553918854409365 238143199010339946300439)
                  ·
                    rfl

theorem cell22_2087020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 6].length) (baseStart_2087020 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2087020 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2087020 prefixEnd_2087020 := by exact prefixLift 2087020
  have htrace : WordTrace (prefixWord ++ tailWord_2087020) baseStart_2087020 baseEnd_2087020 := by
    simpa [prefixWord, tailWord_2087020, baseEnd_2087020] using wordTrace_append hprefix tailTrace_2087020
  have hstable : (prefixWord ++ tailWord_2087020).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2087020).length < 2 ^ (prefixWord ++ tailWord_2087020).sum := by decide
  have hdescent : baseEnd_2087020 < baseStart_2087020 := by decide
  rcases family_descends (prefixWord ++ tailWord_2087020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2087054 : List Nat := [4, 1, 1, 3, 3, 2, 1, 1, 6]
def baseStart_2087054 : Nat := 118140960795 + 2087054 * 2 ^ 59
def prefixEnd_2087054 : Nat := 4983230072969 + 3 ^ 40 * 2087054 * 2
def baseEnd_2087054 : Nat := 238147078641951694517071

theorem tailTrace_2087054 : CollatzResearch.WordTrace tailWord_2087054 prefixEnd_2087054 238147078641951694517071 := by
  unfold tailWord_2087054
  simp only [CollatzResearch.WordTrace]
  refine ⟨9515139122620909161329527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50747408653978182193757477 9515139122620909161329527)
  ·
    refine ⟨14272708683931363741994291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9515139122620909161329527 14272708683931363741994291)
    ·
      refine ⟨21409063025897045612991437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14272708683931363741994291 21409063025897045612991437)
      ·
        refine ⟨8028398634711392104871789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21409063025897045612991437 8028398634711392104871789)
        ·
          refine ⟨3010649488016772039326921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8028398634711392104871789 3010649488016772039326921)
          ·
            refine ⟨2257987116012579029495191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3010649488016772039326921 2257987116012579029495191)
            ·
              refine ⟨3386980674018868544242787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2257987116012579029495191 3386980674018868544242787)
              ·
                refine ⟨5080471011028302816364181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3386980674018868544242787 5080471011028302816364181)
                ·
                  refine ⟨238147078641951694517071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5080471011028302816364181 238147078641951694517071)
                  ·
                    rfl

theorem cell22_2087054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 1, 1, 6].length) (baseStart_2087054 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2087054 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2087054 prefixEnd_2087054 := by exact prefixLift 2087054
  have htrace : WordTrace (prefixWord ++ tailWord_2087054) baseStart_2087054 baseEnd_2087054 := by
    simpa [prefixWord, tailWord_2087054, baseEnd_2087054] using wordTrace_append hprefix tailTrace_2087054
  have hstable : (prefixWord ++ tailWord_2087054).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2087054).length < 2 ^ (prefixWord ++ tailWord_2087054).sum := by decide
  have hdescent : baseEnd_2087054 < baseStart_2087054 := by decide
  rcases family_descends (prefixWord ++ tailWord_2087054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2087069 : List Nat := [1, 4, 2, 1, 1, 4, 1, 3, 2, 3]
def baseStart_2087069 : Nat := 118140960795 + 2087069 * 2 ^ 59
def prefixEnd_2087069 : Nat := 4983230072969 + 3 ^ 40 * 2087069 * 2
def baseEnd_2087069 : Nat := 714446370732400044426167

theorem tailTrace_2087069 : CollatzResearch.WordTrace tailWord_2087069 prefixEnd_2087069 714446370732400044426167 := by
  unfold tailWord_2087069
  simp only [CollatzResearch.WordTrace]
  refine ⟨76121660075912930852432261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50747773383941953901621507 76121660075912930852432261)
  ·
    refine ⟨14272811264233674534831049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76121660075912930852432261 14272811264233674534831049)
    ·
      refine ⟨10704608448175255901123287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14272811264233674534831049 10704608448175255901123287)
      ·
        refine ⟨16056912672262883851684931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10704608448175255901123287 16056912672262883851684931)
        ·
          refine ⟨24085369008394325777527397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16056912672262883851684931 24085369008394325777527397)
          ·
            refine ⟨4516006689073936083286387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24085369008394325777527397 4516006689073936083286387)
            ·
              refine ⟨6774010033610904124929581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4516006689073936083286387 6774010033610904124929581)
              ·
                refine ⟨2540253762604089046848593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6774010033610904124929581 2540253762604089046848593)
                ·
                  refine ⟨1905190321953066785136445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2540253762604089046848593 1905190321953066785136445)
                  ·
                    refine ⟨714446370732400044426167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1905190321953066785136445 714446370732400044426167)
                    ·
                      rfl

theorem cell22_2087069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 1, 3, 2, 3].length) (baseStart_2087069 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2087069 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2087069 prefixEnd_2087069 := by exact prefixLift 2087069
  have htrace : WordTrace (prefixWord ++ tailWord_2087069) baseStart_2087069 baseEnd_2087069 := by
    simpa [prefixWord, tailWord_2087069, baseEnd_2087069] using wordTrace_append hprefix tailTrace_2087069
  have hstable : (prefixWord ++ tailWord_2087069).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2087069).length < 2 ^ (prefixWord ++ tailWord_2087069).sum := by decide
  have hdescent : baseEnd_2087069 < baseStart_2087069 := by decide
  rcases family_descends (prefixWord ++ tailWord_2087069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2087086 : List Nat := [4, 1, 4, 2, 1, 1, 1, 2, 1, 5]
def baseStart_2087086 : Nat := 118140960795 + 2087086 * 2 ^ 59
def prefixEnd_2087086 : Nat := 4983230072969 + 3 ^ 40 * 2087086 * 2
def baseEnd_2087086 : Nat := 714452190179817666751115

theorem tailTrace_2087086 : CollatzResearch.WordTrace tailWord_2087086 prefixEnd_2087086 714452190179817666751115 := by
  unfold tailWord_2087086
  simp only [CollatzResearch.WordTrace]
  refine ⟨9515285014606417844475139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50748186744567561837200741 9515285014606417844475139)
  ·
    refine ⟨14272927521909626766712709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9515285014606417844475139 14272927521909626766712709)
    ·
      refine ⟨2676173910358055018758633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14272927521909626766712709 2676173910358055018758633)
      ·
        refine ⟨2007130432768541264068975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2676173910358055018758633 2007130432768541264068975)
        ·
          refine ⟨3010695649152811896103463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2007130432768541264068975 3010695649152811896103463)
          ·
            refine ⟨4516043473729217844155195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3010695649152811896103463 4516043473729217844155195)
            ·
              refine ⟨6774065210593826766232793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4516043473729217844155195 6774065210593826766232793)
              ·
                refine ⟨5080548907945370074674595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6774065210593826766232793 5080548907945370074674595)
                ·
                  refine ⟨7620823361918055112011893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5080548907945370074674595 7620823361918055112011893)
                  ·
                    refine ⟨714452190179817666751115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7620823361918055112011893 714452190179817666751115)
                    ·
                      rfl

theorem cell22_2087086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 1, 2, 1, 5].length) (baseStart_2087086 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2087086 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2087086 prefixEnd_2087086 := by exact prefixLift 2087086
  have htrace : WordTrace (prefixWord ++ tailWord_2087086) baseStart_2087086 baseEnd_2087086 := by
    simpa [prefixWord, tailWord_2087086, baseEnd_2087086] using wordTrace_append hprefix tailTrace_2087086
  have hstable : (prefixWord ++ tailWord_2087086).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2087086).length < 2 ^ (prefixWord ++ tailWord_2087086).sum := by decide
  have hdescent : baseEnd_2087086 < baseStart_2087086 := by decide
  rcases family_descends (prefixWord ++ tailWord_2087086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2087105 : List Nat := [1, 2, 6, 1, 3, 1, 2, 2, 4]
def baseStart_2087105 : Nat := 118140960795 + 2087105 * 2 ^ 59
def prefixEnd_2087105 : Nat := 4983230072969 + 3 ^ 40 * 2087105 * 2
def baseEnd_2087105 : Nat := 238152898089369316842019

theorem tailTrace_2087105 : CollatzResearch.WordTrace tailWord_2087105 prefixEnd_2087105 238152898089369316842019 := by
  unfold tailWord_2087105
  simp only [CollatzResearch.WordTrace]
  refine ⟨76122973103782509000742769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50748648735855006000495179 76122973103782509000742769)
  ·
    refine ⟨57092229827836881750557077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76122973103782509000742769 57092229827836881750557077)
    ·
      refine ⟨2676198273179853832057363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 57092229827836881750557077 2676198273179853832057363)
      ·
        refine ⟨4014297409769780748086045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2676198273179853832057363 4014297409769780748086045)
        ·
          refine ⟨1505361528663667780532267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4014297409769780748086045 1505361528663667780532267)
          ·
            refine ⟨2258042292995501670798401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1505361528663667780532267 2258042292995501670798401)
            ·
              refine ⟨1693531719746626253098801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2258042292995501670798401 1693531719746626253098801)
              ·
                refine ⟨1270148789809969689824101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1693531719746626253098801 1270148789809969689824101)
                ·
                  refine ⟨238152898089369316842019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1270148789809969689824101 238152898089369316842019)
                  ·
                    rfl

theorem cell22_2087105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 2, 2, 4].length) (baseStart_2087105 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2087105 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2087105 prefixEnd_2087105 := by exact prefixLift 2087105
  have htrace : WordTrace (prefixWord ++ tailWord_2087105) baseStart_2087105 baseEnd_2087105 := by
    simpa [prefixWord, tailWord_2087105, baseEnd_2087105] using wordTrace_append hprefix tailTrace_2087105
  have hstable : (prefixWord ++ tailWord_2087105).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2087105).length < 2 ^ (prefixWord ++ tailWord_2087105).sum := by decide
  have hdescent : baseEnd_2087105 < baseStart_2087105 := by decide
  rcases family_descends (prefixWord ++ tailWord_2087105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
