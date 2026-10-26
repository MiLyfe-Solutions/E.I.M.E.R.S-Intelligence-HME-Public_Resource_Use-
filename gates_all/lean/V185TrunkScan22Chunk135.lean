import V185TrunkScan22Chunk134

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_1206766 : List Nat := [4, 1, 2, 1, 2, 4, 2, 1, 1, 4]
def baseStart_1206766 : Nat := 118140960795 + 1206766 * 2 ^ 59
def prefixEnd_1206766 : Nat := 4983230072969 + 3 ^ 40 * 1206766 * 2
def baseEnd_1206766 : Nat := 413100663669153837450127

theorem tailTrace_1206766 : CollatzResearch.WordTrace tailWord_1206766 prefixEnd_1206766 413100663669153837450127 := by
  unfold tailWord_1206766
  simp only [CollatzResearch.WordTrace]
  refine ⟨5501796493262544508689019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29342914630733570713008101 5501796493262544508689019)
  ·
    refine ⟨8252694739893816763033529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5501796493262544508689019 8252694739893816763033529)
    ·
      refine ⟨6189521054920362572275147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8252694739893816763033529 6189521054920362572275147)
      ·
        refine ⟨9284281582380543858412721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6189521054920362572275147 9284281582380543858412721)
        ·
          refine ⟨6963211186785407893809541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9284281582380543858412721 6963211186785407893809541)
          ·
            refine ⟨1305602097522263980089289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6963211186785407893809541 1305602097522263980089289)
            ·
              refine ⟨979201573141697985066967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1305602097522263980089289 979201573141697985066967)
              ·
                refine ⟨1468802359712546977600451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 979201573141697985066967 1468802359712546977600451)
                ·
                  refine ⟨2203203539568820466400677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1468802359712546977600451 2203203539568820466400677)
                  ·
                    refine ⟨413100663669153837450127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2203203539568820466400677 413100663669153837450127)
                    ·
                      rfl

theorem cell22_1206766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 2, 1, 1, 4].length) (baseStart_1206766 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1206766 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1206766 prefixEnd_1206766 := by exact prefixLift 1206766
  have htrace : WordTrace (prefixWord ++ tailWord_1206766) baseStart_1206766 baseEnd_1206766 := by
    simpa [prefixWord, tailWord_1206766, baseEnd_1206766] using wordTrace_append hprefix tailTrace_1206766
  have hstable : (prefixWord ++ tailWord_1206766).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1206766).length < 2 ^ (prefixWord ++ tailWord_1206766).sum := by decide
  have hdescent : baseEnd_1206766 < baseStart_1206766 := by decide
  rcases family_descends (prefixWord ++ tailWord_1206766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1206796 : List Nat := [2, 2, 1, 2, 4, 2, 3, 1, 2, 3]
def baseStart_1206796 : Nat := 118140960795 + 1206796 * 2 ^ 59
def prefixEnd_1206796 : Nat := 4983230072969 + 3 ^ 40 * 1206796 * 2
def baseEnd_1206796 : Nat := 413110933282243759200035

theorem tailTrace_1206796 : CollatzResearch.WordTrace tailWord_1206796 prefixEnd_1206796 413110933282243759200035 := by
  unfold tailWord_1206796
  simp only [CollatzResearch.WordTrace]
  refine ⟨22007733067995835596552121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29343644090661114128736161 22007733067995835596552121)
  ·
    refine ⟨16505799800996876697414091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22007733067995835596552121 16505799800996876697414091)
    ·
      refine ⟨24758699701495315046121137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16505799800996876697414091 24758699701495315046121137)
      ·
        refine ⟨18569024776121486284590853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24758699701495315046121137 18569024776121486284590853)
        ·
          refine ⟨3481692145522778678360785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18569024776121486284590853 3481692145522778678360785)
          ·
            refine ⟨2611269109142084008770589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3481692145522778678360785 2611269109142084008770589)
            ·
              refine ⟨979225915928281503288971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2611269109142084008770589 979225915928281503288971)
              ·
                refine ⟨1468838873892422254933457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 979225915928281503288971 1468838873892422254933457)
                ·
                  refine ⟨1101629155419316691200093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1468838873892422254933457 1101629155419316691200093)
                  ·
                    refine ⟨413110933282243759200035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1101629155419316691200093 413110933282243759200035)
                    ·
                      rfl

theorem cell22_1206796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 3, 1, 2, 3].length) (baseStart_1206796 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1206796 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1206796 prefixEnd_1206796 := by exact prefixLift 1206796
  have htrace : WordTrace (prefixWord ++ tailWord_1206796) baseStart_1206796 baseEnd_1206796 := by
    simpa [prefixWord, tailWord_1206796, baseEnd_1206796] using wordTrace_append hprefix tailTrace_1206796
  have hstable : (prefixWord ++ tailWord_1206796).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1206796).length < 2 ^ (prefixWord ++ tailWord_1206796).sum := by decide
  have hdescent : baseEnd_1206796 < baseStart_1206796 := by decide
  rcases family_descends (prefixWord ++ tailWord_1206796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1206837 : List Nat := [1, 3, 3, 1, 1, 2, 2, 4, 5]
def baseStart_1206837 : Nat := 118140960795 + 1206837 * 2 ^ 59
def prefixEnd_1206837 : Nat := 4983230072969 + 3 ^ 40 * 1206837 * 2
def baseEnd_1206837 : Nat := 137708322806711106308303

theorem tailTrace_1206837 : CollatzResearch.WordTrace tailWord_1206837 prefixEnd_1206837 137708322806711106308303 := by
  unfold tailWord_1206837
  simp only [CollatzResearch.WordTrace]
  refine ⟨44016961528843135195346765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29344641019228756796897843 44016961528843135195346765)
  ·
    refine ⟨16506360573316175698255037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44016961528843135195346765 16506360573316175698255037)
    ·
      refine ⟨6189885214993565886845639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16506360573316175698255037 6189885214993565886845639)
      ·
        refine ⟨9284827822490348830268459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6189885214993565886845639 9284827822490348830268459)
        ·
          refine ⟨13927241733735523245402689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9284827822490348830268459 13927241733735523245402689)
          ·
            refine ⟨10445431300301642434052017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13927241733735523245402689 10445431300301642434052017)
            ·
              refine ⟨7834073475226231825539013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10445431300301642434052017 7834073475226231825539013)
              ·
                refine ⟨1468888776604918467288565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7834073475226231825539013 1468888776604918467288565)
                ·
                  refine ⟨137708322806711106308303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1468888776604918467288565 137708322806711106308303)
                  ·
                    rfl

theorem cell22_1206837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 4, 5].length) (baseStart_1206837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1206837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1206837 prefixEnd_1206837 := by exact prefixLift 1206837
  have htrace : WordTrace (prefixWord ++ tailWord_1206837) baseStart_1206837 baseEnd_1206837 := by
    simpa [prefixWord, tailWord_1206837, baseEnd_1206837] using wordTrace_append hprefix tailTrace_1206837
  have hstable : (prefixWord ++ tailWord_1206837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1206837).length < 2 ^ (prefixWord ++ tailWord_1206837).sum := by decide
  have hdescent : baseEnd_1206837 < baseStart_1206837 := by decide
  rcases family_descends (prefixWord ++ tailWord_1206837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1206959 : List Nat := [1, 1, 2, 1, 2, 5, 1, 3, 3, 3]
def baseStart_1206959 : Nat := 118140960795 + 1206959 * 2 ^ 59
def prefixEnd_1206959 : Nat := 4983230072969 + 3 ^ 40 * 1206959 * 2
def baseEnd_1206959 : Nat := 413166731513365667374535

theorem tailTrace_1206959 : CollatzResearch.WordTrace tailWord_1206959 prefixEnd_1206959 413166731513365667374535 := by
  unfold tailWord_1206959
  simp only [CollatzResearch.WordTrace]
  refine ⟨44021411234401150031287931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29347607489600766687525287 44021411234401150031287931)
  ·
    refine ⟨66032116851601725046931897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44021411234401150031287931 66032116851601725046931897)
    ·
      refine ⟨49524087638701293785198923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66032116851601725046931897 49524087638701293785198923)
      ·
        refine ⟨74286131458051940677798385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49524087638701293785198923 74286131458051940677798385)
        ·
          refine ⟨55714598593538955508348789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74286131458051940677798385 55714598593538955508348789)
          ·
            refine ⟨5223243618144277078907699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 55714598593538955508348789 5223243618144277078907699)
            ·
              refine ⟨7834865427216415618361549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5223243618144277078907699 7834865427216415618361549)
              ·
                refine ⟨2938074535206155856885581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7834865427216415618361549 2938074535206155856885581)
                ·
                  refine ⟨1101777950702308446332093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2938074535206155856885581 1101777950702308446332093)
                  ·
                    refine ⟨413166731513365667374535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1101777950702308446332093 413166731513365667374535)
                    ·
                      rfl

theorem cell22_1206959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 3, 3, 3].length) (baseStart_1206959 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1206959 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1206959 prefixEnd_1206959 := by exact prefixLift 1206959
  have htrace : WordTrace (prefixWord ++ tailWord_1206959) baseStart_1206959 baseEnd_1206959 := by
    simpa [prefixWord, tailWord_1206959, baseEnd_1206959] using wordTrace_append hprefix tailTrace_1206959
  have hstable : (prefixWord ++ tailWord_1206959).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1206959).length < 2 ^ (prefixWord ++ tailWord_1206959).sum := by decide
  have hdescent : baseEnd_1206959 < baseStart_1206959 := by decide
  rcases family_descends (prefixWord ++ tailWord_1206959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1207036 : List Nat := [2, 2, 2, 1, 3, 2, 3, 2, 1, 4]
def baseStart_1207036 : Nat := 118140960795 + 1207036 * 2 ^ 59
def prefixEnd_1207036 : Nat := 4983230072969 + 3 ^ 40 * 1207036 * 2
def baseEnd_1207036 : Nat := 413193090186963133199299

theorem tailTrace_1207036 : CollatzResearch.WordTrace tailWord_1207036 prefixEnd_1207036 413193090186963133199299 := by
  unfold tailWord_1207036
  simp only [CollatzResearch.WordTrace]
  refine ⟨22012109827561096090920481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29349479770081461454560641 22012109827561096090920481)
  ·
    refine ⟨16509082370670822068190361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22012109827561096090920481 16509082370670822068190361)
    ·
      refine ⟨12381811778003116551142771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16509082370670822068190361 12381811778003116551142771)
      ·
        refine ⟨18572717667004674826714157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12381811778003116551142771 18572717667004674826714157)
        ·
          refine ⟨6964769125126753060017809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18572717667004674826714157 6964769125126753060017809)
          ·
            refine ⟨5223576843845064795013357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6964769125126753060017809 5223576843845064795013357)
            ·
              refine ⟨1958841316441899298130009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5223576843845064795013357 1958841316441899298130009)
              ·
                refine ⟨1469130987331424473597507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1958841316441899298130009 1469130987331424473597507)
                ·
                  refine ⟨2203696480997136710396261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1469130987331424473597507 2203696480997136710396261)
                  ·
                    refine ⟨413193090186963133199299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2203696480997136710396261 413193090186963133199299)
                    ·
                      rfl

theorem cell22_1207036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 3, 2, 1, 4].length) (baseStart_1207036 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1207036 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1207036 prefixEnd_1207036 := by exact prefixLift 1207036
  have htrace : WordTrace (prefixWord ++ tailWord_1207036) baseStart_1207036 baseEnd_1207036 := by
    simpa [prefixWord, tailWord_1207036, baseEnd_1207036] using wordTrace_append hprefix tailTrace_1207036
  have hstable : (prefixWord ++ tailWord_1207036).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1207036).length < 2 ^ (prefixWord ++ tailWord_1207036).sum := by decide
  have hdescent : baseEnd_1207036 < baseStart_1207036 := by decide
  rcases family_descends (prefixWord ++ tailWord_1207036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1207049 : List Nat := [1, 2, 1, 1, 3, 2, 2, 1, 6, 3]
def baseStart_1207049 : Nat := 118140960795 + 1207049 * 2 ^ 59
def prefixEnd_1207049 : Nat := 4983230072969 + 3 ^ 40 * 1207049 * 2
def baseEnd_1207049 : Nat := 413197540352635432624259

theorem tailTrace_1207049 : CollatzResearch.WordTrace tailWord_1207049 prefixEnd_1207049 413197540352635432624259 := by
  unfold tailWord_1207049
  simp only [CollatzResearch.WordTrace]
  refine ⟨44024693804075095402064201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29349795869383396934709467 44024693804075095402064201)
  ·
    refine ⟨33018520353056321551548151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44024693804075095402064201 33018520353056321551548151)
    ·
      refine ⟨49527780529584482327322227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33018520353056321551548151 49527780529584482327322227)
      ·
        refine ⟨74291670794376723490983341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49527780529584482327322227 74291670794376723490983341)
        ·
          refine ⟨27859376547891271309118753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74291670794376723490983341 27859376547891271309118753)
          ·
            refine ⟨20894532410918453481839065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27859376547891271309118753 20894532410918453481839065)
            ·
              refine ⟨15670899308188840111379299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20894532410918453481839065 15670899308188840111379299)
              ·
                refine ⟨23506348962283260167068949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15670899308188840111379299 23506348962283260167068949)
                ·
                  refine ⟨1101860107607027820331357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 23506348962283260167068949 1101860107607027820331357)
                  ·
                    refine ⟨413197540352635432624259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1101860107607027820331357 413197540352635432624259)
                    ·
                      rfl

theorem cell22_1207049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 1, 6, 3].length) (baseStart_1207049 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1207049 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1207049 prefixEnd_1207049 := by exact prefixLift 1207049
  have htrace : WordTrace (prefixWord ++ tailWord_1207049) baseStart_1207049 baseEnd_1207049 := by
    simpa [prefixWord, tailWord_1207049, baseEnd_1207049] using wordTrace_append hprefix tailTrace_1207049
  have hstable : (prefixWord ++ tailWord_1207049).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1207049).length < 2 ^ (prefixWord ++ tailWord_1207049).sum := by decide
  have hdescent : baseEnd_1207049 < baseStart_1207049 := by decide
  rcases family_descends (prefixWord ++ tailWord_1207049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1207068 : List Nat := [2, 2, 3, 1, 1, 3, 4, 2, 4]
def baseStart_1207068 : Nat := 118140960795 + 1207068 * 2 ^ 59
def prefixEnd_1207068 : Nat := 4983230072969 + 3 ^ 40 * 1207068 * 2
def baseEnd_1207068 : Nat := 137734681480308572133067

theorem tailTrace_1207068 : CollatzResearch.WordTrace tailWord_1207068 prefixEnd_1207068 137734681480308572133067 := by
  unfold tailWord_1207068
  simp only [CollatzResearch.WordTrace]
  refine ⟨22012693395503130823502929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29350257860670841098003905 22012693395503130823502929)
  ·
    refine ⟨16509520046627348117627197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22012693395503130823502929 16509520046627348117627197)
    ·
      refine ⟨6191070017485255544110199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16509520046627348117627197 6191070017485255544110199)
      ·
        refine ⟨9286605026227883316165299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6191070017485255544110199 9286605026227883316165299)
        ·
          refine ⟨13929907539341824974247949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9286605026227883316165299 13929907539341824974247949)
          ·
            refine ⟨5223715327253184365342981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13929907539341824974247949 5223715327253184365342981)
            ·
              refine ⟨979446623859972068501809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5223715327253184365342981 979446623859972068501809)
              ·
                refine ⟨734584967894979051376357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 979446623859972068501809 734584967894979051376357)
                ·
                  refine ⟨137734681480308572133067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 734584967894979051376357 137734681480308572133067)
                  ·
                    rfl

theorem cell22_1207068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 4, 2, 4].length) (baseStart_1207068 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1207068 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1207068 prefixEnd_1207068 := by exact prefixLift 1207068
  have htrace : WordTrace (prefixWord ++ tailWord_1207068) baseStart_1207068 baseEnd_1207068 := by
    simpa [prefixWord, tailWord_1207068, baseEnd_1207068] using wordTrace_append hprefix tailTrace_1207068
  have hstable : (prefixWord ++ tailWord_1207068).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1207068).length < 2 ^ (prefixWord ++ tailWord_1207068).sum := by decide
  have hdescent : baseEnd_1207068 < baseStart_1207068 := by decide
  rcases family_descends (prefixWord ++ tailWord_1207068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1207098 : List Nat := [3, 1, 1, 1, 6, 2, 1, 1, 2, 4]
def baseStart_1207098 : Nat := 118140960795 + 1207098 * 2 ^ 59
def prefixEnd_1207098 : Nat := 4983230072969 + 3 ^ 40 * 1207098 * 2
def baseEnd_1207098 : Nat := 413214314054015638149109

theorem tailTrace_1207098 : CollatzResearch.WordTrace tailWord_1207098 prefixEnd_1207098 413214314054015638149109 := by
  unfold tailWord_1207098
  simp only [CollatzResearch.WordTrace]
  refine ⟨11006620245224394192649487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29350987320598384513731965 11006620245224394192649487)
  ·
    refine ⟨16509930367836591288974231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11006620245224394192649487 16509930367836591288974231)
    ·
      refine ⟨24764895551754886933461347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16509930367836591288974231 24764895551754886933461347)
      ·
        refine ⟨37147343327632330400192021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24764895551754886933461347 37147343327632330400192021)
        ·
          refine ⟨1741281718482765487509001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 37147343327632330400192021 1741281718482765487509001)
          ·
            refine ⟨1305961288862074115631751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1741281718482765487509001 1305961288862074115631751)
            ·
              refine ⟨1958941933293111173447627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1305961288862074115631751 1958941933293111173447627)
              ·
                refine ⟨2938412899939666760171441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1958941933293111173447627 2938412899939666760171441)
                ·
                  refine ⟨2203809674954750070128581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2938412899939666760171441 2203809674954750070128581)
                  ·
                    refine ⟨413214314054015638149109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2203809674954750070128581 413214314054015638149109)
                    ·
                      rfl

theorem cell22_1207098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 1, 1, 2, 4].length) (baseStart_1207098 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1207098 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1207098 prefixEnd_1207098 := by exact prefixLift 1207098
  have htrace : WordTrace (prefixWord ++ tailWord_1207098) baseStart_1207098 baseEnd_1207098 := by
    simpa [prefixWord, tailWord_1207098, baseEnd_1207098] using wordTrace_append hprefix tailTrace_1207098
  have hstable : (prefixWord ++ tailWord_1207098).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1207098).length < 2 ^ (prefixWord ++ tailWord_1207098).sum := by decide
  have hdescent : baseEnd_1207098 < baseStart_1207098 := by decide
  rcases family_descends (prefixWord ++ tailWord_1207098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1207117 : List Nat := [1, 6, 1, 2, 2, 2, 1, 2, 2, 3]
def baseStart_1207117 : Nat := 118140960795 + 1207117 * 2 ^ 59
def prefixEnd_1207117 : Nat := 4983230072969 + 3 ^ 40 * 1207117 * 2
def baseEnd_1207117 : Nat := 413220818142305921924051

theorem tailTrace_1207117 : CollatzResearch.WordTrace tailWord_1207117 prefixEnd_1207117 413220818142305921924051 := by
  unfold tailWord_1207117
  simp only [CollatzResearch.WordTrace]
  refine ⟨44027173967828743015539605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29351449311885828677026403 44027173967828743015539605)
  ·
    refine ⟨2063773779741972328853419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 44027173967828743015539605 2063773779741972328853419)
    ·
      refine ⟨3095660669612958493280129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2063773779741972328853419 3095660669612958493280129)
      ·
        refine ⟨2321745502209718869960097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3095660669612958493280129 2321745502209718869960097)
        ·
          refine ⟨1741309126657289152470073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2321745502209718869960097 1741309126657289152470073)
          ·
            refine ⟨1305981844992966864352555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1741309126657289152470073 1305981844992966864352555)
            ·
              refine ⟨1958972767489450296528833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1305981844992966864352555 1958972767489450296528833)
              ·
                refine ⟨1469229575617087722396625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1958972767489450296528833 1469229575617087722396625)
                ·
                  refine ⟨1101922181712815791797469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1469229575617087722396625 1101922181712815791797469)
                  ·
                    refine ⟨413220818142305921924051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1101922181712815791797469 413220818142305921924051)
                    ·
                      rfl

theorem cell22_1207117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 1, 2, 2, 3].length) (baseStart_1207117 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1207117 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1207117 prefixEnd_1207117 := by exact prefixLift 1207117
  have htrace : WordTrace (prefixWord ++ tailWord_1207117) baseStart_1207117 baseEnd_1207117 := by
    simpa [prefixWord, tailWord_1207117, baseEnd_1207117] using wordTrace_append hprefix tailTrace_1207117
  have hstable : (prefixWord ++ tailWord_1207117).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1207117).length < 2 ^ (prefixWord ++ tailWord_1207117).sum := by decide
  have hdescent : baseEnd_1207117 < baseStart_1207117 := by decide
  rcases family_descends (prefixWord ++ tailWord_1207117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1207171 : List Nat := [1, 1, 1, 3, 4, 1, 1, 5, 1, 4]
def baseStart_1207171 : Nat := 118140960795 + 1207171 * 2 ^ 59
def prefixEnd_1207171 : Nat := 4983230072969 + 3 ^ 40 * 1207171 * 2
def baseEnd_1207171 : Nat := 413239303445867781073885

theorem tailTrace_1207171 : CollatzResearch.WordTrace tailWord_1207171 prefixEnd_1207171 413239303445867781073885 := by
  unfold tailWord_1207171
  simp only [CollatzResearch.WordTrace]
  refine ⟨44029143509633110238005367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29352762339755406825336911 44029143509633110238005367)
  ·
    refine ⟨66043715264449665357008051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44029143509633110238005367 66043715264449665357008051)
    ·
      refine ⟨99065572896674498035512077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66043715264449665357008051 99065572896674498035512077)
      ·
        refine ⟨37149589836252936763317029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 99065572896674498035512077 37149589836252936763317029)
        ·
          refine ⟨6965548094297425643121943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37149589836252936763317029 6965548094297425643121943)
          ·
            refine ⟨10448322141446138464682915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6965548094297425643121943 10448322141446138464682915)
            ·
              refine ⟨15672483212169207697024373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10448322141446138464682915 15672483212169207697024373)
              ·
                refine ⟨1469295301140863221596035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15672483212169207697024373 1469295301140863221596035)
                ·
                  refine ⟨2203942951711294832394053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1469295301140863221596035 2203942951711294832394053)
                  ·
                    refine ⟨413239303445867781073885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2203942951711294832394053 413239303445867781073885)
                    ·
                      rfl

theorem cell22_1207171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 5, 1, 4].length) (baseStart_1207171 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1207171 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1207171 prefixEnd_1207171 := by exact prefixLift 1207171
  have htrace : WordTrace (prefixWord ++ tailWord_1207171) baseStart_1207171 baseEnd_1207171 := by
    simpa [prefixWord, tailWord_1207171, baseEnd_1207171] using wordTrace_append hprefix tailTrace_1207171
  have hstable : (prefixWord ++ tailWord_1207171).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1207171).length < 2 ^ (prefixWord ++ tailWord_1207171).sum := by decide
  have hdescent : baseEnd_1207171 < baseStart_1207171 := by decide
  rcases family_descends (prefixWord ++ tailWord_1207171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1207310 : List Nat := [4, 1, 1, 2, 2, 3, 3, 1, 5]
def baseStart_1207310 : Nat := 118140960795 + 1207310 * 2 ^ 59
def prefixEnd_1207310 : Nat := 4983230072969 + 3 ^ 40 * 1207310 * 2
def baseEnd_1207310 : Nat := 137762295328839250616153

theorem tailTrace_1207310 : CollatzResearch.WordTrace tailWord_1207310 prefixEnd_1207310 137762295328839250616153 := by
  unfold tailWord_1207310
  simp only [CollatzResearch.WordTrace]
  refine ⟨5504276657016192122164423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29356142170753024651543589 5504276657016192122164423)
  ·
    refine ⟨8256414985524288183246635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5504276657016192122164423 8256414985524288183246635)
    ·
      refine ⟨12384622478286432274869953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8256414985524288183246635 12384622478286432274869953)
      ·
        refine ⟨9288466858714824206152465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12384622478286432274869953 9288466858714824206152465)
        ·
          refine ⟨6966350144036118154614349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9288466858714824206152465 6966350144036118154614349)
          ·
            refine ⟨2612381304013544307980381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6966350144036118154614349 2612381304013544307980381)
            ·
              refine ⟨979642989005079115492643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2612381304013544307980381 979642989005079115492643)
              ·
                refine ⟨1469464483507618673238965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 979642989005079115492643 1469464483507618673238965)
                ·
                  refine ⟨137762295328839250616153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1469464483507618673238965 137762295328839250616153)
                  ·
                    rfl

theorem cell22_1207310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 3, 1, 5].length) (baseStart_1207310 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1207310 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1207310 prefixEnd_1207310 := by exact prefixLift 1207310
  have htrace : WordTrace (prefixWord ++ tailWord_1207310) baseStart_1207310 baseEnd_1207310 := by
    simpa [prefixWord, tailWord_1207310, baseEnd_1207310] using wordTrace_append hprefix tailTrace_1207310
  have hstable : (prefixWord ++ tailWord_1207310).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1207310).length < 2 ^ (prefixWord ++ tailWord_1207310).sum := by decide
  have hdescent : baseEnd_1207310 < baseStart_1207310 := by decide
  rcases family_descends (prefixWord ++ tailWord_1207310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1207321 : List Nat := [1, 2, 1, 2, 1, 1, 6, 2, 6]
def baseStart_1207321 : Nat := 118140960795 + 1207321 * 2 ^ 59
def prefixEnd_1207321 : Nat := 4983230072969 + 3 ^ 40 * 1207321 * 2
def baseEnd_1207321 : Nat := 137763550503772463274475

theorem tailTrace_1207321 : CollatzResearch.WordTrace tailWord_1207321 prefixEnd_1207321 137763550503772463274475 := by
  unfold tailWord_1207321
  simp only [CollatzResearch.WordTrace]
  refine ⟨44034614459089685855965817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29356409639393123903977211 44034614459089685855965817)
  ·
    refine ⟨33025960844317264391974363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44034614459089685855965817 33025960844317264391974363)
    ·
      refine ⟨49538941266475896587961545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33025960844317264391974363 49538941266475896587961545)
      ·
        refine ⟨37154205949856922440971159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49538941266475896587961545 37154205949856922440971159)
        ·
          refine ⟨55731308924785383661456739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37154205949856922440971159 55731308924785383661456739)
          ·
            refine ⟨83596963387178075492185109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55731308924785383661456739 83596963387178075492185109)
            ·
              refine ⟨3918607658773972288696177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 83596963387178075492185109 3918607658773972288696177)
              ·
                refine ⟨2938955744080479216522133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3918607658773972288696177 2938955744080479216522133)
                ·
                  refine ⟨137763550503772463274475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2938955744080479216522133 137763550503772463274475)
                  ·
                    rfl

theorem cell22_1207321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6, 2, 6].length) (baseStart_1207321 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1207321 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1207321 prefixEnd_1207321 := by exact prefixLift 1207321
  have htrace : WordTrace (prefixWord ++ tailWord_1207321) baseStart_1207321 baseEnd_1207321 := by
    simpa [prefixWord, tailWord_1207321, baseEnd_1207321] using wordTrace_append hprefix tailTrace_1207321
  have hstable : (prefixWord ++ tailWord_1207321).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1207321).length < 2 ^ (prefixWord ++ tailWord_1207321).sum := by decide
  have hdescent : baseEnd_1207321 < baseStart_1207321 := by decide
  rcases family_descends (prefixWord ++ tailWord_1207321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1207400 : List Nat := [2, 1, 4, 4, 2, 9]
def baseStart_1207400 : Nat := 118140960795 + 1207400 * 2 ^ 59
def prefixEnd_1207400 : Nat := 4983230072969 + 3 ^ 40 * 1207400 * 2
def baseEnd_1207400 : Nat := 5102687590441821198743

theorem tailTrace_1207400 : CollatzResearch.WordTrace tailWord_1207400 prefixEnd_1207400 5102687590441821198743 := by
  unfold tailWord_1207400
  simp only [CollatzResearch.WordTrace]
  refine ⟨22018747912901741174045827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29358330550535654898727769 22018747912901741174045827)
  ·
    refine ⟨33028121869352611761068741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22018747912901741174045827 33028121869352611761068741)
    ·
      refine ⟨6192772850503614705200389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33028121869352611761068741 6192772850503614705200389)
      ·
        refine ⟨1161144909469427757225073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6192772850503614705200389 1161144909469427757225073)
        ·
          refine ⟨870858682102070817918805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1161144909469427757225073 870858682102070817918805)
          ·
            refine ⟨5102687590441821198743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 870858682102070817918805 5102687590441821198743)
            ·
              rfl

theorem cell22_1207400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 9].length) (baseStart_1207400 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1207400 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1207400 prefixEnd_1207400 := by exact prefixLift 1207400
  have htrace : WordTrace (prefixWord ++ tailWord_1207400) baseStart_1207400 baseEnd_1207400 := by
    simpa [prefixWord, tailWord_1207400, baseEnd_1207400] using wordTrace_append hprefix tailTrace_1207400
  have hstable : (prefixWord ++ tailWord_1207400).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1207400).length < 2 ^ (prefixWord ++ tailWord_1207400).sum := by decide
  have hdescent : baseEnd_1207400 < baseStart_1207400 := by decide
  rcases family_descends (prefixWord ++ tailWord_1207400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1207432 : List Nat := [2, 1, 3, 4, 2, 1, 1, 2, 3, 3]
def baseStart_1207432 : Nat := 118140960795 + 1207432 * 2 ^ 59
def prefixEnd_1207432 : Nat := 4983230072969 + 3 ^ 40 * 1207432 * 2
def baseEnd_1207432 : Nat := 413328649079750100298085

theorem tailTrace_1207432 : CollatzResearch.WordTrace tailWord_1207432 prefixEnd_1207432 413328649079750100298085 := by
  unfold tailWord_1207432
  simp only [CollatzResearch.WordTrace]
  refine ⟨22019331480843775906628275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29359108641125034542171033 22019331480843775906628275)
  ·
    refine ⟨33028997221265663859942413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22019331480843775906628275 33028997221265663859942413)
    ·
      refine ⟨12385873957974623947478405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33028997221265663859942413 12385873957974623947478405)
      ·
        refine ⟨2322351367120241990152201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12385873957974623947478405 2322351367120241990152201)
        ·
          refine ⟨1741763525340181492614151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2322351367120241990152201 1741763525340181492614151)
          ·
            refine ⟨2612645288010272238921227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1741763525340181492614151 2612645288010272238921227)
            ·
              refine ⟨3918967932015408358381841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2612645288010272238921227 3918967932015408358381841)
              ·
                refine ⟨2939225949011556268786381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3918967932015408358381841 2939225949011556268786381)
                ·
                  refine ⟨1102209730879333600794893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2939225949011556268786381 1102209730879333600794893)
                  ·
                    refine ⟨413328649079750100298085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1102209730879333600794893 413328649079750100298085)
                    ·
                      rfl

theorem cell22_1207432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 1, 2, 3, 3].length) (baseStart_1207432 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1207432 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1207432 prefixEnd_1207432 := by exact prefixLift 1207432
  have htrace : WordTrace (prefixWord ++ tailWord_1207432) baseStart_1207432 baseEnd_1207432 := by
    simpa [prefixWord, tailWord_1207432, baseEnd_1207432] using wordTrace_append hprefix tailTrace_1207432
  have hstable : (prefixWord ++ tailWord_1207432).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1207432).length < 2 ^ (prefixWord ++ tailWord_1207432).sum := by decide
  have hdescent : baseEnd_1207432 < baseStart_1207432 := by decide
  rcases family_descends (prefixWord ++ tailWord_1207432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1207520 : List Nat := [2, 1, 1, 3, 1, 5, 1, 2, 2, 4]
def baseStart_1207520 : Nat := 118140960795 + 1207520 * 2 ^ 59
def prefixEnd_1207520 : Nat := 4983230072969 + 3 ^ 40 * 1207520 * 2
def baseEnd_1207520 : Nat := 413358773278147204097815

theorem tailTrace_1207520 : CollatzResearch.WordTrace tailWord_1207520 prefixEnd_1207520 413358773278147204097815 := by
  unfold tailWord_1207520
  simp only [CollatzResearch.WordTrace]
  refine ⟨22020936292684371421230007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29361248390245828561640009 22020936292684371421230007)
  ·
    refine ⟨33031404439026557131845011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22020936292684371421230007 33031404439026557131845011)
    ·
      refine ⟨49547106658539835697767517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33031404439026557131845011 49547106658539835697767517)
      ·
        refine ⟨18580164996952438386662819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49547106658539835697767517 18580164996952438386662819)
        ·
          refine ⟨27870247495428657579994229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18580164996952438386662819 27870247495428657579994229)
          ·
            refine ⟨2612835702696436648124459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 27870247495428657579994229 2612835702696436648124459)
            ·
              refine ⟨3919253554044654972186689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2612835702696436648124459 3919253554044654972186689)
              ·
                refine ⟨2939440165533491229140017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3919253554044654972186689 2939440165533491229140017)
                ·
                  refine ⟨2204580124150118421855013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2939440165533491229140017 2204580124150118421855013)
                  ·
                    refine ⟨413358773278147204097815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2204580124150118421855013 413358773278147204097815)
                    ·
                      rfl

theorem cell22_1207520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 1, 2, 2, 4].length) (baseStart_1207520 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1207520 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1207520 prefixEnd_1207520 := by exact prefixLift 1207520
  have htrace : WordTrace (prefixWord ++ tailWord_1207520) baseStart_1207520 baseEnd_1207520 := by
    simpa [prefixWord, tailWord_1207520, baseEnd_1207520] using wordTrace_append hprefix tailTrace_1207520
  have hstable : (prefixWord ++ tailWord_1207520).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1207520).length < 2 ^ (prefixWord ++ tailWord_1207520).sum := by decide
  have hdescent : baseEnd_1207520 < baseStart_1207520 := by decide
  rcases family_descends (prefixWord ++ tailWord_1207520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1207535 : List Nat := [1, 1, 2, 1, 7, 1, 2, 7]
def baseStart_1207535 : Nat := 118140960795 + 1207535 * 2 ^ 59
def prefixEnd_1207535 : Nat := 4983230072969 + 3 ^ 40 * 1207535 * 2
def baseEnd_1207535 : Nat := 45929323120521351663641

theorem tailTrace_1207535 : CollatzResearch.WordTrace tailWord_1207535 prefixEnd_1207535 45929323120521351663641 := by
  unfold tailWord_1207535
  simp only [CollatzResearch.WordTrace]
  refine ⟨44042419680314400404256059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29361613120209600269504039 44042419680314400404256059)
  ·
    refine ⟨66063629520471600606384089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44042419680314400404256059 66063629520471600606384089)
    ·
      refine ⟨49547722140353700454788067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66063629520471600606384089 49547722140353700454788067)
      ·
        refine ⟨74321583210530550682182101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49547722140353700454788067 74321583210530550682182101)
        ·
          refine ⟨1741912106496809781613643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 74321583210530550682182101 1741912106496809781613643)
          ·
            refine ⟨2612868159745214672420465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1741912106496809781613643 2612868159745214672420465)
            ·
              refine ⟨1959651119808911004315349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2612868159745214672420465 1959651119808911004315349)
              ·
                refine ⟨45929323120521351663641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1959651119808911004315349 45929323120521351663641)
                ·
                  rfl

theorem cell22_1207535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 2, 7].length) (baseStart_1207535 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1207535 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1207535 prefixEnd_1207535 := by exact prefixLift 1207535
  have htrace : WordTrace (prefixWord ++ tailWord_1207535) baseStart_1207535 baseEnd_1207535 := by
    simpa [prefixWord, tailWord_1207535, baseEnd_1207535] using wordTrace_append hprefix tailTrace_1207535
  have hstable : (prefixWord ++ tailWord_1207535).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1207535).length < 2 ^ (prefixWord ++ tailWord_1207535).sum := by decide
  have hdescent : baseEnd_1207535 < baseStart_1207535 := by decide
  rcases family_descends (prefixWord ++ tailWord_1207535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1207539 : List Nat := [1, 1, 1, 2, 2, 7, 2, 1, 2, 3]
def baseStart_1207539 : Nat := 118140960795 + 1207539 * 2 ^ 59
def prefixEnd_1207539 : Nat := 4983230072969 + 3 ^ 40 * 1207539 * 2
def baseEnd_1207539 : Nat := 413365277366437487872757

theorem tailTrace_1207539 : CollatzResearch.WordTrace tailWord_1207539 prefixEnd_1207539 413365277366437487872757 := by
  unfold tailWord_1207539
  simp only [CollatzResearch.WordTrace]
  refine ⟨44042565572299909087401671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29361710381533272724934447 44042565572299909087401671)
  ·
    refine ⟨66063848358449863631102507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44042565572299909087401671 66063848358449863631102507)
    ·
      refine ⟨99095772537674795446653761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66063848358449863631102507 99095772537674795446653761)
      ·
        refine ⟨74321829403256096584990321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99095772537674795446653761 74321829403256096584990321)
        ·
          refine ⟨55741372052442072438742741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74321829403256096584990321 55741372052442072438742741)
          ·
            refine ⟨1306438407479111072783033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 55741372052442072438742741 1306438407479111072783033)
            ·
              refine ⟨979828805609333304587275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1306438407479111072783033 979828805609333304587275)
              ·
                refine ⟨1469743208413999956880913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 979828805609333304587275 1469743208413999956880913)
                ·
                  refine ⟨1102307406310499967660685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1469743208413999956880913 1102307406310499967660685)
                  ·
                    refine ⟨413365277366437487872757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1102307406310499967660685 413365277366437487872757)
                    ·
                      rfl

theorem cell22_1207539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 2, 1, 2, 3].length) (baseStart_1207539 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1207539 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1207539 prefixEnd_1207539 := by exact prefixLift 1207539
  have htrace : WordTrace (prefixWord ++ tailWord_1207539) baseStart_1207539 baseEnd_1207539 := by
    simpa [prefixWord, tailWord_1207539, baseEnd_1207539] using wordTrace_append hprefix tailTrace_1207539
  have hstable : (prefixWord ++ tailWord_1207539).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1207539).length < 2 ^ (prefixWord ++ tailWord_1207539).sum := by decide
  have hdescent : baseEnd_1207539 < baseStart_1207539 := by decide
  rcases family_descends (prefixWord ++ tailWord_1207539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1207554 : List Nat := [3, 4, 1, 1, 3, 1, 2, 1, 2, 4]
def baseStart_1207554 : Nat := 118140960795 + 1207554 * 2 ^ 59
def prefixEnd_1207554 : Nat := 4983230072969 + 3 ^ 40 * 1207554 * 2
def baseEnd_1207554 : Nat := 413370412172982448747711

theorem tailTrace_1207554 : CollatzResearch.WordTrace tailWord_1207554 prefixEnd_1207554 413370412172982448747711 := by
  unfold tailWord_1207554
  simp only [CollatzResearch.WordTrace]
  refine ⟨11010778166811391662299429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29362075111497044432798477 11010778166811391662299429)
  ·
    refine ⟨2064520906277135936681143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11010778166811391662299429 2064520906277135936681143)
    ·
      refine ⟨3096781359415703905021715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2064520906277135936681143 3096781359415703905021715)
      ·
        refine ⟨4645172039123555857532573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3096781359415703905021715 4645172039123555857532573)
        ·
          refine ⟨1741939514671333446574715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4645172039123555857532573 1741939514671333446574715)
          ·
            refine ⟨2612909272007000169862073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1741939514671333446574715 2612909272007000169862073)
            ·
              refine ⟨1959681954005250127396555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2612909272007000169862073 1959681954005250127396555)
              ·
                refine ⟨2939522931007875191094833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1959681954005250127396555 2939522931007875191094833)
                ·
                  refine ⟨2204642198255906393321125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2939522931007875191094833 2204642198255906393321125)
                  ·
                    refine ⟨413370412172982448747711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2204642198255906393321125 413370412172982448747711)
                    ·
                      rfl

theorem cell22_1207554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 2, 1, 2, 4].length) (baseStart_1207554 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1207554 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1207554 prefixEnd_1207554 := by exact prefixLift 1207554
  have htrace : WordTrace (prefixWord ++ tailWord_1207554) baseStart_1207554 baseEnd_1207554 := by
    simpa [prefixWord, tailWord_1207554, baseEnd_1207554] using wordTrace_append hprefix tailTrace_1207554
  have hstable : (prefixWord ++ tailWord_1207554).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1207554).length < 2 ^ (prefixWord ++ tailWord_1207554).sum := by decide
  have hdescent : baseEnd_1207554 < baseStart_1207554 := by decide
  rcases family_descends (prefixWord ++ tailWord_1207554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1207580 : List Nat := [2, 2, 3, 1, 1, 1, 3, 4, 5]
def baseStart_1207580 : Nat := 118140960795 + 1207580 * 2 ^ 59
def prefixEnd_1207580 : Nat := 4983230072969 + 3 ^ 40 * 1207580 * 2
def baseEnd_1207580 : Nat := 137793104168109015865877

theorem tailTrace_1207580 : CollatzResearch.WordTrace tailWord_1207580 prefixEnd_1207580 137793104168109015865877 := by
  unfold tailWord_1207580
  simp only [CollatzResearch.WordTrace]
  refine ⟨22022030482575686544822097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29362707310100915393096129 22022030482575686544822097)
  ·
    refine ⟨16516522861931764908616573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22022030482575686544822097 16516522861931764908616573)
    ·
      refine ⟨6193696073224411840731215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16516522861931764908616573 6193696073224411840731215)
      ·
        refine ⟨9290544109836617761096823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6193696073224411840731215 9290544109836617761096823)
        ·
          refine ⟨13935816164754926641645235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9290544109836617761096823 13935816164754926641645235)
          ·
            refine ⟨20903724247132389962467853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13935816164754926641645235 20903724247132389962467853)
            ·
              refine ⟨7838896592674646235925445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20903724247132389962467853 7838896592674646235925445)
              ·
                refine ⟨1469793111126496169236021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7838896592674646235925445 1469793111126496169236021)
                ·
                  refine ⟨137793104168109015865877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1469793111126496169236021 137793104168109015865877)
                  ·
                    rfl

theorem cell22_1207580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 4, 5].length) (baseStart_1207580 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1207580 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1207580 prefixEnd_1207580 := by exact prefixLift 1207580
  have htrace : WordTrace (prefixWord ++ tailWord_1207580) baseStart_1207580 baseEnd_1207580 := by
    simpa [prefixWord, tailWord_1207580, baseEnd_1207580] using wordTrace_append hprefix tailTrace_1207580
  have hstable : (prefixWord ++ tailWord_1207580).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1207580).length < 2 ^ (prefixWord ++ tailWord_1207580).sum := by decide
  have hdescent : baseEnd_1207580 < baseStart_1207580 := by decide
  rcases family_descends (prefixWord ++ tailWord_1207580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1207610 : List Nat := [3, 1, 1, 1, 4, 1, 1, 3, 3, 4]
def baseStart_1207610 : Nat := 118140960795 + 1207610 * 2 ^ 59
def prefixEnd_1207610 : Nat := 4983230072969 + 3 ^ 40 * 1207610 * 2
def baseEnd_1207610 : Nat := 413389582117416969347539

theorem tailTrace_1207610 : CollatzResearch.WordTrace tailWord_1207610 prefixEnd_1207610 413389582117416969347539 := by
  unfold tailWord_1207610
  simp only [CollatzResearch.WordTrace]
  refine ⟨11011288788760672053309071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29363436770028458808824189 11011288788760672053309071)
  ·
    refine ⟨16516933183141008079963607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11011288788760672053309071 16516933183141008079963607)
    ·
      refine ⟨24775399774711512119945411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16516933183141008079963607 24775399774711512119945411)
      ·
        refine ⟨37163099662067268179918117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24775399774711512119945411 37163099662067268179918117)
        ·
          refine ⟨6968081186637612783734647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37163099662067268179918117 6968081186637612783734647)
          ·
            refine ⟨10452121779956419175601971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6968081186637612783734647 10452121779956419175601971)
            ·
              refine ⟨15678182669934628763402957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10452121779956419175601971 15678182669934628763402957)
              ·
                refine ⟨5879318501225485786276109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15678182669934628763402957 5879318501225485786276109)
                ·
                  refine ⟨2204744437959557169853541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5879318501225485786276109 2204744437959557169853541)
                  ·
                    refine ⟨413389582117416969347539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2204744437959557169853541 413389582117416969347539)
                    ·
                      rfl

theorem cell22_1207610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 3, 3, 4].length) (baseStart_1207610 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1207610 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1207610 prefixEnd_1207610 := by exact prefixLift 1207610
  have htrace : WordTrace (prefixWord ++ tailWord_1207610) baseStart_1207610 baseEnd_1207610 := by
    simpa [prefixWord, tailWord_1207610, baseEnd_1207610] using wordTrace_append hprefix tailTrace_1207610
  have hstable : (prefixWord ++ tailWord_1207610).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1207610).length < 2 ^ (prefixWord ++ tailWord_1207610).sum := by decide
  have hdescent : baseEnd_1207610 < baseStart_1207610 := by decide
  rcases family_descends (prefixWord ++ tailWord_1207610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1207642 : List Nat := [3, 1, 1, 2, 1, 2, 4, 4, 4]
def baseStart_1207642 : Nat := 118140960795 + 1207642 * 2 ^ 59
def prefixEnd_1207642 : Nat := 4983230072969 + 3 ^ 40 * 1207642 * 2
def baseEnd_1207642 : Nat := 137800178790459850849147

theorem tailTrace_1207642 : CollatzResearch.WordTrace tailWord_1207642 prefixEnd_1207642 137800178790459850849147 := by
  unfold tailWord_1207642
  simp only [CollatzResearch.WordTrace]
  refine ⟨11011580572731689419600295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29364214860617838452267453 11011580572731689419600295)
  ·
    refine ⟨16517370859097534129400443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11011580572731689419600295 16517370859097534129400443)
    ·
      refine ⟨24776056288646301194100665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16517370859097534129400443 24776056288646301194100665)
      ·
        refine ⟨18582042216484725895575499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24776056288646301194100665 18582042216484725895575499)
        ·
          refine ⟨27873063324727088843363249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18582042216484725895575499 27873063324727088843363249)
          ·
            refine ⟨20904797493545316632522437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27873063324727088843363249 20904797493545316632522437)
            ·
              refine ⟨3919649530039746868597957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20904797493545316632522437 3919649530039746868597957)
              ·
                refine ⟨734934286882452537862117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3919649530039746868597957 734934286882452537862117)
                ·
                  refine ⟨137800178790459850849147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 734934286882452537862117 137800178790459850849147)
                  ·
                    rfl

theorem cell22_1207642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4, 4, 4].length) (baseStart_1207642 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1207642 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1207642 prefixEnd_1207642 := by exact prefixLift 1207642
  have htrace : WordTrace (prefixWord ++ tailWord_1207642) baseStart_1207642 baseEnd_1207642 := by
    simpa [prefixWord, tailWord_1207642, baseEnd_1207642] using wordTrace_append hprefix tailTrace_1207642
  have hstable : (prefixWord ++ tailWord_1207642).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1207642).length < 2 ^ (prefixWord ++ tailWord_1207642).sum := by decide
  have hdescent : baseEnd_1207642 < baseStart_1207642 := by decide
  rcases family_descends (prefixWord ++ tailWord_1207642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1207730 : List Nat := [3, 2, 1, 1, 1, 1, 2, 1, 3, 7]
def baseStart_1207730 : Nat := 118140960795 + 1207730 * 2 ^ 59
def prefixEnd_1207730 : Nat := 4983230072969 + 3 ^ 40 * 1207730 * 2
def baseEnd_1207730 : Nat := 413430660569776656347171

theorem tailTrace_1207730 : CollatzResearch.WordTrace tailWord_1207730 prefixEnd_1207730 413430660569776656347171 := by
  unfold tailWord_1207730
  simp only [CollatzResearch.WordTrace]
  refine ⟨11012382978651987176901161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29366354609738632471736429 11012382978651987176901161)
  ·
    refine ⟨8259287233988990382675871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11012382978651987176901161 8259287233988990382675871)
    ·
      refine ⟨12388930850983485574013807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8259287233988990382675871 12388930850983485574013807)
      ·
        refine ⟨18583396276475228361020711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12388930850983485574013807 18583396276475228361020711)
        ·
          refine ⟨27875094414712842541531067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18583396276475228361020711 27875094414712842541531067)
          ·
            refine ⟨41812641622069263812296601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27875094414712842541531067 41812641622069263812296601)
            ·
              refine ⟨31359481216551947859222451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41812641622069263812296601 31359481216551947859222451)
              ·
                refine ⟨47039221824827921788833677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31359481216551947859222451 47039221824827921788833677)
                ·
                  refine ⟨17639708184310470670812629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47039221824827921788833677 17639708184310470670812629)
                  ·
                    refine ⟨413430660569776656347171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17639708184310470670812629 413430660569776656347171)
                    ·
                      rfl

theorem cell22_1207730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 1, 3, 7].length) (baseStart_1207730 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1207730 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1207730 prefixEnd_1207730 := by exact prefixLift 1207730
  have htrace : WordTrace (prefixWord ++ tailWord_1207730) baseStart_1207730 baseEnd_1207730 := by
    simpa [prefixWord, tailWord_1207730, baseEnd_1207730] using wordTrace_append hprefix tailTrace_1207730
  have hstable : (prefixWord ++ tailWord_1207730).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1207730).length < 2 ^ (prefixWord ++ tailWord_1207730).sum := by decide
  have hdescent : baseEnd_1207730 < baseStart_1207730 := by decide
  rcases family_descends (prefixWord ++ tailWord_1207730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1207764 : List Nat := [2, 4, 1, 2, 3, 1, 1, 1, 2, 5]
def baseStart_1207764 : Nat := 118140960795 + 1207764 * 2 ^ 59
def prefixEnd_1207764 : Nat := 4983230072969 + 3 ^ 40 * 1207764 * 2
def baseEnd_1207764 : Nat := 413442299464611900997067

theorem tailTrace_1207764 : CollatzResearch.WordTrace tailWord_1207764 prefixEnd_1207764 413442299464611900997067 := by
  unfold tailWord_1207764
  simp only [CollatzResearch.WordTrace]
  refine ⟨22025385998242386257171173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29367181330989848342894897 22025385998242386257171173)
  ·
    refine ⟨4129759874670447423219595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22025385998242386257171173 4129759874670447423219595)
    ·
      refine ⟨6194639812005671134829393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4129759874670447423219595 6194639812005671134829393)
      ·
        refine ⟨4645979859004253351122045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6194639812005671134829393 4645979859004253351122045)
        ·
          refine ⟨1742242447126595006670767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4645979859004253351122045 1742242447126595006670767)
          ·
            refine ⟨2613363670689892510006151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1742242447126595006670767 2613363670689892510006151)
            ·
              refine ⟨3920045506034838765009227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2613363670689892510006151 3920045506034838765009227)
              ·
                refine ⟨5880068259052258147513841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3920045506034838765009227 5880068259052258147513841)
                ·
                  refine ⟨4410051194289193610635381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5880068259052258147513841 4410051194289193610635381)
                  ·
                    refine ⟨413442299464611900997067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4410051194289193610635381 413442299464611900997067)
                    ·
                      rfl

theorem cell22_1207764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 1, 1, 2, 5].length) (baseStart_1207764 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1207764 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1207764 prefixEnd_1207764 := by exact prefixLift 1207764
  have htrace : WordTrace (prefixWord ++ tailWord_1207764) baseStart_1207764 baseEnd_1207764 := by
    simpa [prefixWord, tailWord_1207764, baseEnd_1207764] using wordTrace_append hprefix tailTrace_1207764
  have hstable : (prefixWord ++ tailWord_1207764).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1207764).length < 2 ^ (prefixWord ++ tailWord_1207764).sum := by decide
  have hdescent : baseEnd_1207764 < baseStart_1207764 := by decide
  rcases family_descends (prefixWord ++ tailWord_1207764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1207777 : List Nat := [1, 2, 3, 1, 2, 4, 1, 2, 6]
def baseStart_1207777 : Nat := 118140960795 + 1207777 * 2 ^ 59
def prefixEnd_1207777 : Nat := 4983230072969 + 3 ^ 40 * 1207777 * 2
def baseEnd_1207777 : Nat := 137815583210094733474009

theorem tailTrace_1207777 : CollatzResearch.WordTrace tailWord_1207777 prefixEnd_1207777 137815583210094733474009 := by
  unfold tailWord_1207777
  simp only [CollatzResearch.WordTrace]
  refine ⟨44051246145437675734565585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29367497430291783823043723 44051246145437675734565585)
  ·
    refine ⟨33038434609078256800924189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44051246145437675734565585 33038434609078256800924189)
    ·
      refine ⟨12389412978404346300346571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33038434609078256800924189 12389412978404346300346571)
      ·
        refine ⟨18584119467606519450519857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12389412978404346300346571 18584119467606519450519857)
        ·
          refine ⟨13938089600704889587889893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18584119467606519450519857 13938089600704889587889893)
          ·
            refine ⟨2613391800132166797729355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13938089600704889587889893 2613391800132166797729355)
            ·
              refine ⟨3920087700198250196594033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2613391800132166797729355 3920087700198250196594033)
              ·
                refine ⟨2940065775148687647445525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3920087700198250196594033 2940065775148687647445525)
                ·
                  refine ⟨137815583210094733474009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2940065775148687647445525 137815583210094733474009)
                  ·
                    rfl

theorem cell22_1207777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 1, 2, 6].length) (baseStart_1207777 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1207777 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1207777 prefixEnd_1207777 := by exact prefixLift 1207777
  have htrace : WordTrace (prefixWord ++ tailWord_1207777) baseStart_1207777 baseEnd_1207777 := by
    simpa [prefixWord, tailWord_1207777, baseEnd_1207777] using wordTrace_append hprefix tailTrace_1207777
  have hstable : (prefixWord ++ tailWord_1207777).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1207777).length < 2 ^ (prefixWord ++ tailWord_1207777).sum := by decide
  have hdescent : baseEnd_1207777 < baseStart_1207777 := by decide
  rcases family_descends (prefixWord ++ tailWord_1207777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1207792 : List Nat := [2, 1, 1, 1, 3, 4, 2, 2, 1, 5]
def baseStart_1207792 : Nat := 118140960795 + 1207792 * 2 ^ 59
def prefixEnd_1207792 : Nat := 4983230072969 + 3 ^ 40 * 1207792 * 2
def baseEnd_1207792 : Nat := 413451884436829161296981

theorem tailTrace_1207792 : CollatzResearch.WordTrace tailWord_1207792 prefixEnd_1207792 413451884436829161296981 := by
  unfold tailWord_1207792
  simp only [CollatzResearch.WordTrace]
  refine ⟨22025896620191666648180815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29367862160255555530907753 22025896620191666648180815)
  ·
    refine ⟨33038844930287499972271223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22025896620191666648180815 33038844930287499972271223)
    ·
      refine ⟨49558267395431249958406835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33038844930287499972271223 49558267395431249958406835)
      ·
        refine ⟨74337401093146874937610253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49558267395431249958406835 74337401093146874937610253)
        ·
          refine ⟨27876525409930078101603845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74337401093146874937610253 27876525409930078101603845)
          ·
            refine ⟨5226848514361889644050721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27876525409930078101603845 5226848514361889644050721)
            ·
              refine ⟨3920136385771417233038041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5226848514361889644050721 3920136385771417233038041)
              ·
                refine ⟨2940102289328562924778531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3920136385771417233038041 2940102289328562924778531)
                ·
                  refine ⟨4410153433992844387167797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2940102289328562924778531 4410153433992844387167797)
                  ·
                    refine ⟨413451884436829161296981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4410153433992844387167797 413451884436829161296981)
                    ·
                      rfl

theorem cell22_1207792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2, 2, 1, 5].length) (baseStart_1207792 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1207792 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1207792 prefixEnd_1207792 := by exact prefixLift 1207792
  have htrace : WordTrace (prefixWord ++ tailWord_1207792) baseStart_1207792 baseEnd_1207792 := by
    simpa [prefixWord, tailWord_1207792, baseEnd_1207792] using wordTrace_append hprefix tailTrace_1207792
  have hstable : (prefixWord ++ tailWord_1207792).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1207792).length < 2 ^ (prefixWord ++ tailWord_1207792).sum := by decide
  have hdescent : baseEnd_1207792 < baseStart_1207792 := by decide
  rcases family_descends (prefixWord ++ tailWord_1207792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1207837 : List Nat := [1, 4, 2, 2, 1, 1, 1, 1, 2, 7]
def baseStart_1207837 : Nat := 118140960795 + 1207837 * 2 ^ 59
def prefixEnd_1207837 : Nat := 4983230072969 + 3 ^ 40 * 1207837 * 2
def baseEnd_1207837 : Nat := 413467288856464043921843

theorem tailTrace_1207837 : CollatzResearch.WordTrace tailWord_1207837 prefixEnd_1207837 413467288856464043921843 := by
  unfold tailWord_1207837
  simp only [CollatzResearch.WordTrace]
  refine ⟨44053434525220305981749765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29368956350146870654499843 44053434525220305981749765)
  ·
    refine ⟨8260018973478807371578081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44053434525220305981749765 8260018973478807371578081)
    ·
      refine ⟨6195014230109105528683561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8260018973478807371578081 6195014230109105528683561)
      ·
        refine ⟨4646260672581829146512671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6195014230109105528683561 4646260672581829146512671)
        ·
          refine ⟨6969391008872743719769007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4646260672581829146512671 6969391008872743719769007)
          ·
            refine ⟨10454086513309115579653511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6969391008872743719769007 10454086513309115579653511)
            ·
              refine ⟨15681129769963673369480267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10454086513309115579653511 15681129769963673369480267)
              ·
                refine ⟨23521694654945510054220401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15681129769963673369480267 23521694654945510054220401)
                ·
                  refine ⟨17641270991209132540665301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23521694654945510054220401 17641270991209132540665301)
                  ·
                    refine ⟨413467288856464043921843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17641270991209132540665301 413467288856464043921843)
                    ·
                      rfl

theorem cell22_1207837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 1, 2, 7].length) (baseStart_1207837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1207837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1207837 prefixEnd_1207837 := by exact prefixLift 1207837
  have htrace : WordTrace (prefixWord ++ tailWord_1207837) baseStart_1207837 baseEnd_1207837 := by
    simpa [prefixWord, tailWord_1207837, baseEnd_1207837] using wordTrace_append hprefix tailTrace_1207837
  have hstable : (prefixWord ++ tailWord_1207837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1207837).length < 2 ^ (prefixWord ++ tailWord_1207837).sum := by decide
  have hdescent : baseEnd_1207837 < baseStart_1207837 := by decide
  rcases family_descends (prefixWord ++ tailWord_1207837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1207871 : List Nat := [1, 1, 2, 2, 3, 5, 1, 1, 3, 3]
def baseStart_1207871 : Nat := 118140960795 + 1207871 * 2 ^ 59
def prefixEnd_1207871 : Nat := 4983230072969 + 3 ^ 40 * 1207871 * 2
def baseEnd_1207871 : Nat := 413478927751299288571739

theorem tailTrace_1207871 : CollatzResearch.WordTrace tailWord_1207871 prefixEnd_1207871 413478927751299288571739 := by
  unfold tailWord_1207871
  simp only [CollatzResearch.WordTrace]
  refine ⟨44054674607097129788487467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29369783071398086525658311 44054674607097129788487467)
  ·
    refine ⟨66082011910645694682731201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44054674607097129788487467 66082011910645694682731201)
    ·
      refine ⟨49561508932984271012048401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66082011910645694682731201 49561508932984271012048401)
      ·
        refine ⟨37171131699738203259036301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49561508932984271012048401 37171131699738203259036301)
        ·
          refine ⟨13939174387401826222138613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37171131699738203259036301 13939174387401826222138613)
          ·
            refine ⟨1306797598818921208325495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13939174387401826222138613 1306797598818921208325495)
            ·
              refine ⟨1960196398228381812488243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1306797598818921208325495 1960196398228381812488243)
              ·
                refine ⟨2940294597342572718732365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1960196398228381812488243 2940294597342572718732365)
                ·
                  refine ⟨1102610474003464769524637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2940294597342572718732365 1102610474003464769524637)
                  ·
                    refine ⟨413478927751299288571739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1102610474003464769524637 413478927751299288571739)
                    ·
                      rfl

theorem cell22_1207871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 1, 1, 3, 3].length) (baseStart_1207871 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1207871 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1207871 prefixEnd_1207871 := by exact prefixLift 1207871
  have htrace : WordTrace (prefixWord ++ tailWord_1207871) baseStart_1207871 baseEnd_1207871 := by
    simpa [prefixWord, tailWord_1207871, baseEnd_1207871] using wordTrace_append hprefix tailTrace_1207871
  have hstable : (prefixWord ++ tailWord_1207871).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1207871).length < 2 ^ (prefixWord ++ tailWord_1207871).sum := by decide
  have hdescent : baseEnd_1207871 < baseStart_1207871 := by decide
  rcases family_descends (prefixWord ++ tailWord_1207871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1207882 : List Nat := [3, 1, 2, 1, 1, 3, 2, 1, 1, 7]
def baseStart_1207882 : Nat := 118140960795 + 1207882 * 2 ^ 59
def prefixEnd_1207882 : Nat := 4983230072969 + 3 ^ 40 * 1207882 * 2
def baseEnd_1207882 : Nat := 413482693276098926546705

theorem tailTrace_1207882 : CollatzResearch.WordTrace tailWord_1207882 prefixEnd_1207882 413482693276098926546705 := by
  unfold tailWord_1207882
  simp only [CollatzResearch.WordTrace]
  refine ⟨11013768952514319666784475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29370050540038185778091933 11013768952514319666784475)
  ·
    refine ⟨16520653428771479500176713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11013768952514319666784475 16520653428771479500176713)
    ·
      refine ⟨12390490071578609625132535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16520653428771479500176713 12390490071578609625132535)
      ·
        refine ⟨18585735107367914437698803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12390490071578609625132535 18585735107367914437698803)
        ·
          refine ⟨27878602661051871656548205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18585735107367914437698803 27878602661051871656548205)
          ·
            refine ⟨10454475997894451871205577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27878602661051871656548205 10454475997894451871205577)
            ·
              refine ⟨7840856998420838903404183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10454475997894451871205577 7840856998420838903404183)
              ·
                refine ⟨11761285497631258355106275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7840856998420838903404183 11761285497631258355106275)
                ·
                  refine ⟨17641928246446887532659413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11761285497631258355106275 17641928246446887532659413)
                  ·
                    refine ⟨413482693276098926546705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17641928246446887532659413 413482693276098926546705)
                    ·
                      rfl

theorem cell22_1207882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 1, 1, 7].length) (baseStart_1207882 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1207882 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1207882 prefixEnd_1207882 := by exact prefixLift 1207882
  have htrace : WordTrace (prefixWord ++ tailWord_1207882) baseStart_1207882 baseEnd_1207882 := by
    simpa [prefixWord, tailWord_1207882, baseEnd_1207882] using wordTrace_append hprefix tailTrace_1207882
  have hstable : (prefixWord ++ tailWord_1207882).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1207882).length < 2 ^ (prefixWord ++ tailWord_1207882).sum := by decide
  have hdescent : baseEnd_1207882 < baseStart_1207882 := by decide
  rcases family_descends (prefixWord ++ tailWord_1207882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1207884 : List Nat := [2, 2, 1, 3, 1, 4, 1, 3, 5]
def baseStart_1207884 : Nat := 118140960795 + 1207884 * 2 ^ 59
def prefixEnd_1207884 : Nat := 4983230072969 + 3 ^ 40 * 1207884 * 2
def baseEnd_1207884 : Nat := 137827792638990529332233

theorem tailTrace_1207884 : CollatzResearch.WordTrace tailWord_1207884 prefixEnd_1207884 137827792638990529332233 := by
  unfold tailWord_1207884
  simp only [CollatzResearch.WordTrace]
  refine ⟨22027574378025016504355353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29370099170700022005807137 22027574378025016504355353)
  ·
    refine ⟨16520680783518762378266515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22027574378025016504355353 16520680783518762378266515)
    ·
      refine ⟨24781021175278143567399773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16520680783518762378266515 24781021175278143567399773)
      ·
        refine ⟨9292882940729303837774915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24781021175278143567399773 9292882940729303837774915)
        ·
          refine ⟨13939324411093955756662373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9292882940729303837774915 13939324411093955756662373)
          ·
            refine ⟨2613623327080116704374195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13939324411093955756662373 2613623327080116704374195)
            ·
              refine ⟨3920434990620175056561293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2613623327080116704374195 3920434990620175056561293)
              ·
                refine ⟨1470163121482565646210485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3920434990620175056561293 1470163121482565646210485)
                ·
                  refine ⟨137827792638990529332233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1470163121482565646210485 137827792638990529332233)
                  ·
                    rfl

theorem cell22_1207884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 1, 3, 5].length) (baseStart_1207884 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1207884 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1207884 prefixEnd_1207884 := by exact prefixLift 1207884
  have htrace : WordTrace (prefixWord ++ tailWord_1207884) baseStart_1207884 baseEnd_1207884 := by
    simpa [prefixWord, tailWord_1207884, baseEnd_1207884] using wordTrace_append hprefix tailTrace_1207884
  have hstable : (prefixWord ++ tailWord_1207884).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1207884).length < 2 ^ (prefixWord ++ tailWord_1207884).sum := by decide
  have hdescent : baseEnd_1207884 < baseStart_1207884 := by decide
  rcases family_descends (prefixWord ++ tailWord_1207884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1207927 : List Nat := [1, 1, 3, 1, 1, 3, 1, 1, 5, 5]
def baseStart_1207927 : Nat := 118140960795 + 1207927 * 2 ^ 59
def prefixEnd_1207927 : Nat := 4983230072969 + 3 ^ 40 * 1207927 * 2
def baseEnd_1207927 : Nat := 413498097695733809171567

theorem tailTrace_1207927 : CollatzResearch.WordTrace tailWord_1207927 prefixEnd_1207927 413498097695733809171567 := by
  unfold tailWord_1207927
  simp only [CollatzResearch.WordTrace]
  refine ⟨44056717094894251352526035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29371144729929500901684023 44056717094894251352526035)
  ·
    refine ⟨66085075642341377028789053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44056717094894251352526035 66085075642341377028789053)
    ·
      refine ⟨24781903365878016385795895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66085075642341377028789053 24781903365878016385795895)
      ·
        refine ⟨37172855048817024578693843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24781903365878016385795895 37172855048817024578693843)
        ·
          refine ⟨55759282573225536868040765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37172855048817024578693843 55759282573225536868040765)
          ·
            refine ⟨20909730964959576325515287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55759282573225536868040765 20909730964959576325515287)
            ·
              refine ⟨31364596447439364488272931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20909730964959576325515287 31364596447439364488272931)
              ·
                refine ⟨47046894671159046732409397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31364596447439364488272931 47046894671159046732409397)
                ·
                  refine ⟨4410646375421160631163381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 47046894671159046732409397 4410646375421160631163381)
                  ·
                    refine ⟨413498097695733809171567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4410646375421160631163381 413498097695733809171567)
                    ·
                      rfl

theorem cell22_1207927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 1, 5, 5].length) (baseStart_1207927 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1207927 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1207927 prefixEnd_1207927 := by exact prefixLift 1207927
  have htrace : WordTrace (prefixWord ++ tailWord_1207927) baseStart_1207927 baseEnd_1207927 := by
    simpa [prefixWord, tailWord_1207927, baseEnd_1207927] using wordTrace_append hprefix tailTrace_1207927
  have hstable : (prefixWord ++ tailWord_1207927).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1207927).length < 2 ^ (prefixWord ++ tailWord_1207927).sum := by decide
  have hdescent : baseEnd_1207927 < baseStart_1207927 := by decide
  rcases family_descends (prefixWord ++ tailWord_1207927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1207957 : List Nat := [1, 3, 2, 1, 1, 1, 1, 12]
def baseStart_1207957 : Nat := 118140960795 + 1207957 * 2 ^ 59
def prefixEnd_1207957 : Nat := 4983230072969 + 3 ^ 40 * 1207957 * 2
def baseEnd_1207957 : Nat := 45945374145424858991275

theorem tailTrace_1207957 : CollatzResearch.WordTrace tailWord_1207957 prefixEnd_1207957 45945374145424858991275 := by
  unfold tailWord_1207957
  simp only [CollatzResearch.WordTrace]
  refine ⟨44057811284785566476118125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29371874189857044317412083 44057811284785566476118125)
  ·
    refine ⟨16521679231794587428544297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44057811284785566476118125 16521679231794587428544297)
    ·
      refine ⟨12391259423845940571408223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16521679231794587428544297 12391259423845940571408223)
      ·
        refine ⟨18586889135768910857112335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12391259423845940571408223 18586889135768910857112335)
        ·
          refine ⟨27880333703653366285668503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18586889135768910857112335 27880333703653366285668503)
          ·
            refine ⟨41820500555480049428502755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27880333703653366285668503 41820500555480049428502755)
            ·
              refine ⟨62730750833220074142754133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41820500555480049428502755 62730750833220074142754133)
              ·
                refine ⟨45945374145424858991275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 62730750833220074142754133 45945374145424858991275)
                ·
                  rfl

theorem cell22_1207957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 12].length) (baseStart_1207957 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1207957 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1207957 prefixEnd_1207957 := by exact prefixLift 1207957
  have htrace : WordTrace (prefixWord ++ tailWord_1207957) baseStart_1207957 baseEnd_1207957 := by
    simpa [prefixWord, tailWord_1207957, baseEnd_1207957] using wordTrace_append hprefix tailTrace_1207957
  have hstable : (prefixWord ++ tailWord_1207957).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1207957).length < 2 ^ (prefixWord ++ tailWord_1207957).sum := by decide
  have hdescent : baseEnd_1207957 < baseStart_1207957 := by decide
  rcases family_descends (prefixWord ++ tailWord_1207957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1207959 : List Nat := [1, 1, 3, 3, 2, 3, 1, 1, 1, 6]
def baseStart_1207959 : Nat := 118140960795 + 1207959 * 2 ^ 59
def prefixEnd_1207959 : Nat := 4983230072969 + 3 ^ 40 * 1207959 * 2
def baseEnd_1207959 : Nat := 413509051949696392371469

theorem tailTrace_1207959 : CollatzResearch.WordTrace tailWord_1207959 prefixEnd_1207959 413509051949696392371469 := by
  unfold tailWord_1207959
  simp only [CollatzResearch.WordTrace]
  refine ⟨44057884230778320817690931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29371922820518880545127287 44057884230778320817690931)
  ·
    refine ⟨66086826346167481226536397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44057884230778320817690931 66086826346167481226536397)
    ·
      refine ⟨24782559879812805459951149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66086826346167481226536397 24782559879812805459951149)
      ·
        refine ⟨9293459954929802047481681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24782559879812805459951149 9293459954929802047481681)
        ·
          refine ⟨6970094966197351535611261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9293459954929802047481681 6970094966197351535611261)
          ·
            refine ⟨2613785612324006825854223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6970094966197351535611261 2613785612324006825854223)
            ·
              refine ⟨3920678418486010238781335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2613785612324006825854223 3920678418486010238781335)
              ·
                refine ⟨5881017627729015358172003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3920678418486010238781335 5881017627729015358172003)
                ·
                  refine ⟨8821526441593523037258005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5881017627729015358172003 8821526441593523037258005)
                  ·
                    refine ⟨413509051949696392371469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8821526441593523037258005 413509051949696392371469)
                    ·
                      rfl

theorem cell22_1207959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 1, 1, 1, 6].length) (baseStart_1207959 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1207959 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1207959 prefixEnd_1207959 := by exact prefixLift 1207959
  have htrace : WordTrace (prefixWord ++ tailWord_1207959) baseStart_1207959 baseEnd_1207959 := by
    simpa [prefixWord, tailWord_1207959, baseEnd_1207959] using wordTrace_append hprefix tailTrace_1207959
  have hstable : (prefixWord ++ tailWord_1207959).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1207959).length < 2 ^ (prefixWord ++ tailWord_1207959).sum := by decide
  have hdescent : baseEnd_1207959 < baseStart_1207959 := by decide
  rcases family_descends (prefixWord ++ tailWord_1207959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1208081 : List Nat := [1, 2, 2, 1, 1, 3, 1, 7, 4]
def baseStart_1208081 : Nat := 118140960795 + 1208081 * 2 ^ 59
def prefixEnd_1208081 : Nat := 4983230072969 + 3 ^ 40 * 1208081 * 2
def baseEnd_1208081 : Nat := 137850271680976246940365

theorem tailTrace_1208081 : CollatzResearch.WordTrace tailWord_1208081 prefixEnd_1208081 137850271680976246940365 := by
  unfold tailWord_1208081
  simp only [CollatzResearch.WordTrace]
  refine ⟨44062333936336335653632097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29374889290890890435754731 44062333936336335653632097)
  ·
    refine ⟨33046750452252251740224073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44062333936336335653632097 33046750452252251740224073)
    ·
      refine ⟨24785062839189188805168055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33046750452252251740224073 24785062839189188805168055)
      ·
        refine ⟨37177594258783783207752083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24785062839189188805168055 37177594258783783207752083)
        ·
          refine ⟨55766391388175674811628125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37177594258783783207752083 55766391388175674811628125)
          ·
            refine ⟨20912396770565878054360547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55766391388175674811628125 20912396770565878054360547)
            ·
              refine ⟨31368595155848817081540821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20912396770565878054360547 31368595155848817081540821)
              ·
                refine ⟨735201448965206650348613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 31368595155848817081540821 735201448965206650348613)
                ·
                  refine ⟨137850271680976246940365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 735201448965206650348613 137850271680976246940365)
                  ·
                    rfl

theorem cell22_1208081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 7, 4].length) (baseStart_1208081 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1208081 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1208081 prefixEnd_1208081 := by exact prefixLift 1208081
  have htrace : WordTrace (prefixWord ++ tailWord_1208081) baseStart_1208081 baseEnd_1208081 := by
    simpa [prefixWord, tailWord_1208081, baseEnd_1208081] using wordTrace_append hprefix tailTrace_1208081
  have hstable : (prefixWord ++ tailWord_1208081).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1208081).length < 2 ^ (prefixWord ++ tailWord_1208081).sum := by decide
  have hdescent : baseEnd_1208081 < baseStart_1208081 := by decide
  rcases family_descends (prefixWord ++ tailWord_1208081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1208098 : List Nat := [3, 3, 1, 1, 2, 1, 3, 4, 4]
def baseStart_1208098 : Nat := 118140960795 + 1208098 * 2 ^ 59
def prefixEnd_1208098 : Nat := 4983230072969 + 3 ^ 40 * 1208098 * 2
def baseEnd_1208098 : Nat := 137852211496782121048681

theorem tailTrace_1208098 : CollatzResearch.WordTrace tailWord_1208098 prefixEnd_1208098 137852211496782121048681 := by
  unfold tailWord_1208098
  simp only [CollatzResearch.WordTrace]
  refine ⟨11015738494318686889250237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29375302651516498371333965 11015738494318686889250237)
  ·
    refine ⟨4130901935369507583468839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11015738494318686889250237 4130901935369507583468839)
    ·
      refine ⟨6196352903054261375203259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4130901935369507583468839 6196352903054261375203259)
      ·
        refine ⟨9294529354581392062804889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6196352903054261375203259 9294529354581392062804889)
        ·
          refine ⟨6970897015936044047103667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9294529354581392062804889 6970897015936044047103667)
          ·
            refine ⟨10456345523904066070655501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6970897015936044047103667 10456345523904066070655501)
            ·
              refine ⟨3921129571464024776495813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10456345523904066070655501 3921129571464024776495813)
              ·
                refine ⟨735211794649504645592965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3921129571464024776495813 735211794649504645592965)
                ·
                  refine ⟨137852211496782121048681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 735211794649504645592965 137852211496782121048681)
                  ·
                    rfl

theorem cell22_1208098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 3, 4, 4].length) (baseStart_1208098 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1208098 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1208098 prefixEnd_1208098 := by exact prefixLift 1208098
  have htrace : WordTrace (prefixWord ++ tailWord_1208098) baseStart_1208098 baseEnd_1208098 := by
    simpa [prefixWord, tailWord_1208098, baseEnd_1208098] using wordTrace_append hprefix tailTrace_1208098
  have hstable : (prefixWord ++ tailWord_1208098).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1208098).length < 2 ^ (prefixWord ++ tailWord_1208098).sum := by decide
  have hdescent : baseEnd_1208098 < baseStart_1208098 := by decide
  rcases family_descends (prefixWord ++ tailWord_1208098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1208113 : List Nat := [1, 2, 2, 3, 2, 2, 2, 3, 2, 3]
def baseStart_1208113 : Nat := 118140960795 + 1208113 * 2 ^ 59
def prefixEnd_1208113 : Nat := 4983230072969 + 3 ^ 40 * 1208113 * 2
def baseEnd_1208113 : Nat := 413561769296891324020997

theorem tailTrace_1208113 : CollatzResearch.WordTrace tailWord_1208113 prefixEnd_1208113 413561769296891324020997 := by
  unfold tailWord_1208113
  simp only [CollatzResearch.WordTrace]
  refine ⟨44063501072220405118796993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29375667381480270079197995 44063501072220405118796993)
  ·
    refine ⟨33047625804165303839097745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44063501072220405118796993 33047625804165303839097745)
    ·
      refine ⟨24785719353123977879323309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33047625804165303839097745 24785719353123977879323309)
      ·
        refine ⟨9294644757421491704746241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24785719353123977879323309 9294644757421491704746241)
        ·
          refine ⟨6970983568066118778559681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9294644757421491704746241 6970983568066118778559681)
          ·
            refine ⟨5228237676049589083919761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6970983568066118778559681 5228237676049589083919761)
            ·
              refine ⟨3921178257037191812939821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5228237676049589083919761 3921178257037191812939821)
              ·
                refine ⟨1470441846388946929852433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3921178257037191812939821 1470441846388946929852433)
                ·
                  refine ⟨1102831384791710197389325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1470441846388946929852433 1102831384791710197389325)
                  ·
                    refine ⟨413561769296891324020997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1102831384791710197389325 413561769296891324020997)
                    ·
                      rfl

theorem cell22_1208113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 2, 3, 2, 3].length) (baseStart_1208113 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1208113 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1208113 prefixEnd_1208113 := by exact prefixLift 1208113
  have htrace : WordTrace (prefixWord ++ tailWord_1208113) baseStart_1208113 baseEnd_1208113 := by
    simpa [prefixWord, tailWord_1208113, baseEnd_1208113] using wordTrace_append hprefix tailTrace_1208113
  have hstable : (prefixWord ++ tailWord_1208113).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1208113).length < 2 ^ (prefixWord ++ tailWord_1208113).sum := by decide
  have hdescent : baseEnd_1208113 < baseStart_1208113 := by decide
  rcases family_descends (prefixWord ++ tailWord_1208113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1208134 : List Nat := [6, 1, 1, 2, 1, 3, 2, 1, 1, 4]
def baseStart_1208134 : Nat := 118140960795 + 1208134 * 2 ^ 59
def prefixEnd_1208134 : Nat := 4983230072969 + 3 ^ 40 * 1208134 * 2
def baseEnd_1208134 : Nat := 413568958026054269245933

theorem tailTrace_1208134 : CollatzResearch.WordTrace tailWord_1208134 prefixEnd_1208134 413568958026054269245933 := by
  unfold tailWord_1208134
  simp only [CollatzResearch.WordTrace]
  refine ⟨1377008343910760178290983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 29376178003429550470207637 1377008343910760178290983)
  ·
    refine ⟨2065512515866140267436475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1377008343910760178290983 2065512515866140267436475)
    ·
      refine ⟨3098268773799210401154713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2065512515866140267436475 3098268773799210401154713)
      ·
        refine ⟨2323701580349407800866035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3098268773799210401154713 2323701580349407800866035)
        ·
          refine ⟨3485552370524111701299053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2323701580349407800866035 3485552370524111701299053)
          ·
            refine ⟨1307082138946541887987145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3485552370524111701299053 1307082138946541887987145)
            ·
              refine ⟨980311604209906415990359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1307082138946541887987145 980311604209906415990359)
              ·
                refine ⟨1470467406314859623985539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 980311604209906415990359 1470467406314859623985539)
                ·
                  refine ⟨2205701109472289435978309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1470467406314859623985539 2205701109472289435978309)
                  ·
                    refine ⟨413568958026054269245933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2205701109472289435978309 413568958026054269245933)
                    ·
                      rfl

theorem cell22_1208134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 2, 1, 1, 4].length) (baseStart_1208134 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1208134 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1208134 prefixEnd_1208134 := by exact prefixLift 1208134
  have htrace : WordTrace (prefixWord ++ tailWord_1208134) baseStart_1208134 baseEnd_1208134 := by
    simpa [prefixWord, tailWord_1208134, baseEnd_1208134] using wordTrace_append hprefix tailTrace_1208134
  have hstable : (prefixWord ++ tailWord_1208134).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1208134).length < 2 ^ (prefixWord ++ tailWord_1208134).sum := by decide
  have hdescent : baseEnd_1208134 < baseStart_1208134 := by decide
  rcases family_descends (prefixWord ++ tailWord_1208134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1208222 : List Nat := [4, 3, 1, 3, 1, 1, 1, 3, 5]
def baseStart_1208222 : Nat := 118140960795 + 1208222 * 2 ^ 59
def prefixEnd_1208222 : Nat := 4983230072969 + 3 ^ 40 * 1208222 * 2
def baseEnd_1208222 : Nat := 137866360741483791015221

theorem tailTrace_1208222 : CollatzResearch.WordTrace tailWord_1208222 prefixEnd_1208222 137866360741483791015221 := by
  unfold tailWord_1208222
  simp only [CollatzResearch.WordTrace]
  refine ⟨5508434578603189591814365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29378317752550344489676613 5508434578603189591814365)
  ·
    refine ⟨2065662966976196096930387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5508434578603189591814365 2065662966976196096930387)
    ·
      refine ⟨3098494450464294145395581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2065662966976196096930387 3098494450464294145395581)
      ·
        refine ⟨1161935418924110304523343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3098494450464294145395581 1161935418924110304523343)
        ·
          refine ⟨1742903128386165456785015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1161935418924110304523343 1742903128386165456785015)
          ·
            refine ⟨2614354692579248185177523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1742903128386165456785015 2614354692579248185177523)
            ·
              refine ⟨3921532038868872277766285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2614354692579248185177523 3921532038868872277766285)
              ·
                refine ⟨1470574514575827104162357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3921532038868872277766285 1470574514575827104162357)
                ·
                  refine ⟨137866360741483791015221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1470574514575827104162357 137866360741483791015221)
                  ·
                    rfl

theorem cell22_1208222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 1, 3, 5].length) (baseStart_1208222 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1208222 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1208222 prefixEnd_1208222 := by exact prefixLift 1208222
  have htrace : WordTrace (prefixWord ++ tailWord_1208222) baseStart_1208222 baseEnd_1208222 := by
    simpa [prefixWord, tailWord_1208222, baseEnd_1208222] using wordTrace_append hprefix tailTrace_1208222
  have hstable : (prefixWord ++ tailWord_1208222).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1208222).length < 2 ^ (prefixWord ++ tailWord_1208222).sum := by decide
  have hdescent : baseEnd_1208222 < baseStart_1208222 := by decide
  rcases family_descends (prefixWord ++ tailWord_1208222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1208295 : List Nat := [1, 1, 5, 2, 3, 1, 3, 6]
def baseStart_1208295 : Nat := 118140960795 + 1208295 * 2 ^ 59
def prefixEnd_1208295 : Nat := 4983230072969 + 3 ^ 40 * 1208295 * 2
def baseEnd_1208295 : Nat := 45958230179589279552271

theorem tailTrace_1208295 : CollatzResearch.WordTrace tailWord_1208295 prefixEnd_1208295 45958230179589279552271 := by
  unfold tailWord_1208295
  simp only [CollatzResearch.WordTrace]
  refine ⟨44070139157561050201922339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29380092771707366801281559 44070139157561050201922339)
  ·
    refine ⟨66105208736341575302883509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44070139157561050201922339 66105208736341575302883509)
    ·
      refine ⟨6197363319032022684645329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 66105208736341575302883509 6197363319032022684645329)
      ·
        refine ⟨4648022489274017013483997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6197363319032022684645329 4648022489274017013483997)
        ·
          refine ⟨1743008433477756380056499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4648022489274017013483997 1743008433477756380056499)
          ·
            refine ⟨2614512650216634570084749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1743008433477756380056499 2614512650216634570084749)
            ·
              refine ⟨980442243831237963781781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2614512650216634570084749 980442243831237963781781)
              ·
                refine ⟨45958230179589279552271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 980442243831237963781781 45958230179589279552271)
                ·
                  rfl

theorem cell22_1208295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 3, 6].length) (baseStart_1208295 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1208295 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1208295 prefixEnd_1208295 := by exact prefixLift 1208295
  have htrace : WordTrace (prefixWord ++ tailWord_1208295) baseStart_1208295 baseEnd_1208295 := by
    simpa [prefixWord, tailWord_1208295, baseEnd_1208295] using wordTrace_append hprefix tailTrace_1208295
  have hstable : (prefixWord ++ tailWord_1208295).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1208295).length < 2 ^ (prefixWord ++ tailWord_1208295).sum := by decide
  have hdescent : baseEnd_1208295 < baseStart_1208295 := by decide
  rcases family_descends (prefixWord ++ tailWord_1208295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1208327 : List Nat := [1, 1, 4, 3, 1, 2, 2, 4, 1, 3]
def baseStart_1208327 : Nat := 118140960795 + 1208327 * 2 ^ 59
def prefixEnd_1208327 : Nat := 4983230072969 + 3 ^ 40 * 1208327 * 2
def baseEnd_1208327 : Nat := 413635025870266099170341

theorem tailTrace_1208327 : CollatzResearch.WordTrace tailWord_1208327 prefixEnd_1208327 413635025870266099170341 := by
  unfold tailWord_1208327
  simp only [CollatzResearch.WordTrace]
  refine ⟨44071306293445119667087235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29380870862296746444724823 44071306293445119667087235)
  ·
    refine ⟨66106959440167679500630853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44071306293445119667087235 66106959440167679500630853)
    ·
      refine ⟨12395054895031439906368285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 66106959440167679500630853 12395054895031439906368285)
      ·
        refine ⟨4648145585636789964888107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12395054895031439906368285 4648145585636789964888107)
        ·
          refine ⟨6972218378455184947332161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4648145585636789964888107 6972218378455184947332161)
          ·
            refine ⟨5229163783841388710499121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6972218378455184947332161 5229163783841388710499121)
            ·
              refine ⟨3921872837881041532874341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5229163783841388710499121 3921872837881041532874341)
              ·
                refine ⟨735351157102695287413939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3921872837881041532874341 735351157102695287413939)
                ·
                  refine ⟨1103026735654042931120909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 735351157102695287413939 1103026735654042931120909)
                  ·
                    refine ⟨413635025870266099170341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1103026735654042931120909 413635025870266099170341)
                    ·
                      rfl

theorem cell22_1208327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 2, 4, 1, 3].length) (baseStart_1208327 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1208327 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1208327 prefixEnd_1208327 := by exact prefixLift 1208327
  have htrace : WordTrace (prefixWord ++ tailWord_1208327) baseStart_1208327 baseEnd_1208327 := by
    simpa [prefixWord, tailWord_1208327, baseEnd_1208327] using wordTrace_append hprefix tailTrace_1208327
  have hstable : (prefixWord ++ tailWord_1208327).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1208327).length < 2 ^ (prefixWord ++ tailWord_1208327).sum := by decide
  have hdescent : baseEnd_1208327 < baseStart_1208327 := by decide
  rcases family_descends (prefixWord ++ tailWord_1208327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1208333 : List Nat := [1, 7, 1, 2, 1, 1, 3, 1, 2, 3]
def baseStart_1208333 : Nat := 118140960795 + 1208333 * 2 ^ 59
def prefixEnd_1208333 : Nat := 4983230072969 + 3 ^ 40 * 1208333 * 2
def baseEnd_1208333 : Nat := 413637079792884083520323

theorem tailTrace_1208333 : CollatzResearch.WordTrace tailWord_1208333 prefixEnd_1208333 413637079792884083520323 := by
  unfold tailWord_1208333
  simp only [CollatzResearch.WordTrace]
  refine ⟨44071525131423382691805653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29381016754282255127870435 44071525131423382691805653)
  ·
    refine ⟨1032926370267735531839195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 44071525131423382691805653 1032926370267735531839195)
    ·
      refine ⟨1549389555401603297758793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1032926370267735531839195 1549389555401603297758793)
      ·
        refine ⟨1162042166551202473319095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1549389555401603297758793 1162042166551202473319095)
        ·
          refine ⟨1743063249826803709978643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1162042166551202473319095 1743063249826803709978643)
          ·
            refine ⟨2614594874740205564967965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1743063249826803709978643 2614594874740205564967965)
            ·
              refine ⟨980473078027577086862987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2614594874740205564967965 980473078027577086862987)
              ·
                refine ⟨1470709617041365630294481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 980473078027577086862987 1470709617041365630294481)
                ·
                  refine ⟨1103032212781024222720861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1470709617041365630294481 1103032212781024222720861)
                  ·
                    refine ⟨413637079792884083520323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1103032212781024222720861 413637079792884083520323)
                    ·
                      rfl

theorem cell22_1208333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 3, 1, 2, 3].length) (baseStart_1208333 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1208333 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1208333 prefixEnd_1208333 := by exact prefixLift 1208333
  have htrace : WordTrace (prefixWord ++ tailWord_1208333) baseStart_1208333 baseEnd_1208333 := by
    simpa [prefixWord, tailWord_1208333, baseEnd_1208333] using wordTrace_append hprefix tailTrace_1208333
  have hstable : (prefixWord ++ tailWord_1208333).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1208333).length < 2 ^ (prefixWord ++ tailWord_1208333).sum := by decide
  have hdescent : baseEnd_1208333 < baseStart_1208333 := by decide
  rcases family_descends (prefixWord ++ tailWord_1208333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1208370 : List Nat := [3, 2, 1, 1, 2, 3, 2, 3, 1, 4]
def baseStart_1208370 : Nat := 118140960795 + 1208370 * 2 ^ 59
def prefixEnd_1208370 : Nat := 4983230072969 + 3 ^ 40 * 1208370 * 2
def baseEnd_1208370 : Nat := 413649745649028320345209

theorem tailTrace_1208370 : CollatzResearch.WordTrace tailWord_1208370 prefixEnd_1208370 413649745649028320345209 := by
  unfold tailWord_1208370
  simp only [CollatzResearch.WordTrace]
  refine ⟨11018218658072334502725641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29381916421526225340601709 11018218658072334502725641)
  ·
    refine ⟨8263663993554250877044231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11018218658072334502725641 8263663993554250877044231)
    ·
      refine ⟨12395495990331376315566347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8263663993554250877044231 12395495990331376315566347)
      ·
        refine ⟨18593243985497064473349521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12395495990331376315566347 18593243985497064473349521)
        ·
          refine ⟨13944932989122798355012141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18593243985497064473349521 13944932989122798355012141)
          ·
            refine ⟨5229349870921049383129553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13944932989122798355012141 5229349870921049383129553)
            ·
              refine ⟨3922012403190787037347165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5229349870921049383129553 3922012403190787037347165)
              ·
                refine ⟨1470754651196545139005187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3922012403190787037347165 1470754651196545139005187)
                ·
                  refine ⟨2206131976794817708507781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1470754651196545139005187 2206131976794817708507781)
                  ·
                    refine ⟨413649745649028320345209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2206131976794817708507781 413649745649028320345209)
                    ·
                      rfl

theorem cell22_1208370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 2, 3, 1, 4].length) (baseStart_1208370 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1208370 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1208370 prefixEnd_1208370 := by exact prefixLift 1208370
  have htrace : WordTrace (prefixWord ++ tailWord_1208370) baseStart_1208370 baseEnd_1208370 := by
    simpa [prefixWord, tailWord_1208370, baseEnd_1208370] using wordTrace_append hprefix tailTrace_1208370
  have hstable : (prefixWord ++ tailWord_1208370).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1208370).length < 2 ^ (prefixWord ++ tailWord_1208370).sum := by decide
  have hdescent : baseEnd_1208370 < baseStart_1208370 := by decide
  rcases family_descends (prefixWord ++ tailWord_1208370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1208385 : List Nat := [1, 2, 5, 1, 2, 1, 3, 1, 6]
def baseStart_1208385 : Nat := 118140960795 + 1208385 * 2 ^ 59
def prefixEnd_1208385 : Nat := 4983230072969 + 3 ^ 40 * 1208385 * 2
def baseEnd_1208385 : Nat := 137884960151857760406721

theorem tailTrace_1208385 : CollatzResearch.WordTrace tailWord_1208385 prefixEnd_1208385 137884960151857760406721 := by
  unfold tailWord_1208385
  simp only [CollatzResearch.WordTrace]
  refine ⟨44073421727234995572698609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29382281151489997048465739 44073421727234995572698609)
  ·
    refine ⟨33055066295426246679523957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44073421727234995572698609 33055066295426246679523957)
    ·
      refine ⟨3098912465196210626205371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 33055066295426246679523957 3098912465196210626205371)
      ·
        refine ⟨4648368697794315939308057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3098912465196210626205371 4648368697794315939308057)
        ·
          refine ⟨3486276523345736954481043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4648368697794315939308057 3486276523345736954481043)
          ·
            refine ⟨5229414785018605431721565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3486276523345736954481043 5229414785018605431721565)
            ·
              refine ⟨1961030544381977036895587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5229414785018605431721565 1961030544381977036895587)
              ·
                refine ⟨2941545816572965555343381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1961030544381977036895587 2941545816572965555343381)
                ·
                  refine ⟨137884960151857760406721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2941545816572965555343381 137884960151857760406721)
                  ·
                    rfl

theorem cell22_1208385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 3, 1, 6].length) (baseStart_1208385 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1208385 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1208385 prefixEnd_1208385 := by exact prefixLift 1208385
  have htrace : WordTrace (prefixWord ++ tailWord_1208385) baseStart_1208385 baseEnd_1208385 := by
    simpa [prefixWord, tailWord_1208385, baseEnd_1208385] using wordTrace_append hprefix tailTrace_1208385
  have hstable : (prefixWord ++ tailWord_1208385).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1208385).length < 2 ^ (prefixWord ++ tailWord_1208385).sum := by decide
  have hdescent : baseEnd_1208385 < baseStart_1208385 := by decide
  rcases family_descends (prefixWord ++ tailWord_1208385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1208470 : List Nat := [5, 3, 2, 1, 1, 1, 2, 3, 4]
def baseStart_1208470 : Nat := 118140960795 + 1208470 * 2 ^ 59
def prefixEnd_1208470 : Nat := 4983230072969 + 3 ^ 40 * 1208470 * 2
def baseEnd_1208470 : Nat := 137894659230887130948301

theorem tailTrace_1208470 : CollatzResearch.WordTrace tailWord_1208470 prefixEnd_1208470 137894659230887130948301 := by
  unfold tailWord_1208470
  simp only [CollatzResearch.WordTrace]
  refine ⟨2754782620745440943096429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 29384347954618036726361909 2754782620745440943096429)
  ·
    refine ⟨1033043482779540353661161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2754782620745440943096429 1033043482779540353661161)
    ·
      refine ⟨774782612084655265245871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1033043482779540353661161 774782612084655265245871)
      ·
        refine ⟨1162173918126982897868807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 774782612084655265245871 1162173918126982897868807)
        ·
          refine ⟨1743260877190474346803211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1162173918126982897868807 1743260877190474346803211)
          ·
            refine ⟨2614891315785711520204817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1743260877190474346803211 2614891315785711520204817)
            ·
              refine ⟨1961168486839283640153613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2614891315785711520204817 1961168486839283640153613)
              ·
                refine ⟨735438182564731365057605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1961168486839283640153613 735438182564731365057605)
                ·
                  refine ⟨137894659230887130948301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 735438182564731365057605 137894659230887130948301)
                  ·
                    rfl

theorem cell22_1208470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 2, 3, 4].length) (baseStart_1208470 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1208470 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1208470 prefixEnd_1208470 := by exact prefixLift 1208470
  have htrace : WordTrace (prefixWord ++ tailWord_1208470) baseStart_1208470 baseEnd_1208470 := by
    simpa [prefixWord, tailWord_1208470, baseEnd_1208470] using wordTrace_append hprefix tailTrace_1208470
  have hstable : (prefixWord ++ tailWord_1208470).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1208470).length < 2 ^ (prefixWord ++ tailWord_1208470).sum := by decide
  have hdescent : baseEnd_1208470 < baseStart_1208470 := by decide
  rcases family_descends (prefixWord ++ tailWord_1208470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1208479 : List Nat := [1, 1, 2, 6, 1, 1, 1, 5, 1, 3]
def baseStart_1208479 : Nat := 118140960795 + 1208479 * 2 ^ 59
def prefixEnd_1208479 : Nat := 4983230072969 + 3 ^ 40 * 1208479 * 2
def baseEnd_1208479 : Nat := 413687058576588369369875

theorem tailTrace_1208479 : CollatzResearch.WordTrace tailWord_1208479 prefixEnd_1208479 413687058576588369369875 := by
  unfold tailWord_1208479
  simp only [CollatzResearch.WordTrace]
  refine ⟨44076850188894449626620491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29384566792596299751080327 44076850188894449626620491)
  ·
    refine ⟨66115275283341674439930737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44076850188894449626620491 66115275283341674439930737)
    ·
      refine ⟨49586456462506255829948053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66115275283341674439930737 49586456462506255829948053)
      ·
        refine ⟨2324365146679980742028815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 49586456462506255829948053 2324365146679980742028815)
        ·
          refine ⟨3486547720019971113043223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2324365146679980742028815 3486547720019971113043223)
          ·
            refine ⟨5229821580029956669564835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3486547720019971113043223 5229821580029956669564835)
            ·
              refine ⟨7844732370044935004347253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5229821580029956669564835 7844732370044935004347253)
              ·
                refine ⟨735443659691712656657555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7844732370044935004347253 735443659691712656657555)
                ·
                  refine ⟨1103165489537568984986333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 735443659691712656657555 1103165489537568984986333)
                  ·
                    refine ⟨413687058576588369369875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1103165489537568984986333 413687058576588369369875)
                    ·
                      rfl

theorem cell22_1208479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 5, 1, 3].length) (baseStart_1208479 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1208479 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1208479 prefixEnd_1208479 := by exact prefixLift 1208479
  have htrace : WordTrace (prefixWord ++ tailWord_1208479) baseStart_1208479 baseEnd_1208479 := by
    simpa [prefixWord, tailWord_1208479, baseEnd_1208479] using wordTrace_append hprefix tailTrace_1208479
  have hstable : (prefixWord ++ tailWord_1208479).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1208479).length < 2 ^ (prefixWord ++ tailWord_1208479).sum := by decide
  have hdescent : baseEnd_1208479 < baseStart_1208479 := by decide
  rcases family_descends (prefixWord ++ tailWord_1208479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1208522 : List Nat := [3, 1, 2, 1, 3, 1, 4, 2, 1, 4]
def baseStart_1208522 : Nat := 118140960795 + 1208522 * 2 ^ 59
def prefixEnd_1208522 : Nat := 4983230072969 + 3 ^ 40 * 1208522 * 2
def baseEnd_1208522 : Nat := 413701778355350590544743

theorem tailTrace_1208522 : CollatzResearch.WordTrace tailWord_1208522 prefixEnd_1208522 413701778355350590544743 := by
  unfold tailWord_1208522
  simp only [CollatzResearch.WordTrace]
  refine ⟨11019604631934666992608955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29385612351825778646957213 11019604631934666992608955)
  ·
    refine ⟨16529406947902000488913433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11019604631934666992608955 16529406947902000488913433)
    ·
      refine ⟨12397055210926500366685075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16529406947902000488913433 12397055210926500366685075)
      ·
        refine ⟨18595582816389750550027613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12397055210926500366685075 18595582816389750550027613)
        ·
          refine ⟨6973343556146156456260355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18595582816389750550027613 6973343556146156456260355)
          ·
            refine ⟨10460015334219234684390533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6973343556146156456260355 10460015334219234684390533)
            ·
              refine ⟨1961252875166106503323225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10460015334219234684390533 1961252875166106503323225)
              ·
                refine ⟨1470939656374579877492419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1961252875166106503323225 1470939656374579877492419)
                ·
                  refine ⟨2206409484561869816238629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1470939656374579877492419 2206409484561869816238629)
                  ·
                    refine ⟨413701778355350590544743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2206409484561869816238629 413701778355350590544743)
                    ·
                      rfl

theorem cell22_1208522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 4, 2, 1, 4].length) (baseStart_1208522 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1208522 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1208522 prefixEnd_1208522 := by exact prefixLift 1208522
  have htrace : WordTrace (prefixWord ++ tailWord_1208522) baseStart_1208522 baseEnd_1208522 := by
    simpa [prefixWord, tailWord_1208522, baseEnd_1208522] using wordTrace_append hprefix tailTrace_1208522
  have hstable : (prefixWord ++ tailWord_1208522).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1208522).length < 2 ^ (prefixWord ++ tailWord_1208522).sum := by decide
  have hdescent : baseEnd_1208522 < baseStart_1208522 := by decide
  rcases family_descends (prefixWord ++ tailWord_1208522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1208537 : List Nat := [1, 2, 1, 2, 3, 1, 5, 3, 4]
def baseStart_1208537 : Nat := 118140960795 + 1208537 * 2 ^ 59
def prefixEnd_1208537 : Nat := 4983230072969 + 3 ^ 40 * 1208537 * 2
def baseEnd_1208537 : Nat := 137902304387298517139899

theorem tailTrace_1208537 : CollatzResearch.WordTrace tailWord_1208537 prefixEnd_1208537 137902304387298517139899 := by
  unfold tailWord_1208537
  simp only [CollatzResearch.WordTrace]
  refine ⟨44078965622684325532231865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29385977081789550354821243 44078965622684325532231865)
  ·
    refine ⟨33059224217013244149173899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44078965622684325532231865 33059224217013244149173899)
    ·
      refine ⟨49588836325519866223760849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33059224217013244149173899 49588836325519866223760849)
      ·
        refine ⟨37191627244139899667820637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49588836325519866223760849 37191627244139899667820637)
        ·
          refine ⟨13946860216552462375432739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37191627244139899667820637 13946860216552462375432739)
          ·
            refine ⟨20920290324828693563149109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13946860216552462375432739 20920290324828693563149109)
            ·
              refine ⟨1961277217952690021545229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20920290324828693563149109 1961277217952690021545229)
              ·
                refine ⟨735478956732258758079461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1961277217952690021545229 735478956732258758079461)
                ·
                  refine ⟨137902304387298517139899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 735478956732258758079461 137902304387298517139899)
                  ·
                    rfl

theorem cell22_1208537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 5, 3, 4].length) (baseStart_1208537 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1208537 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1208537 prefixEnd_1208537 := by exact prefixLift 1208537
  have htrace : WordTrace (prefixWord ++ tailWord_1208537) baseStart_1208537 baseEnd_1208537 := by
    simpa [prefixWord, tailWord_1208537, baseEnd_1208537] using wordTrace_append hprefix tailTrace_1208537
  have hstable : (prefixWord ++ tailWord_1208537).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1208537).length < 2 ^ (prefixWord ++ tailWord_1208537).sum := by decide
  have hdescent : baseEnd_1208537 < baseStart_1208537 := by decide
  rcases family_descends (prefixWord ++ tailWord_1208537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1208552 : List Nat := [2, 1, 4, 1, 2, 2, 2, 1, 4, 3]
def baseStart_1208552 : Nat := 118140960795 + 1208552 * 2 ^ 59
def prefixEnd_1208552 : Nat := 4983230072969 + 3 ^ 40 * 1208552 * 2
def baseEnd_1208552 : Nat := 413712047968440512294651

theorem tailTrace_1208552 : CollatzResearch.WordTrace tailWord_1208552 prefixEnd_1208552 413712047968440512294651 := by
  unfold tailWord_1208552
  simp only [CollatzResearch.WordTrace]
  refine ⟨22039756358814991547013955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29386341811753322062685273 22039756358814991547013955)
  ·
    refine ⟨33059634538222487320520933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22039756358814991547013955 33059634538222487320520933)
    ·
      refine ⟨6198681475916716372597675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33059634538222487320520933 6198681475916716372597675)
      ·
        refine ⟨9298022213875074558896513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6198681475916716372597675 9298022213875074558896513)
        ·
          refine ⟨6973516660406305919172385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9298022213875074558896513 6973516660406305919172385)
          ·
            refine ⟨5230137495304729439379289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6973516660406305919172385 5230137495304729439379289)
            ·
              refine ⟨3922603121478547079534467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5230137495304729439379289 3922603121478547079534467)
              ·
                refine ⟨5883904682217820619301701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3922603121478547079534467 5883904682217820619301701)
                ·
                  refine ⟨1103232127915841366119069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5883904682217820619301701 1103232127915841366119069)
                  ·
                    refine ⟨413712047968440512294651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1103232127915841366119069 413712047968440512294651)
                    ·
                      rfl

theorem cell22_1208552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 2, 1, 4, 3].length) (baseStart_1208552 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1208552 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1208552 prefixEnd_1208552 := by exact prefixLift 1208552
  have htrace : WordTrace (prefixWord ++ tailWord_1208552) baseStart_1208552 baseEnd_1208552 := by
    simpa [prefixWord, tailWord_1208552, baseEnd_1208552] using wordTrace_append hprefix tailTrace_1208552
  have hstable : (prefixWord ++ tailWord_1208552).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1208552).length < 2 ^ (prefixWord ++ tailWord_1208552).sum := by decide
  have hdescent : baseEnd_1208552 < baseStart_1208552 := by decide
  rcases family_descends (prefixWord ++ tailWord_1208552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1208554 : List Nat := [3, 1, 3, 1, 1, 2, 5, 2, 4]
def baseStart_1208554 : Nat := 118140960795 + 1208554 * 2 ^ 59
def prefixEnd_1208554 : Nat := 4983230072969 + 3 ^ 40 * 1208554 * 2
def baseEnd_1208554 : Nat := 137904244203104391248215

theorem tailTrace_1208554 : CollatzResearch.WordTrace tailWord_1208554 prefixEnd_1208554 137904244203104391248215 := by
  unfold tailWord_1208554
  simp only [CollatzResearch.WordTrace]
  refine ⟨11019896415905684358900179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29386390442415158290400477 11019896415905684358900179)
  ·
    refine ⟨16529844623858526538350269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11019896415905684358900179 16529844623858526538350269)
    ·
      refine ⟨6198691733946947451881351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16529844623858526538350269 6198691733946947451881351)
      ·
        refine ⟨9298037600920421177822027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6198691733946947451881351 9298037600920421177822027)
        ·
          refine ⟨13947056401380631766733041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9298037600920421177822027 13947056401380631766733041)
          ·
            refine ⟨10460292301035473825049781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13947056401380631766733041 10460292301035473825049781)
            ·
              refine ⟨980652403222075671098417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10460292301035473825049781 980652403222075671098417)
              ·
                refine ⟨735489302416556753323813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 980652403222075671098417 735489302416556753323813)
                ·
                  refine ⟨137904244203104391248215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 735489302416556753323813 137904244203104391248215)
                  ·
                    rfl

theorem cell22_1208554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 5, 2, 4].length) (baseStart_1208554 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1208554 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1208554 prefixEnd_1208554 := by exact prefixLift 1208554
  have htrace : WordTrace (prefixWord ++ tailWord_1208554) baseStart_1208554 baseEnd_1208554 := by
    simpa [prefixWord, tailWord_1208554, baseEnd_1208554] using wordTrace_append hprefix tailTrace_1208554
  have hstable : (prefixWord ++ tailWord_1208554).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1208554).length < 2 ^ (prefixWord ++ tailWord_1208554).sum := by decide
  have hdescent : baseEnd_1208554 < baseStart_1208554 := by decide
  rcases family_descends (prefixWord ++ tailWord_1208554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1208661 : List Nat := [1, 3, 2, 2, 5, 1, 1, 2, 5]
def baseStart_1208661 : Nat := 118140960795 + 1208661 * 2 ^ 59
def prefixEnd_1208661 : Nat := 4983230072969 + 3 ^ 40 * 1208661 * 2
def baseEnd_1208661 : Nat := 137916453632000187106439

theorem tailTrace_1208661 : CollatzResearch.WordTrace tailWord_1208661 prefixEnd_1208661 137916453632000187106439 := by
  unfold tailWord_1208661
  simp only [CollatzResearch.WordTrace]
  refine ⟨44083488274235094709745837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29388992182823396473163891 44083488274235094709745837)
  ·
    refine ⟨16531308102838160516154689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44083488274235094709745837 16531308102838160516154689)
    ·
      refine ⟨12398481077128620387116017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16531308102838160516154689 12398481077128620387116017)
      ·
        refine ⟨9298860807846465290337013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12398481077128620387116017 9298860807846465290337013)
        ·
          refine ⟨871768200735606120969095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9298860807846465290337013 871768200735606120969095)
          ·
            refine ⟨1307652301103409181453643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 871768200735606120969095 1307652301103409181453643)
            ·
              refine ⟨1961478451655113772180465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1307652301103409181453643 1961478451655113772180465)
              ·
                refine ⟨1471108838741335329135349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1961478451655113772180465 1471108838741335329135349)
                ·
                  refine ⟨137916453632000187106439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1471108838741335329135349 137916453632000187106439)
                  ·
                    rfl

theorem cell22_1208661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 1, 2, 5].length) (baseStart_1208661 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1208661 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1208661 prefixEnd_1208661 := by exact prefixLift 1208661
  have htrace : WordTrace (prefixWord ++ tailWord_1208661) baseStart_1208661 baseEnd_1208661 := by
    simpa [prefixWord, tailWord_1208661, baseEnd_1208661] using wordTrace_append hprefix tailTrace_1208661
  have hstable : (prefixWord ++ tailWord_1208661).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1208661).length < 2 ^ (prefixWord ++ tailWord_1208661).sum := by decide
  have hdescent : baseEnd_1208661 < baseStart_1208661 := by decide
  rcases family_descends (prefixWord ++ tailWord_1208661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1208734 : List Nat := [4, 3, 1, 2, 1, 1, 1, 9]
def baseStart_1208734 : Nat := 118140960795 + 1208734 * 2 ^ 59
def prefixEnd_1208734 : Nat := 4983230072969 + 3 ^ 40 * 1208734 * 2
def baseEnd_1208734 : Nat := 45974927809761411582677

theorem tailTrace_1208734 : CollatzResearch.WordTrace tailWord_1208734 prefixEnd_1208734 45974927809761411582677 := by
  unfold tailWord_1208734
  simp only [CollatzResearch.WordTrace]
  refine ⟨5510768850371328522144157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29390767201980418784768837 5510768850371328522144157)
  ·
    refine ⟨2066538318889248195804059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5510768850371328522144157 2066538318889248195804059)
    ·
      refine ⟨3099807478333872293706089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2066538318889248195804059 3099807478333872293706089)
      ·
        refine ⟨2324855608750404220279567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3099807478333872293706089 2324855608750404220279567)
        ·
          refine ⟨3487283413125606330419351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2324855608750404220279567 3487283413125606330419351)
          ·
            refine ⟨5230925119688409495629027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3487283413125606330419351 5230925119688409495629027)
            ·
              refine ⟨7846387679532614243443541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5230925119688409495629027 7846387679532614243443541)
              ·
                refine ⟨45974927809761411582677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 7846387679532614243443541 45974927809761411582677)
                ·
                  rfl

theorem cell22_1208734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 9].length) (baseStart_1208734 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1208734 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1208734 prefixEnd_1208734 := by exact prefixLift 1208734
  have htrace : WordTrace (prefixWord ++ tailWord_1208734) baseStart_1208734 baseEnd_1208734 := by
    simpa [prefixWord, tailWord_1208734, baseEnd_1208734] using wordTrace_append hprefix tailTrace_1208734
  have hstable : (prefixWord ++ tailWord_1208734).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1208734).length < 2 ^ (prefixWord ++ tailWord_1208734).sum := by decide
  have hdescent : baseEnd_1208734 < baseStart_1208734 := by decide
  rcases family_descends (prefixWord ++ tailWord_1208734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1208856 : List Nat := [2, 1, 2, 3, 3, 3, 1, 1, 1, 5]
def baseStart_1208856 : Nat := 118140960795 + 1208856 * 2 ^ 59
def prefixEnd_1208856 : Nat := 4983230072969 + 3 ^ 40 * 1208856 * 2
def baseEnd_1208856 : Nat := 413816113381085052693719

theorem tailTrace_1208856 : CollatzResearch.WordTrace tailWord_1208856 prefixEnd_1208856 413816113381085052693719 := by
  unfold tailWord_1208856
  simp only [CollatzResearch.WordTrace]
  refine ⟨22045300254264321506547211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29393733672352428675396281 22045300254264321506547211)
  ·
    refine ⟨33067950381396482259820817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22045300254264321506547211 33067950381396482259820817)
    ·
      refine ⟨24800962786047361694865613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33067950381396482259820817 24800962786047361694865613)
      ·
        refine ⟨9300361044767760635574605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24800962786047361694865613 9300361044767760635574605)
        ·
          refine ⟨3487635391787910238340477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9300361044767760635574605 3487635391787910238340477)
          ·
            refine ⟨1307863271920466339377679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3487635391787910238340477 1307863271920466339377679)
            ·
              refine ⟨1961794907880699509066519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1307863271920466339377679 1961794907880699509066519)
              ·
                refine ⟨2942692361821049263599779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1961794907880699509066519 2942692361821049263599779)
                ·
                  refine ⟨4414038542731573895399669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2942692361821049263599779 4414038542731573895399669)
                  ·
                    refine ⟨413816113381085052693719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4414038542731573895399669 413816113381085052693719)
                    ·
                      rfl

theorem cell22_1208856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 1, 1, 1, 5].length) (baseStart_1208856 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1208856 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1208856 prefixEnd_1208856 := by exact prefixLift 1208856
  have htrace : WordTrace (prefixWord ++ tailWord_1208856) baseStart_1208856 baseEnd_1208856 := by
    simpa [prefixWord, tailWord_1208856, baseEnd_1208856] using wordTrace_append hprefix tailTrace_1208856
  have hstable : (prefixWord ++ tailWord_1208856).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1208856).length < 2 ^ (prefixWord ++ tailWord_1208856).sum := by decide
  have hdescent : baseEnd_1208856 < baseStart_1208856 := by decide
  rcases family_descends (prefixWord ++ tailWord_1208856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1208869 : List Nat := [1, 3, 1, 2, 2, 1, 6, 6]
def baseStart_1208869 : Nat := 118140960795 + 1208869 * 2 ^ 59
def prefixEnd_1208869 : Nat := 4983230072969 + 3 ^ 40 * 1208869 * 2
def baseEnd_1208869 : Nat := 45980062616306372457631

theorem tailTrace_1208869 : CollatzResearch.WordTrace tailWord_1208869 prefixEnd_1208869 45980062616306372457631 := by
  unfold tailWord_1208869
  simp only [CollatzResearch.WordTrace]
  refine ⟨44091074657481546233317661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29394049771654364155545107 44091074657481546233317661)
  ·
    refine ⟨16534152996555579837494123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44091074657481546233317661 16534152996555579837494123)
    ·
      refine ⟨24801229494833369756241185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16534152996555579837494123 24801229494833369756241185)
      ·
        refine ⟨18600922121125027317180889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24801229494833369756241185 18600922121125027317180889)
        ·
          refine ⟨13950691590843770487885667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18600922121125027317180889 13950691590843770487885667)
          ·
            refine ⟨20926037386265655731828501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13950691590843770487885667 20926037386265655731828501)
            ·
              refine ⟨980908002481202612429461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 20926037386265655731828501 980908002481202612429461)
              ·
                refine ⟨45980062616306372457631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 980908002481202612429461 45980062616306372457631)
                ·
                  rfl

theorem cell22_1208869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 6, 6].length) (baseStart_1208869 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1208869 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1208869 prefixEnd_1208869 := by exact prefixLift 1208869
  have htrace : WordTrace (prefixWord ++ tailWord_1208869) baseStart_1208869 baseEnd_1208869 := by
    simpa [prefixWord, tailWord_1208869, baseEnd_1208869] using wordTrace_append hprefix tailTrace_1208869
  have hstable : (prefixWord ++ tailWord_1208869).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1208869).length < 2 ^ (prefixWord ++ tailWord_1208869).sum := by decide
  have hdescent : baseEnd_1208869 < baseStart_1208869 := by decide
  rcases family_descends (prefixWord ++ tailWord_1208869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1208886 : List Nat := [5, 1, 2, 1, 2, 3, 8]
def baseStart_1208886 : Nat := 118140960795 + 1208886 * 2 ^ 59
def prefixEnd_1208886 : Nat := 4983230072969 + 3 ^ 40 * 1208886 * 2
def baseEnd_1208886 : Nat := 15326903073858332386801

theorem tailTrace_1208886 : CollatzResearch.WordTrace tailWord_1208886 prefixEnd_1208886 15326903073858332386801 := by
  unfold tailWord_1208886
  simp only [CollatzResearch.WordTrace]
  refine ⟨2755730918651247383542907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 29394463132279972091124341 2755730918651247383542907)
  ·
    refine ⟨4133596377976871075314361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2755730918651247383542907 4133596377976871075314361)
    ·
      refine ⟨3100197283482653306485771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4133596377976871075314361 3100197283482653306485771)
      ·
        refine ⟨4650295925223979959728657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3100197283482653306485771 4650295925223979959728657)
        ·
          refine ⟨3487721943917984969796493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4650295925223979959728657 3487721943917984969796493)
          ·
            refine ⟨1307895728969244363673685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3487721943917984969796493 1307895728969244363673685)
            ·
              refine ⟨15326903073858332386801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1307895728969244363673685 15326903073858332386801)
              ·
                rfl

theorem cell22_1208886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 8].length) (baseStart_1208886 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1208886 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1208886 prefixEnd_1208886 := by exact prefixLift 1208886
  have htrace : WordTrace (prefixWord ++ tailWord_1208886) baseStart_1208886 baseEnd_1208886 := by
    simpa [prefixWord, tailWord_1208886, baseEnd_1208886] using wordTrace_append hprefix tailTrace_1208886
  have hstable : (prefixWord ++ tailWord_1208886).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1208886).length < 2 ^ (prefixWord ++ tailWord_1208886).sum := by decide
  have hdescent : baseEnd_1208886 < baseStart_1208886 := by decide
  rcases family_descends (prefixWord ++ tailWord_1208886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1208901 : List Nat := [1, 3, 1, 1, 1, 5, 3, 1, 3, 3]
def baseStart_1208901 : Nat := 118140960795 + 1208901 * 2 ^ 59
def prefixEnd_1208901 : Nat := 4983230072969 + 3 ^ 40 * 1208901 * 2
def baseEnd_1208901 : Nat := 413831517800719935318581

theorem tailTrace_1208901 : CollatzResearch.WordTrace tailWord_1208901 prefixEnd_1208901 413831517800719935318581 := by
  unfold tailWord_1208901
  simp only [CollatzResearch.WordTrace]
  refine ⟨44092241793365615698482557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29394827862243743798988371 44092241793365615698482557)
  ·
    refine ⟨16534590672512105886930959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44092241793365615698482557 16534590672512105886930959)
    ·
      refine ⟨24801886008768158830396439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16534590672512105886930959 24801886008768158830396439)
      ·
        refine ⟨37202829013152238245594659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24801886008768158830396439 37202829013152238245594659)
        ·
          refine ⟨55804243519728357368391989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37202829013152238245594659 55804243519728357368391989)
          ·
            refine ⟨5231647829974533503286749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 55804243519728357368391989 5231647829974533503286749)
            ·
              refine ⟨1961867936240450063732531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5231647829974533503286749 1961867936240450063732531)
              ·
                refine ⟨2942801904360675095598797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1961867936240450063732531 2942801904360675095598797)
                ·
                  refine ⟨1103550714135253160849549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2942801904360675095598797 1103550714135253160849549)
                  ·
                    refine ⟨413831517800719935318581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1103550714135253160849549 413831517800719935318581)
                    ·
                      rfl

theorem cell22_1208901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 3, 1, 3, 3].length) (baseStart_1208901 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1208901 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1208901 prefixEnd_1208901 := by exact prefixLift 1208901
  have htrace : WordTrace (prefixWord ++ tailWord_1208901) baseStart_1208901 baseEnd_1208901 := by
    simpa [prefixWord, tailWord_1208901, baseEnd_1208901] using wordTrace_append hprefix tailTrace_1208901
  have hstable : (prefixWord ++ tailWord_1208901).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1208901).length < 2 ^ (prefixWord ++ tailWord_1208901).sum := by decide
  have hdescent : baseEnd_1208901 < baseStart_1208901 := by decide
  rcases family_descends (prefixWord ++ tailWord_1208901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1209038 : List Nat := [4, 1, 1, 1, 3, 4, 2, 6]
def baseStart_1209038 : Nat := 118140960795 + 1209038 * 2 ^ 59
def prefixEnd_1209038 : Nat := 4983230072969 + 3 ^ 40 * 1209038 * 2
def baseEnd_1209038 : Nat := 45986490633388582738129

theorem tailTrace_1209038 : CollatzResearch.WordTrace tailWord_1209038 prefixEnd_1209038 45986490633388582738129 := by
  unfold tailWord_1209038
  simp only [CollatzResearch.WordTrace]
  refine ⟨5512154824233661012027471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29398159062579525397479845 5512154824233661012027471)
  ·
    refine ⟨8268232236350491518041207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5512154824233661012027471 8268232236350491518041207)
    ·
      refine ⟨12402348354525737277061811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8268232236350491518041207 12402348354525737277061811)
      ·
        refine ⟨18603522531788605915592717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12402348354525737277061811 18603522531788605915592717)
        ·
          refine ⟨6976320949420727218347269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18603522531788605915592717 6976320949420727218347269)
          ·
            refine ⟨1308060178016386353440113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6976320949420727218347269 1308060178016386353440113)
            ·
              refine ⟨981045133512289765080085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1308060178016386353440113 981045133512289765080085)
              ·
                refine ⟨45986490633388582738129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 981045133512289765080085 45986490633388582738129)
                ·
                  rfl

theorem cell22_1209038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 2, 6].length) (baseStart_1209038 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1209038 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1209038 prefixEnd_1209038 := by exact prefixLift 1209038
  have htrace : WordTrace (prefixWord ++ tailWord_1209038) baseStart_1209038 baseEnd_1209038 := by
    simpa [prefixWord, tailWord_1209038, baseEnd_1209038] using wordTrace_append hprefix tailTrace_1209038
  have hstable : (prefixWord ++ tailWord_1209038).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1209038).length < 2 ^ (prefixWord ++ tailWord_1209038).sum := by decide
  have hdescent : baseEnd_1209038 < baseStart_1209038 := by decide
  rcases family_descends (prefixWord ++ tailWord_1209038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1209049 : List Nat := [1, 2, 1, 2, 3, 2, 1, 1, 9]
def baseStart_1209049 : Nat := 118140960795 + 1209049 * 2 ^ 59
def prefixEnd_1209049 : Nat := 4983230072969 + 3 ^ 40 * 1209049 * 2
def baseEnd_1209049 : Nat := 137960727075098960872709

theorem tailTrace_1209049 : CollatzResearch.WordTrace tailWord_1209049 prefixEnd_1209049 137960727075098960872709 := by
  unfold tailWord_1209049
  simp only [CollatzResearch.WordTrace]
  refine ⟨44097639796829436974870201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29398426531219624649913467 44097639796829436974870201)
  ·
    refine ⟨33073229847622077731152651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44097639796829436974870201 33073229847622077731152651)
    ·
      refine ⟨49609844771433116596728977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33073229847622077731152651 49609844771433116596728977)
      ·
        refine ⟨37207383578574837447546733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49609844771433116596728977 37207383578574837447546733)
        ·
          refine ⟨13952768841965564042830025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37207383578574837447546733 13952768841965564042830025)
          ·
            refine ⟨10464576631474173032122519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13952768841965564042830025 10464576631474173032122519)
            ·
              refine ⟨15696864947211259548183779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10464576631474173032122519 15696864947211259548183779)
              ·
                refine ⟨23545297420816889322275669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15696864947211259548183779 23545297420816889322275669)
                ·
                  refine ⟨137960727075098960872709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 23545297420816889322275669 137960727075098960872709)
                  ·
                    rfl

theorem cell22_1209049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 1, 9].length) (baseStart_1209049 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1209049 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1209049 prefixEnd_1209049 := by exact prefixLift 1209049
  have htrace : WordTrace (prefixWord ++ tailWord_1209049) baseStart_1209049 baseEnd_1209049 := by
    simpa [prefixWord, tailWord_1209049, baseEnd_1209049] using wordTrace_append hprefix tailTrace_1209049
  have hstable : (prefixWord ++ tailWord_1209049).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1209049).length < 2 ^ (prefixWord ++ tailWord_1209049).sum := by decide
  have hdescent : baseEnd_1209049 < baseStart_1209049 := by decide
  rcases family_descends (prefixWord ++ tailWord_1209049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1209066 : List Nat := [3, 1, 3, 1, 1, 1, 1, 6, 5]
def baseStart_1209066 : Nat := 118140960795 + 1209066 * 2 ^ 59
def prefixEnd_1209066 : Nat := 4983230072969 + 3 ^ 40 * 1209066 * 2
def baseEnd_1209066 : Nat := 137962666890904834981025

theorem tailTrace_1209066 : CollatzResearch.WordTrace tailWord_1209066 prefixEnd_1209066 137962666890904834981025 := by
  unfold tailWord_1209066
  simp only [CollatzResearch.WordTrace]
  refine ⟨11024564959441962219559763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29398839891845232585492701 11024564959441962219559763)
  ·
    refine ⟨16536847439162943329339645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11024564959441962219559763 16536847439162943329339645)
    ·
      refine ⟨6201317789686103748502367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16536847439162943329339645 6201317789686103748502367)
      ·
        refine ⟨9301976684529155622753551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6201317789686103748502367 9301976684529155622753551)
        ·
          refine ⟨13952965026793733434130327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9301976684529155622753551 13952965026793733434130327)
          ·
            refine ⟨20929447540190600151195491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13952965026793733434130327 20929447540190600151195491)
            ·
              refine ⟨31394171310285900226793237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20929447540190600151195491 31394171310285900226793237)
              ·
                refine ⟨1471601780169651573130933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 31394171310285900226793237 1471601780169651573130933)
                ·
                  refine ⟨137962666890904834981025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1471601780169651573130933 137962666890904834981025)
                  ·
                    rfl

theorem cell22_1209066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 6, 5].length) (baseStart_1209066 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1209066 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1209066 prefixEnd_1209066 := by exact prefixLift 1209066
  have htrace : WordTrace (prefixWord ++ tailWord_1209066) baseStart_1209066 baseEnd_1209066 := by
    simpa [prefixWord, tailWord_1209066, baseEnd_1209066] using wordTrace_append hprefix tailTrace_1209066
  have hstable : (prefixWord ++ tailWord_1209066).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1209066).length < 2 ^ (prefixWord ++ tailWord_1209066).sum := by decide
  have hdescent : baseEnd_1209066 < baseStart_1209066 := by decide
  rcases family_descends (prefixWord ++ tailWord_1209066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1209070 : List Nat := [4, 1, 2, 1, 1, 5, 1, 1, 3, 3]
def baseStart_1209070 : Nat := 118140960795 + 1209070 * 2 ^ 59
def prefixEnd_1209070 : Nat := 4983230072969 + 3 ^ 40 * 1209070 * 2
def baseEnd_1209070 : Nat := 413889369954459827843063

theorem tailTrace_1209070 : CollatzResearch.WordTrace tailWord_1209070 prefixEnd_1209070 413889369954459827843063 := by
  unfold tailWord_1209070
  simp only [CollatzResearch.WordTrace]
  refine ⟨5512300716219169695173083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29398937153168905040923109 5512300716219169695173083)
  ·
    refine ⟨8268451074328754542759625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5512300716219169695173083 8268451074328754542759625)
    ·
      refine ⟨6201338305746565907069719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8268451074328754542759625 6201338305746565907069719)
      ·
        refine ⟨9302007458619848860604579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6201338305746565907069719 9302007458619848860604579)
        ·
          refine ⟨13953011187929773290906869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9302007458619848860604579 13953011187929773290906869)
          ·
            refine ⟨1308094798868416246022519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13953011187929773290906869 1308094798868416246022519)
            ·
              refine ⟨1962142198302624369033779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1308094798868416246022519 1962142198302624369033779)
              ·
                refine ⟨2943213297453936553550669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1962142198302624369033779 2943213297453936553550669)
                ·
                  refine ⟨1103704986545226207581501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2943213297453936553550669 1103704986545226207581501)
                  ·
                    refine ⟨413889369954459827843063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1103704986545226207581501 413889369954459827843063)
                    ·
                      rfl

theorem cell22_1209070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 1, 1, 3, 3].length) (baseStart_1209070 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1209070 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1209070 prefixEnd_1209070 := by exact prefixLift 1209070
  have htrace : WordTrace (prefixWord ++ tailWord_1209070) baseStart_1209070 baseEnd_1209070 := by
    simpa [prefixWord, tailWord_1209070, baseEnd_1209070] using wordTrace_append hprefix tailTrace_1209070
  have hstable : (prefixWord ++ tailWord_1209070).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1209070).length < 2 ^ (prefixWord ++ tailWord_1209070).sum := by decide
  have hdescent : baseEnd_1209070 < baseStart_1209070 := by decide
  rcases family_descends (prefixWord ++ tailWord_1209070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1209076 : List Nat := [2, 6, 1, 1, 2, 2, 2, 1, 2, 3]
def baseStart_1209076 : Nat := 118140960795 + 1209076 * 2 ^ 59
def prefixEnd_1209076 : Nat := 4983230072969 + 3 ^ 40 * 1209076 * 2
def baseEnd_1209076 : Nat := 413891423877077812193045

theorem tailTrace_1209076 : CollatzResearch.WordTrace tailWord_1209076 prefixEnd_1209076 413891423877077812193045 := by
  unfold tailWord_1209076
  simp only [CollatzResearch.WordTrace]
  refine ⟨22049312283865810293051541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29399083045154413724068721 22049312283865810293051541)
  ·
    refine ⟨1033561513306209857486791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 22049312283865810293051541 1033561513306209857486791)
    ·
      refine ⟨1550342269959314786230187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1033561513306209857486791 1550342269959314786230187)
      ·
        refine ⟨2325513404938972179345281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1550342269959314786230187 2325513404938972179345281)
        ·
          refine ⟨1744135053704229134508961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2325513404938972179345281 1744135053704229134508961)
          ·
            refine ⟨1308101290278171850881721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1744135053704229134508961 1308101290278171850881721)
            ·
              refine ⟨981075967708628888161291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1308101290278171850881721 981075967708628888161291)
              ·
                refine ⟨1471613951562943332241937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 981075967708628888161291 1471613951562943332241937)
                ·
                  refine ⟨1103710463672207499181453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1471613951562943332241937 1103710463672207499181453)
                  ·
                    refine ⟨413891423877077812193045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1103710463672207499181453 413891423877077812193045)
                    ·
                      rfl

theorem cell22_1209076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 2, 1, 2, 3].length) (baseStart_1209076 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1209076 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1209076 prefixEnd_1209076 := by exact prefixLift 1209076
  have htrace : WordTrace (prefixWord ++ tailWord_1209076) baseStart_1209076 baseEnd_1209076 := by
    simpa [prefixWord, tailWord_1209076, baseEnd_1209076] using wordTrace_append hprefix tailTrace_1209076
  have hstable : (prefixWord ++ tailWord_1209076).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1209076).length < 2 ^ (prefixWord ++ tailWord_1209076).sum := by decide
  have hdescent : baseEnd_1209076 < baseStart_1209076 := by decide
  rcases family_descends (prefixWord ++ tailWord_1209076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1209079 : List Nat := [1, 1, 3, 1, 1, 1, 3, 1, 2, 8]
def baseStart_1209079 : Nat := 118140960795 + 1209079 * 2 ^ 59
def prefixEnd_1209079 : Nat := 4983230072969 + 3 ^ 40 * 1209079 * 2
def baseEnd_1209079 : Nat := 413892450838386804368035

theorem tailTrace_1209079 : CollatzResearch.WordTrace tailWord_1209079 prefixEnd_1209079 413892450838386804368035 := by
  unfold tailWord_1209079
  simp only [CollatzResearch.WordTrace]
  refine ⟨44098733986720752098462291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29399155991147168065641527 44098733986720752098462291)
  ·
    refine ⟨66148100980081128147693437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44098733986720752098462291 66148100980081128147693437)
    ·
      refine ⟨24805537867530423055385039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66148100980081128147693437 24805537867530423055385039)
      ·
        refine ⟨37208306801295634583077559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24805537867530423055385039 37208306801295634583077559)
        ·
          refine ⟨55812460201943451874616339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37208306801295634583077559 55812460201943451874616339)
          ·
            refine ⟨83718690302915177811924509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55812460201943451874616339 83718690302915177811924509)
            ·
              refine ⟨31394508863593191679471691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 83718690302915177811924509 31394508863593191679471691)
              ·
                refine ⟨47091763295389787519207537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31394508863593191679471691 47091763295389787519207537)
                ·
                  refine ⟨35318822471542340639405653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47091763295389787519207537 35318822471542340639405653)
                  ·
                    refine ⟨413892450838386804368035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 35318822471542340639405653 413892450838386804368035)
                    ·
                      rfl

theorem cell22_1209079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 1, 2, 8].length) (baseStart_1209079 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1209079 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1209079 prefixEnd_1209079 := by exact prefixLift 1209079
  have htrace : WordTrace (prefixWord ++ tailWord_1209079) baseStart_1209079 baseEnd_1209079 := by
    simpa [prefixWord, tailWord_1209079, baseEnd_1209079] using wordTrace_append hprefix tailTrace_1209079
  have hstable : (prefixWord ++ tailWord_1209079).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1209079).length < 2 ^ (prefixWord ++ tailWord_1209079).sum := by decide
  have hdescent : baseEnd_1209079 < baseStart_1209079 := by decide
  rcases family_descends (prefixWord ++ tailWord_1209079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1209143 : List Nat := [1, 1, 3, 1, 2, 1, 3, 5, 2, 3]
def baseStart_1209143 : Nat := 118140960795 + 1209143 * 2 ^ 59
def prefixEnd_1209143 : Nat := 4983230072969 + 3 ^ 40 * 1209143 * 2
def baseEnd_1209143 : Nat := 413914359346311970767839

theorem tailTrace_1209143 : CollatzResearch.WordTrace tailWord_1209143 prefixEnd_1209143 413914359346311970767839 := by
  unfold tailWord_1209143
  simp only [CollatzResearch.WordTrace]
  refine ⟨44101068258488891028792083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29400712172325927352528055 44101068258488891028792083)
  ·
    refine ⟨66151602387733336543188125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44101068258488891028792083 66151602387733336543188125)
    ·
      refine ⟨24806850895400001203695547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66151602387733336543188125 24806850895400001203695547)
      ·
        refine ⟨37210276343100001805543321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24806850895400001203695547 37210276343100001805543321)
        ·
          refine ⟨27907707257325001354157491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37210276343100001805543321 27907707257325001354157491)
          ·
            refine ⟨41861560885987502031236237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27907707257325001354157491 41861560885987502031236237)
            ·
              refine ⟨15698085332245313261713589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41861560885987502031236237 15698085332245313261713589)
              ·
                refine ⟨1471695499897998118285649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15698085332245313261713589 1471695499897998118285649)
                ·
                  refine ⟨1103771624923498588714237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1471695499897998118285649 1103771624923498588714237)
                  ·
                    refine ⟨413914359346311970767839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1103771624923498588714237 413914359346311970767839)
                    ·
                      rfl

theorem cell22_1209143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 5, 2, 3].length) (baseStart_1209143 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1209143 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1209143 prefixEnd_1209143 := by exact prefixLift 1209143
  have htrace : WordTrace (prefixWord ++ tailWord_1209143) baseStart_1209143 baseEnd_1209143 := by
    simpa [prefixWord, tailWord_1209143, baseEnd_1209143] using wordTrace_append hprefix tailTrace_1209143
  have hstable : (prefixWord ++ tailWord_1209143).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1209143).length < 2 ^ (prefixWord ++ tailWord_1209143).sum := by decide
  have hdescent : baseEnd_1209143 < baseStart_1209143 := by decide
  rcases family_descends (prefixWord ++ tailWord_1209143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1209205 : List Nat := [1, 3, 4, 1, 1, 2, 2, 2, 3, 3]
def baseStart_1209205 : Nat := 118140960795 + 1209205 * 2 ^ 59
def prefixEnd_1209205 : Nat := 4983230072969 + 3 ^ 40 * 1209205 * 2
def baseEnd_1209205 : Nat := 413935583213364475717649

theorem tailTrace_1209205 : CollatzResearch.WordTrace tailWord_1209205 prefixEnd_1209205 413935583213364475717649 := by
  unfold tailWord_1209205
  simp only [CollatzResearch.WordTrace]
  refine ⟨44103329584264275617549069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29402219722842850411699379 44103329584264275617549069)
  ·
    refine ⟨16538748594099103356580901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44103329584264275617549069 16538748594099103356580901)
    ·
      refine ⟨3101015361393581879358919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16538748594099103356580901 3101015361393581879358919)
      ·
        refine ⟨4651523042090372819038379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3101015361393581879358919 4651523042090372819038379)
        ·
          refine ⟨6977284563135559228557569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4651523042090372819038379 6977284563135559228557569)
          ·
            refine ⟨5232963422351669421418177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6977284563135559228557569 5232963422351669421418177)
            ·
              refine ⟨3924722566763752066063633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5232963422351669421418177 3924722566763752066063633)
              ·
                refine ⟨2943541925072814049547725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3924722566763752066063633 2943541925072814049547725)
                ·
                  refine ⟨1103828221902305268580397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2943541925072814049547725 1103828221902305268580397)
                  ·
                    refine ⟨413935583213364475717649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1103828221902305268580397 413935583213364475717649)
                    ·
                      rfl

theorem cell22_1209205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 2, 2, 3, 3].length) (baseStart_1209205 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1209205 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1209205 prefixEnd_1209205 := by exact prefixLift 1209205
  have htrace : WordTrace (prefixWord ++ tailWord_1209205) baseStart_1209205 baseEnd_1209205 := by
    simpa [prefixWord, tailWord_1209205, baseEnd_1209205] using wordTrace_append hprefix tailTrace_1209205
  have hstable : (prefixWord ++ tailWord_1209205).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1209205).length < 2 ^ (prefixWord ++ tailWord_1209205).sum := by decide
  have hdescent : baseEnd_1209205 < baseStart_1209205 := by decide
  rcases family_descends (prefixWord ++ tailWord_1209205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1209216 : List Nat := [2, 1, 1, 2, 1, 2, 2, 2, 4, 5]
def baseStart_1209216 : Nat := 118140960795 + 1209216 * 2 ^ 59
def prefixEnd_1209216 : Nat := 4983230072969 + 3 ^ 40 * 1209216 * 2
def baseEnd_1209216 : Nat := 413939348738164113692615

theorem tailTrace_1209216 : CollatzResearch.WordTrace tailWord_1209216 prefixEnd_1209216 413939348738164113692615 := by
  unfold tailWord_1209216
  simp only [CollatzResearch.WordTrace]
  refine ⟨22051865393612212248099751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29402487191482949664133001 22051865393612212248099751)
  ·
    refine ⟨33077798090418318372149627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22051865393612212248099751 33077798090418318372149627)
    ·
      refine ⟨49616697135627477558224441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33077798090418318372149627 49616697135627477558224441)
      ·
        refine ⟨37212522851720608168668331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49616697135627477558224441 37212522851720608168668331)
        ·
          refine ⟨55818784277580912253002497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37212522851720608168668331 55818784277580912253002497)
          ·
            refine ⟨41864088208185684189751873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55818784277580912253002497 41864088208185684189751873)
            ·
              refine ⟨31398066156139263142313905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41864088208185684189751873 31398066156139263142313905)
              ·
                refine ⟨23548549617104447356735429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31398066156139263142313905 23548549617104447356735429)
                ·
                  refine ⟨4415353053207083879387893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23548549617104447356735429 4415353053207083879387893)
                  ·
                    refine ⟨413939348738164113692615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4415353053207083879387893 413939348738164113692615)
                    ·
                      rfl

theorem cell22_1209216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 2, 4, 5].length) (baseStart_1209216 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1209216 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1209216 prefixEnd_1209216 := by exact prefixLift 1209216
  have htrace : WordTrace (prefixWord ++ tailWord_1209216) baseStart_1209216 baseEnd_1209216 := by
    simpa [prefixWord, tailWord_1209216, baseEnd_1209216] using wordTrace_append hprefix tailTrace_1209216
  have hstable : (prefixWord ++ tailWord_1209216).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1209216).length < 2 ^ (prefixWord ++ tailWord_1209216).sum := by decide
  have hdescent : baseEnd_1209216 < baseStart_1209216 := by decide
  rcases family_descends (prefixWord ++ tailWord_1209216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1209265 : List Nat := [1, 2, 2, 4, 3, 1, 1, 1, 3, 4]
def baseStart_1209265 : Nat := 118140960795 + 1209265 * 2 ^ 59
def prefixEnd_1209265 : Nat := 4983230072969 + 3 ^ 40 * 1209265 * 2
def baseEnd_1209265 : Nat := 413956122439544319217465

theorem tailTrace_1209265 : CollatzResearch.WordTrace tailWord_1209265 prefixEnd_1209265 413956122439544319217465 := by
  unfold tailWord_1209265
  simp only [CollatzResearch.WordTrace]
  refine ⟨44105517964046905864733249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29403678642697937243155499 44105517964046905864733249)
  ·
    refine ⟨33079138473035179398549937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44105517964046905864733249 33079138473035179398549937)
    ·
      refine ⟨24809353854776384548912453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33079138473035179398549937 24809353854776384548912453)
      ·
        refine ⟨4651753847770572102921085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24809353854776384548912453 4651753847770572102921085)
        ·
          refine ⟨1744407692913964538595407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4651753847770572102921085 1744407692913964538595407)
          ·
            refine ⟨2616611539370946807893111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1744407692913964538595407 2616611539370946807893111)
            ·
              refine ⟨3924917309056420211839667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2616611539370946807893111 3924917309056420211839667)
              ·
                refine ⟨5887375963584630317759501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3924917309056420211839667 5887375963584630317759501)
                ·
                  refine ⟨2207765986344236369159813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5887375963584630317759501 2207765986344236369159813)
                  ·
                    refine ⟨413956122439544319217465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2207765986344236369159813 413956122439544319217465)
                    ·
                      rfl

theorem cell22_1209265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 1, 1, 3, 4].length) (baseStart_1209265 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1209265 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1209265 prefixEnd_1209265 := by exact prefixLift 1209265
  have htrace : WordTrace (prefixWord ++ tailWord_1209265) baseStart_1209265 baseEnd_1209265 := by
    simpa [prefixWord, tailWord_1209265, baseEnd_1209265] using wordTrace_append hprefix tailTrace_1209265
  have hstable : (prefixWord ++ tailWord_1209265).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1209265).length < 2 ^ (prefixWord ++ tailWord_1209265).sum := by decide
  have hdescent : baseEnd_1209265 < baseStart_1209265 := by decide
  rcases family_descends (prefixWord ++ tailWord_1209265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1209291 : List Nat := [1, 1, 1, 1, 3, 15]
def baseStart_1209291 : Nat := 118140960795 + 1209291 * 2 ^ 59
def prefixEnd_1209291 : Nat := 4983230072969 + 3 ^ 40 * 1209291 * 2
def baseEnd_1209291 : Nat := 5110679293467764420585

theorem tailTrace_1209291 : CollatzResearch.WordTrace tailWord_1209291 prefixEnd_1209291 5110679293467764420585 := by
  unfold tailWord_1209291
  simp only [CollatzResearch.WordTrace]
  refine ⟨44106466261952712305179727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29404310841301808203453151 44106466261952712305179727)
  ·
    refine ⟨66159699392929068457769591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44106466261952712305179727 66159699392929068457769591)
    ·
      refine ⟨99239549089393602686654387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66159699392929068457769591 99239549089393602686654387)
      ·
        refine ⟨148859323634090404029981581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99239549089393602686654387 148859323634090404029981581)
        ·
          refine ⟨55822246362783901511243093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 148859323634090404029981581 55822246362783901511243093)
          ·
            refine ⟨5110679293467764420585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 15 55822246362783901511243093 5110679293467764420585)
            ·
              rfl

theorem cell22_1209291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 15].length) (baseStart_1209291 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1209291 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1209291 prefixEnd_1209291 := by exact prefixLift 1209291
  have htrace : WordTrace (prefixWord ++ tailWord_1209291) baseStart_1209291 baseEnd_1209291 := by
    simpa [prefixWord, tailWord_1209291, baseEnd_1209291] using wordTrace_append hprefix tailTrace_1209291
  have hstable : (prefixWord ++ tailWord_1209291).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1209291).length < 2 ^ (prefixWord ++ tailWord_1209291).sum := by decide
  have hdescent : baseEnd_1209291 < baseStart_1209291 := by decide
  rcases family_descends (prefixWord ++ tailWord_1209291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1209295 : List Nat := [1, 1, 2, 1, 1, 6, 1, 4, 2, 3]
def baseStart_1209295 : Nat := 118140960795 + 1209295 * 2 ^ 59
def prefixEnd_1209295 : Nat := 4983230072969 + 3 ^ 40 * 1209295 * 2
def baseEnd_1209295 : Nat := 413966392052634240967373

theorem tailTrace_1209295 : CollatzResearch.WordTrace tailWord_1209295 prefixEnd_1209295 413966392052634240967373 := by
  unfold tailWord_1209295
  simp only [CollatzResearch.WordTrace]
  refine ⟨44106612153938220988325339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29404408102625480658883559 44106612153938220988325339)
  ·
    refine ⟨66159918230907331482488009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44106612153938220988325339 66159918230907331482488009)
    ·
      refine ⟨49619938673180498611866007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66159918230907331482488009 49619938673180498611866007)
      ·
        refine ⟨74429908009770747917799011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49619938673180498611866007 74429908009770747917799011)
        ·
          refine ⟨111644862014656121876698517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74429908009770747917799011 111644862014656121876698517)
          ·
            refine ⟨5233352906937005712970243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 111644862014656121876698517 5233352906937005712970243)
            ·
              refine ⟨7850029360405508569455365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5233352906937005712970243 7850029360405508569455365)
              ·
                refine ⟨1471880505076032856772881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7850029360405508569455365 1471880505076032856772881)
                ·
                  refine ⟨1103910378807024642579661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1471880505076032856772881 1103910378807024642579661)
                  ·
                    refine ⟨413966392052634240967373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1103910378807024642579661 413966392052634240967373)
                    ·
                      rfl

theorem cell22_1209295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 4, 2, 3].length) (baseStart_1209295 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1209295 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1209295 prefixEnd_1209295 := by exact prefixLift 1209295
  have htrace : WordTrace (prefixWord ++ tailWord_1209295) baseStart_1209295 baseEnd_1209295 := by
    simpa [prefixWord, tailWord_1209295, baseEnd_1209295] using wordTrace_append hprefix tailTrace_1209295
  have hstable : (prefixWord ++ tailWord_1209295).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1209295).length < 2 ^ (prefixWord ++ tailWord_1209295).sum := by decide
  have hdescent : baseEnd_1209295 < baseStart_1209295 := by decide
  rcases family_descends (prefixWord ++ tailWord_1209295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1209333 : List Nat := [1, 3, 5, 2, 2, 1, 2, 1, 1, 4]
def baseStart_1209333 : Nat := 118140960795 + 1209333 * 2 ^ 59
def prefixEnd_1209333 : Nat := 4983230072969 + 3 ^ 40 * 1209333 * 2
def baseEnd_1209333 : Nat := 413979400229214808517257

theorem tailTrace_1209333 : CollatzResearch.WordTrace tailWord_1209333 prefixEnd_1209333 413979400229214808517257 := by
  unfold tailWord_1209333
  simp only [CollatzResearch.WordTrace]
  refine ⟨44107998127800553478208653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29405332085200368985472435 44107998127800553478208653)
  ·
    refine ⟨16540499297925207554328245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44107998127800553478208653 16540499297925207554328245)
    ·
      refine ⟨1550671809180488208218273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16540499297925207554328245 1550671809180488208218273)
      ·
        refine ⟨1163003856885366156163705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1550671809180488208218273 1163003856885366156163705)
        ·
          refine ⟨872252892664024617122779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1163003856885366156163705 872252892664024617122779)
          ·
            refine ⟨1308379338996036925684169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 872252892664024617122779 1308379338996036925684169)
            ·
              refine ⟨981284504247027694263127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1308379338996036925684169 981284504247027694263127)
              ·
                refine ⟨1471926756370541541394691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 981284504247027694263127 1471926756370541541394691)
                ·
                  refine ⟨2207890134555812312092037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1471926756370541541394691 2207890134555812312092037)
                  ·
                    refine ⟨413979400229214808517257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2207890134555812312092037 413979400229214808517257)
                    ·
                      rfl

theorem cell22_1209333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 2, 1, 1, 4].length) (baseStart_1209333 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1209333 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1209333 prefixEnd_1209333 := by exact prefixLift 1209333
  have htrace : WordTrace (prefixWord ++ tailWord_1209333) baseStart_1209333 baseEnd_1209333 := by
    simpa [prefixWord, tailWord_1209333, baseEnd_1209333] using wordTrace_append hprefix tailTrace_1209333
  have hstable : (prefixWord ++ tailWord_1209333).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1209333).length < 2 ^ (prefixWord ++ tailWord_1209333).sum := by decide
  have hdescent : baseEnd_1209333 < baseStart_1209333 := by decide
  rcases family_descends (prefixWord ++ tailWord_1209333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1209415 : List Nat := [1, 1, 4, 1, 3, 2, 3, 1, 6]
def baseStart_1209415 : Nat := 118140960795 + 1209415 * 2 ^ 59
def prefixEnd_1209415 : Nat := 4983230072969 + 3 ^ 40 * 1209415 * 2
def baseEnd_1209415 : Nat := 138002490168331309322335

theorem tailTrace_1209415 : CollatzResearch.WordTrace tailWord_1209415 prefixEnd_1209415 138002490168331309322335 := by
  unfold tailWord_1209415
  simp only [CollatzResearch.WordTrace]
  refine ⟨44110988913503481482693699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29407325942335654321795799 44110988913503481482693699)
  ·
    refine ⟨66166483370255222224040549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44110988913503481482693699 66166483370255222224040549)
    ·
      refine ⟨12406215631922854167007603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 66166483370255222224040549 12406215631922854167007603)
      ·
        refine ⟨18609323447884281250511405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12406215631922854167007603 18609323447884281250511405)
        ·
          refine ⟨6978496292956605468941777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18609323447884281250511405 6978496292956605468941777)
          ·
            refine ⟨5233872219717454101706333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6978496292956605468941777 5233872219717454101706333)
            ·
              refine ⟨1962702082394045288139875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5233872219717454101706333 1962702082394045288139875)
              ·
                refine ⟨2944053123591067932209813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1962702082394045288139875 2944053123591067932209813)
                ·
                  refine ⟨138002490168331309322335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2944053123591067932209813 138002490168331309322335)
                  ·
                    rfl

theorem cell22_1209415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 3, 1, 6].length) (baseStart_1209415 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1209415 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1209415 prefixEnd_1209415 := by exact prefixLift 1209415
  have htrace : WordTrace (prefixWord ++ tailWord_1209415) baseStart_1209415 baseEnd_1209415 := by
    simpa [prefixWord, tailWord_1209415, baseEnd_1209415] using wordTrace_append hprefix tailTrace_1209415
  have hstable : (prefixWord ++ tailWord_1209415).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1209415).length < 2 ^ (prefixWord ++ tailWord_1209415).sum := by decide
  have hdescent : baseEnd_1209415 < baseStart_1209415 := by decide
  rcases family_descends (prefixWord ++ tailWord_1209415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1209462 : List Nat := [5, 1, 1, 2, 1, 1, 1, 4, 2, 4]
def baseStart_1209462 : Nat := 118140960795 + 1209462 * 2 ^ 59
def prefixEnd_1209462 : Nat := 4983230072969 + 3 ^ 40 * 1209462 * 2
def baseEnd_1209462 : Nat := 414023559565501472041861

theorem tailTrace_1209462 : CollatzResearch.WordTrace tailWord_1209462 prefixEnd_1209462 414023559565501472041861 := by
  unfold tailWord_1209462
  simp only [CollatzResearch.WordTrace]
  refine ⟨2757043946520825531853415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 29408468762888805673103093 2757043946520825531853415)
  ·
    refine ⟨4135565919781238297780123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2757043946520825531853415 4135565919781238297780123)
    ·
      refine ⟨6203348879671857446670185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4135565919781238297780123 6203348879671857446670185)
      ·
        refine ⟨4652511659753893085002639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6203348879671857446670185 4652511659753893085002639)
        ·
          refine ⟨6978767489630839627503959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4652511659753893085002639 6978767489630839627503959)
          ·
            refine ⟨10468151234446259441255939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6978767489630839627503959 10468151234446259441255939)
            ·
              refine ⟨15702226851669389161883909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10468151234446259441255939 15702226851669389161883909)
              ·
                refine ⟨2944167534688010467853233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15702226851669389161883909 2944167534688010467853233)
                ·
                  refine ⟨2208125651016007850889925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2944167534688010467853233 2208125651016007850889925)
                  ·
                    refine ⟨414023559565501472041861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2208125651016007850889925 414023559565501472041861)
                    ·
                      rfl

theorem cell22_1209462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 4, 2, 4].length) (baseStart_1209462 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1209462 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1209462 prefixEnd_1209462 := by exact prefixLift 1209462
  have htrace : WordTrace (prefixWord ++ tailWord_1209462) baseStart_1209462 baseEnd_1209462 := by
    simpa [prefixWord, tailWord_1209462, baseEnd_1209462] using wordTrace_append hprefix tailTrace_1209462
  have hstable : (prefixWord ++ tailWord_1209462).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1209462).length < 2 ^ (prefixWord ++ tailWord_1209462).sum := by decide
  have hdescent : baseEnd_1209462 < baseStart_1209462 := by decide
  rcases family_descends (prefixWord ++ tailWord_1209462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1209477 : List Nat := [1, 3, 1, 1, 6, 2, 1, 7]
def baseStart_1209477 : Nat := 118140960795 + 1209477 * 2 ^ 59
def prefixEnd_1209477 : Nat := 4983230072969 + 3 ^ 40 * 1209477 * 2
def baseEnd_1209477 : Nat := 46003188263560714768535

theorem tailTrace_1209477 : CollatzResearch.WordTrace tailWord_1209477 prefixEnd_1209477 46003188263560714768535 := by
  unfold tailWord_1209477
  simp only [CollatzResearch.WordTrace]
  refine ⟨44113250239278866071450685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29408833492852577380967123 44113250239278866071450685)
  ·
    refine ⟨16542468839729574776794007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44113250239278866071450685 16542468839729574776794007)
    ·
      refine ⟨24813703259594362165191011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16542468839729574776794007 24813703259594362165191011)
      ·
        refine ⟨37220554889391543247786517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24813703259594362165191011 37220554889391543247786517)
        ·
          refine ⟨1744713510440228589739993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 37220554889391543247786517 1744713510440228589739993)
          ·
            refine ⟨1308535132830171442304995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1744713510440228589739993 1308535132830171442304995)
            ·
              refine ⟨1962802699245257163457493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1308535132830171442304995 1962802699245257163457493)
              ·
                refine ⟨46003188263560714768535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1962802699245257163457493 46003188263560714768535)
                ·
                  rfl

theorem cell22_1209477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 1, 7].length) (baseStart_1209477 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1209477 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1209477 prefixEnd_1209477 := by exact prefixLift 1209477
  have htrace : WordTrace (prefixWord ++ tailWord_1209477) baseStart_1209477 baseEnd_1209477 := by
    simpa [prefixWord, tailWord_1209477, baseEnd_1209477] using wordTrace_append hprefix tailTrace_1209477
  have hstable : (prefixWord ++ tailWord_1209477).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1209477).length < 2 ^ (prefixWord ++ tailWord_1209477).sum := by decide
  have hdescent : baseEnd_1209477 < baseStart_1209477 := by decide
  rcases family_descends (prefixWord ++ tailWord_1209477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1209505 : List Nat := [1, 2, 3, 3, 1, 1, 2, 2, 7]
def baseStart_1209505 : Nat := 118140960795 + 1209505 * 2 ^ 59
def prefixEnd_1209505 : Nat := 4983230072969 + 3 ^ 40 * 1209505 * 2
def baseEnd_1209505 : Nat := 138012759781421231072243

theorem tailTrace_1209505 : CollatzResearch.WordTrace tailWord_1209505 prefixEnd_1209505 138012759781421231072243 := by
  unfold tailWord_1209505
  simp only [CollatzResearch.WordTrace]
  refine ⟨44114271483177426853469969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29409514322118284568979979 44114271483177426853469969)
  ·
    refine ⟨33085703612383070140102477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44114271483177426853469969 33085703612383070140102477)
    ·
      refine ⟨12407138854643651302538429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33085703612383070140102477 12407138854643651302538429)
      ·
        refine ⟨4652677070491369238451911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12407138854643651302538429 4652677070491369238451911)
        ·
          refine ⟨6979015605737053857677867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4652677070491369238451911 6979015605737053857677867)
          ·
            refine ⟨10468523408605580786516801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6979015605737053857677867 10468523408605580786516801)
            ·
              refine ⟨7851392556454185589887601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10468523408605580786516801 7851392556454185589887601)
              ·
                refine ⟨5888544417340639192415701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7851392556454185589887601 5888544417340639192415701)
                ·
                  refine ⟨138012759781421231072243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5888544417340639192415701 138012759781421231072243)
                  ·
                    rfl

theorem cell22_1209505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 2, 7].length) (baseStart_1209505 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1209505 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1209505 prefixEnd_1209505 := by exact prefixLift 1209505
  have htrace : WordTrace (prefixWord ++ tailWord_1209505) baseStart_1209505 baseEnd_1209505 := by
    simpa [prefixWord, tailWord_1209505, baseEnd_1209505] using wordTrace_append hprefix tailTrace_1209505
  have hstable : (prefixWord ++ tailWord_1209505).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1209505).length < 2 ^ (prefixWord ++ tailWord_1209505).sum := by decide
  have hdescent : baseEnd_1209505 < baseStart_1209505 := by decide
  rcases family_descends (prefixWord ++ tailWord_1209505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1209509 : List Nat := [1, 3, 1, 2, 1, 4, 1, 5, 1, 3]
def baseStart_1209509 : Nat := 118140960795 + 1209509 * 2 ^ 59
def prefixEnd_1209509 : Nat := 4983230072969 + 3 ^ 40 * 1209509 * 2
def baseEnd_1209509 : Nat := 414039648626009016116717

theorem tailTrace_1209509 : CollatzResearch.WordTrace tailWord_1209509 prefixEnd_1209509 414039648626009016116717 := by
  unfold tailWord_1209509
  simp only [CollatzResearch.WordTrace]
  refine ⟨44114417375162935536615581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29409611583441957024410387 44114417375162935536615581)
  ·
    refine ⟨16542906515686100826230843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44114417375162935536615581 16542906515686100826230843)
    ·
      refine ⟨24814359773529151239346265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16542906515686100826230843 24814359773529151239346265)
      ·
        refine ⟨18610769830146863429509699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24814359773529151239346265 18610769830146863429509699)
        ·
          refine ⟨27916154745220295144264549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18610769830146863429509699 27916154745220295144264549)
          ·
            refine ⟨5234279014728805339549603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27916154745220295144264549 5234279014728805339549603)
            ·
              refine ⟨7851418522093208009324405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5234279014728805339549603 7851418522093208009324405)
              ·
                refine ⟨736070486446238250874163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7851418522093208009324405 736070486446238250874163)
                ·
                  refine ⟨1104105729669357376311245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 736070486446238250874163 1104105729669357376311245)
                  ·
                    refine ⟨414039648626009016116717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1104105729669357376311245 414039648626009016116717)
                    ·
                      rfl

theorem cell22_1209509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 5, 1, 3].length) (baseStart_1209509 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1209509 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1209509 prefixEnd_1209509 := by exact prefixLift 1209509
  have htrace : WordTrace (prefixWord ++ tailWord_1209509) baseStart_1209509 baseEnd_1209509 := by
    simpa [prefixWord, tailWord_1209509, baseEnd_1209509] using wordTrace_append hprefix tailTrace_1209509
  have hstable : (prefixWord ++ tailWord_1209509).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1209509).length < 2 ^ (prefixWord ++ tailWord_1209509).sum := by decide
  have hdescent : baseEnd_1209509 < baseStart_1209509 := by decide
  rcases family_descends (prefixWord ++ tailWord_1209509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1209522 : List Nat := [3, 2, 1, 1, 1, 4, 3, 2, 5]
def baseStart_1209522 : Nat := 118140960795 + 1209522 * 2 ^ 59
def prefixEnd_1209522 : Nat := 4983230072969 + 3 ^ 40 * 1209522 * 2
def baseEnd_1209522 : Nat := 138014699597227105180559

theorem tailTrace_1209522 : CollatzResearch.WordTrace tailWord_1209522 prefixEnd_1209522 138014699597227105180559 := by
  unfold tailWord_1209522
  simp only [CollatzResearch.WordTrace]
  refine ⟨11028722881028959689209705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29409927682743892504559213 11028722881028959689209705)
  ·
    refine ⟨8271542160771719766907279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11028722881028959689209705 8271542160771719766907279)
    ·
      refine ⟨12407313241157579650360919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8271542160771719766907279 12407313241157579650360919)
      ·
        refine ⟨18610969861736369475541379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12407313241157579650360919 18610969861736369475541379)
        ·
          refine ⟨27916454792604554213312069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18610969861736369475541379 27916454792604554213312069)
          ·
            refine ⟨5234335273613353914996013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27916454792604554213312069 5234335273613353914996013)
            ·
              refine ⟨1962875727605007718123505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5234335273613353914996013 1962875727605007718123505)
              ·
                refine ⟨1472156795703755788592629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1962875727605007718123505 1472156795703755788592629)
                ·
                  refine ⟨138014699597227105180559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1472156795703755788592629 138014699597227105180559)
                  ·
                    rfl

theorem cell22_1209522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 3, 2, 5].length) (baseStart_1209522 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1209522 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1209522 prefixEnd_1209522 := by exact prefixLift 1209522
  have htrace : WordTrace (prefixWord ++ tailWord_1209522) baseStart_1209522 baseEnd_1209522 := by
    simpa [prefixWord, tailWord_1209522, baseEnd_1209522] using wordTrace_append hprefix tailTrace_1209522
  have hstable : (prefixWord ++ tailWord_1209522).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1209522).length < 2 ^ (prefixWord ++ tailWord_1209522).sum := by decide
  have hdescent : baseEnd_1209522 < baseStart_1209522 := by decide
  rcases family_descends (prefixWord ++ tailWord_1209522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1209535 : List Nat := [1, 1, 2, 2, 2, 2, 2, 1, 5, 4]
def baseStart_1209535 : Nat := 118140960795 + 1209535 * 2 ^ 59
def prefixEnd_1209535 : Nat := 4983230072969 + 3 ^ 40 * 1209535 * 2
def baseEnd_1209535 : Nat := 414048548957353614966637

theorem tailTrace_1209535 : CollatzResearch.WordTrace tailWord_1209535 prefixEnd_1209535 414048548957353614966637 := by
  unfold tailWord_1209535
  simp only [CollatzResearch.WordTrace]
  refine ⟨44115365673068741977062059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29410243782045827984708039 44115365673068741977062059)
  ·
    refine ⟨66173048509603112965593089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44115365673068741977062059 66173048509603112965593089)
    ·
      refine ⟨49629786382202334724194817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66173048509603112965593089 49629786382202334724194817)
      ·
        refine ⟨37222339786651751043146113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49629786382202334724194817 37222339786651751043146113)
        ·
          refine ⟨27916754839988813282359585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37222339786651751043146113 27916754839988813282359585)
          ·
            refine ⟨20937566129991609961769689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27916754839988813282359585 20937566129991609961769689)
            ·
              refine ⟨15703174597493707471327267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20937566129991609961769689 15703174597493707471327267)
              ·
                refine ⟨23554761896240561206990901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15703174597493707471327267 23554761896240561206990901)
                ·
                  refine ⟨2208258927772552613155397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23554761896240561206990901 2208258927772552613155397)
                  ·
                    refine ⟨414048548957353614966637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2208258927772552613155397 414048548957353614966637)
                    ·
                      rfl

theorem cell22_1209535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 1, 5, 4].length) (baseStart_1209535 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1209535 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1209535 prefixEnd_1209535 := by exact prefixLift 1209535
  have htrace : WordTrace (prefixWord ++ tailWord_1209535) baseStart_1209535 baseEnd_1209535 := by
    simpa [prefixWord, tailWord_1209535, baseEnd_1209535] using wordTrace_append hprefix tailTrace_1209535
  have hstable : (prefixWord ++ tailWord_1209535).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1209535).length < 2 ^ (prefixWord ++ tailWord_1209535).sum := by decide
  have hdescent : baseEnd_1209535 < baseStart_1209535 := by decide
  rcases family_descends (prefixWord ++ tailWord_1209535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1209599 : List Nat := [1, 1, 2, 2, 1, 6, 1, 3, 2, 3]
def baseStart_1209599 : Nat := 118140960795 + 1209599 * 2 ^ 59
def prefixEnd_1209599 : Nat := 4983230072969 + 3 ^ 40 * 1209599 * 2
def baseEnd_1209599 : Nat := 414070457465278781366441

theorem tailTrace_1209599 : CollatzResearch.WordTrace tailWord_1209599 prefixEnd_1209599 414070457465278781366441 := by
  unfold tailWord_1209599
  simp only [CollatzResearch.WordTrace]
  refine ⟨44117699944836880907391851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29411799963224587271594567 44117699944836880907391851)
  ·
    refine ⟨66176549917255321361087777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44117699944836880907391851 66176549917255321361087777)
    ·
      refine ⟨49632412437941491020815833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66176549917255321361087777 49632412437941491020815833)
      ·
        refine ⟨37224309328456118265611875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49632412437941491020815833 37224309328456118265611875)
        ·
          refine ⟨55836463992684177398417813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37224309328456118265611875 55836463992684177398417813)
          ·
            refine ⟨2617334249657070815550835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 55836463992684177398417813 2617334249657070815550835)
            ·
              refine ⟨3926001374485606223326253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2617334249657070815550835 3926001374485606223326253)
              ·
                refine ⟨1472250515432102333747345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3926001374485606223326253 1472250515432102333747345)
                ·
                  refine ⟨1104187886574076750310509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1472250515432102333747345 1104187886574076750310509)
                  ·
                    refine ⟨414070457465278781366441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1104187886574076750310509 414070457465278781366441)
                    ·
                      rfl

theorem cell22_1209599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 1, 3, 2, 3].length) (baseStart_1209599 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1209599 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1209599 prefixEnd_1209599 := by exact prefixLift 1209599
  have htrace : WordTrace (prefixWord ++ tailWord_1209599) baseStart_1209599 baseEnd_1209599 := by
    simpa [prefixWord, tailWord_1209599, baseEnd_1209599] using wordTrace_append hprefix tailTrace_1209599
  have hstable : (prefixWord ++ tailWord_1209599).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1209599).length < 2 ^ (prefixWord ++ tailWord_1209599).sum := by decide
  have hdescent : baseEnd_1209599 < baseStart_1209599 := by decide
  rcases family_descends (prefixWord ++ tailWord_1209599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1209614 : List Nat := [4, 1, 1, 2, 1, 4, 2, 1, 2, 4]
def baseStart_1209614 : Nat := 118140960795 + 1209614 * 2 ^ 59
def prefixEnd_1209614 : Nat := 4983230072969 + 3 ^ 40 * 1209614 * 2
def baseEnd_1209614 : Nat := 414075592271823742241395

theorem tailTrace_1209614 : CollatzResearch.WordTrace tailWord_1209614 prefixEnd_1209614 414075592271823742241395 := by
  unfold tailWord_1209614
  simp only [CollatzResearch.WordTrace]
  refine ⟨5514780879972817308648487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29412164693188358979458597 5514780879972817308648487)
  ·
    refine ⟨8272171319959225962972731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5514780879972817308648487 8272171319959225962972731)
    ·
      refine ⟨12408256979938838944459097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8272171319959225962972731 12408256979938838944459097)
      ·
        refine ⟨9306192734954129208344323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12408256979938838944459097 9306192734954129208344323)
        ·
          refine ⟨13959289102431193812516485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9306192734954129208344323 13959289102431193812516485)
          ·
            refine ⟨2617366706705848839846841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13959289102431193812516485 2617366706705848839846841)
            ·
              refine ⟨1963025030029386629885131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2617366706705848839846841 1963025030029386629885131)
              ·
                refine ⟨2944537545044079944827697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1963025030029386629885131 2944537545044079944827697)
                ·
                  refine ⟨2208403158783059958620773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2944537545044079944827697 2208403158783059958620773)
                  ·
                    refine ⟨414075592271823742241395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2208403158783059958620773 414075592271823742241395)
                    ·
                      rfl

theorem cell22_1209614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 2, 1, 2, 4].length) (baseStart_1209614 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1209614 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1209614 prefixEnd_1209614 := by exact prefixLift 1209614
  have htrace : WordTrace (prefixWord ++ tailWord_1209614) baseStart_1209614 baseEnd_1209614 := by
    simpa [prefixWord, tailWord_1209614, baseEnd_1209614] using wordTrace_append hprefix tailTrace_1209614
  have hstable : (prefixWord ++ tailWord_1209614).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1209614).length < 2 ^ (prefixWord ++ tailWord_1209614).sum := by decide
  have hdescent : baseEnd_1209614 < baseStart_1209614 := by decide
  rcases family_descends (prefixWord ++ tailWord_1209614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1209625 : List Nat := [1, 2, 1, 2, 1, 1, 1, 1, 6, 6]
def baseStart_1209625 : Nat := 118140960795 + 1209625 * 2 ^ 59
def prefixEnd_1209625 : Nat := 4983230072969 + 3 ^ 40 * 1209625 * 2
def baseEnd_1209625 : Nat := 414079357796623380216361

theorem tailTrace_1209625 : CollatzResearch.WordTrace tailWord_1209625 prefixEnd_1209625 414079357796623380216361 := by
  unfold tailWord_1209625
  simp only [CollatzResearch.WordTrace]
  refine ⟨44118648242742687347838329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29412432161828458231892219 44118648242742687347838329)
  ·
    refine ⟨33088986182057015510878747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44118648242742687347838329 33088986182057015510878747)
    ·
      refine ⟨49633479273085523266318121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33088986182057015510878747 49633479273085523266318121)
      ·
        refine ⟨37225109454814142449738591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49633479273085523266318121 37225109454814142449738591)
        ·
          refine ⟨55837664182221213674607887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37225109454814142449738591 55837664182221213674607887)
          ·
            refine ⟨83756496273331820511911831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55837664182221213674607887 83756496273331820511911831)
            ·
              refine ⟨125634744409997730767867747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83756496273331820511911831 125634744409997730767867747)
              ·
                refine ⟨188452116614996596151801621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 125634744409997730767867747 188452116614996596151801621)
                ·
                  refine ⟨8833692966327965444615701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 188452116614996596151801621 8833692966327965444615701)
                  ·
                    refine ⟨414079357796623380216361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8833692966327965444615701 414079357796623380216361)
                    ·
                      rfl

theorem cell22_1209625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 6, 6].length) (baseStart_1209625 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1209625 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1209625 prefixEnd_1209625 := by exact prefixLift 1209625
  have htrace : WordTrace (prefixWord ++ tailWord_1209625) baseStart_1209625 baseEnd_1209625 := by
    simpa [prefixWord, tailWord_1209625, baseEnd_1209625] using wordTrace_append hprefix tailTrace_1209625
  have hstable : (prefixWord ++ tailWord_1209625).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1209625).length < 2 ^ (prefixWord ++ tailWord_1209625).sum := by decide
  have hdescent : baseEnd_1209625 < baseStart_1209625 := by decide
  rcases family_descends (prefixWord ++ tailWord_1209625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1209736 : List Nat := [2, 1, 3, 3, 1, 2, 3, 3, 4]
def baseStart_1209736 : Nat := 118140960795 + 1209736 * 2 ^ 59
def prefixEnd_1209736 : Nat := 4983230072969 + 3 ^ 40 * 1209736 * 2
def baseEnd_1209736 : Nat := 138039118455018696897007

theorem tailTrace_1209736 : CollatzResearch.WordTrace tailWord_1209736 prefixEnd_1209736 138039118455018696897007 := by
  unfold tailWord_1209736
  simp only [CollatzResearch.WordTrace]
  refine ⟨22061348372670276652564531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29415131163560368870086041 22061348372670276652564531)
  ·
    refine ⟨33092022559005414978846797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22061348372670276652564531 33092022559005414978846797)
    ·
      refine ⟨12409508459627030617067549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33092022559005414978846797 12409508459627030617067549)
      ·
        refine ⟨4653565672360136481400331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12409508459627030617067549 4653565672360136481400331)
        ·
          refine ⟨6980348508540204722100497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4653565672360136481400331 6980348508540204722100497)
          ·
            refine ⟨5235261381405153541575373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6980348508540204722100497 5235261381405153541575373)
            ·
              refine ⟨1963223018026932578090765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5235261381405153541575373 1963223018026932578090765)
              ·
                refine ⟨736208631760099716784037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1963223018026932578090765 736208631760099716784037)
                ·
                  refine ⟨138039118455018696897007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 736208631760099716784037 138039118455018696897007)
                  ·
                    rfl

theorem cell22_1209736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 3, 3, 4].length) (baseStart_1209736 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1209736 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1209736 prefixEnd_1209736 := by exact prefixLift 1209736
  have htrace : WordTrace (prefixWord ++ tailWord_1209736) baseStart_1209736 baseEnd_1209736 := by
    simpa [prefixWord, tailWord_1209736, baseEnd_1209736] using wordTrace_append hprefix tailTrace_1209736
  have hstable : (prefixWord ++ tailWord_1209736).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1209736).length < 2 ^ (prefixWord ++ tailWord_1209736).sum := by decide
  have hdescent : baseEnd_1209736 < baseStart_1209736 := by decide
  rcases family_descends (prefixWord ++ tailWord_1209736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1209779 : List Nat := [1, 1, 1, 2, 3, 1, 1, 6, 3, 3]
def baseStart_1209779 : Nat := 118140960795 + 1209779 * 2 ^ 59
def prefixEnd_1209779 : Nat := 4983230072969 + 3 ^ 40 * 1209779 * 2
def baseEnd_1209779 : Nat := 414132075143818311865889

theorem tailTrace_1209779 : CollatzResearch.WordTrace tailWord_1209779 prefixEnd_1209779 414132075143818311865889 := by
  unfold tailWord_1209779
  simp only [CollatzResearch.WordTrace]
  refine ⟨44124265084184771648944391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29416176722789847765962927 44124265084184771648944391)
  ·
    refine ⟨66186397626277157473416587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44124265084184771648944391 66186397626277157473416587)
    ·
      refine ⟨99279596439415736210124881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66186397626277157473416587 99279596439415736210124881)
      ·
        refine ⟨74459697329561802157593661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99279596439415736210124881 74459697329561802157593661)
        ·
          refine ⟨27922386498585675809097623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74459697329561802157593661 27922386498585675809097623)
          ·
            refine ⟨41883579747878513713646435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27922386498585675809097623 41883579747878513713646435)
            ·
              refine ⟨62825369621817770570469653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41883579747878513713646435 62825369621817770570469653)
              ·
                refine ⟨2944939201022707995490765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 62825369621817770570469653 2944939201022707995490765)
                ·
                  refine ⟨1104352200383515498309037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2944939201022707995490765 1104352200383515498309037)
                  ·
                    refine ⟨414132075143818311865889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1104352200383515498309037 414132075143818311865889)
                    ·
                      rfl

theorem cell22_1209779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 6, 3, 3].length) (baseStart_1209779 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1209779 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1209779 prefixEnd_1209779 := by exact prefixLift 1209779
  have htrace : WordTrace (prefixWord ++ tailWord_1209779) baseStart_1209779 baseEnd_1209779 := by
    simpa [prefixWord, tailWord_1209779, baseEnd_1209779] using wordTrace_append hprefix tailTrace_1209779
  have hstable : (prefixWord ++ tailWord_1209779).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1209779).length < 2 ^ (prefixWord ++ tailWord_1209779).sum := by decide
  have hdescent : baseEnd_1209779 < baseStart_1209779 := by decide
  rcases family_descends (prefixWord ++ tailWord_1209779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1209792 : List Nat := [2, 1, 1, 2, 3, 1, 2, 1, 9]
def baseStart_1209792 : Nat := 118140960795 + 1209792 * 2 ^ 59
def prefixEnd_1209792 : Nat := 4983230072969 + 3 ^ 40 * 1209792 * 2
def baseEnd_1209792 : Nat := 138045508436496870430283

theorem tailTrace_1209792 : CollatzResearch.WordTrace tailWord_1209792 prefixEnd_1209792 138045508436496870430283 := by
  unfold tailWord_1209792
  simp only [CollatzResearch.WordTrace]
  refine ⟨22062369616568837434583815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29416492822091783246111753 22062369616568837434583815)
  ·
    refine ⟨33093554424853256151875723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22062369616568837434583815 33093554424853256151875723)
    ·
      refine ⟨49640331637279884227813585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33093554424853256151875723 49640331637279884227813585)
      ·
        refine ⟨37230248727959913170860189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49640331637279884227813585 37230248727959913170860189)
        ·
          refine ⟨13961343272984967439072571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37230248727959913170860189 13961343272984967439072571)
          ·
            refine ⟨20942014909477451158608857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13961343272984967439072571 20942014909477451158608857)
            ·
              refine ⟨15706511182108088368956643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20942014909477451158608857 15706511182108088368956643)
              ·
                refine ⟨23559766773162132553434965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15706511182108088368956643 23559766773162132553434965)
                ·
                  refine ⟨138045508436496870430283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 23559766773162132553434965 138045508436496870430283)
                  ·
                    rfl

theorem cell22_1209792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 1, 9].length) (baseStart_1209792 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1209792 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1209792 prefixEnd_1209792 := by exact prefixLift 1209792
  have htrace : WordTrace (prefixWord ++ tailWord_1209792) baseStart_1209792 baseEnd_1209792 := by
    simpa [prefixWord, tailWord_1209792, baseEnd_1209792] using wordTrace_append hprefix tailTrace_1209792
  have hstable : (prefixWord ++ tailWord_1209792).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1209792).length < 2 ^ (prefixWord ++ tailWord_1209792).sum := by decide
  have hdescent : baseEnd_1209792 < baseStart_1209792 := by decide
  rcases family_descends (prefixWord ++ tailWord_1209792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1209813 : List Nat := [1, 3, 2, 3, 1, 1, 3, 4, 1, 3]
def baseStart_1209813 : Nat := 118140960795 + 1209813 * 2 ^ 59
def prefixEnd_1209813 : Nat := 4983230072969 + 3 ^ 40 * 1209813 * 2
def baseEnd_1209813 : Nat := 414143714038653556515785

theorem tailTrace_1209813 : CollatzResearch.WordTrace tailWord_1209813 prefixEnd_1209813 414143714038653556515785 := by
  unfold tailWord_1209813
  simp only [CollatzResearch.WordTrace]
  refine ⟨44125505166061595455682093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29417003444041063637121395 44125505166061595455682093)
  ·
    refine ⟨16547064437273098295880785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44125505166061595455682093 16547064437273098295880785)
    ·
      refine ⟨12410298327954823721910589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16547064437273098295880785 12410298327954823721910589)
      ·
        refine ⟨4653861872983058895716471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12410298327954823721910589 4653861872983058895716471)
        ·
          refine ⟨6980792809474588343574707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4653861872983058895716471 6980792809474588343574707)
          ·
            refine ⟨10471189214211882515362061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6980792809474588343574707 10471189214211882515362061)
            ·
              refine ⟨3926695955329455943260773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10471189214211882515362061 3926695955329455943260773)
              ·
                refine ⟨736255491624272989361395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3926695955329455943260773 736255491624272989361395)
                ·
                  refine ⟨1104383237436409484042093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 736255491624272989361395 1104383237436409484042093)
                  ·
                    refine ⟨414143714038653556515785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1104383237436409484042093 414143714038653556515785)
                    ·
                      rfl

theorem cell22_1209813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 3, 4, 1, 3].length) (baseStart_1209813 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1209813 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1209813 prefixEnd_1209813 := by exact prefixLift 1209813
  have htrace : WordTrace (prefixWord ++ tailWord_1209813) baseStart_1209813 baseEnd_1209813 := by
    simpa [prefixWord, tailWord_1209813, baseEnd_1209813] using wordTrace_append hprefix tailTrace_1209813
  have hstable : (prefixWord ++ tailWord_1209813).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1209813).length < 2 ^ (prefixWord ++ tailWord_1209813).sum := by decide
  have hdescent : baseEnd_1209813 < baseStart_1209813 := by decide
  rcases family_descends (prefixWord ++ tailWord_1209813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1209839 : List Nat := [1, 1, 2, 1, 4, 1, 4, 1, 3, 4]
def baseStart_1209839 : Nat := 118140960795 + 1209839 * 2 ^ 59
def prefixEnd_1209839 : Nat := 4983230072969 + 3 ^ 40 * 1209839 * 2
def baseEnd_1209839 : Nat := 414152614369998155365705

theorem tailTrace_1209839 : CollatzResearch.WordTrace tailWord_1209839 prefixEnd_1209839 414152614369998155365705 := by
  unfold tailWord_1209839
  simp only [CollatzResearch.WordTrace]
  refine ⟨44126453463967401896128571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29417635642644934597419047 44126453463967401896128571)
  ·
    refine ⟨66189680195951102844192857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44126453463967401896128571 66189680195951102844192857)
    ·
      refine ⟨49642260146963327133144643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66189680195951102844192857 49642260146963327133144643)
      ·
        refine ⟨74463390220444990699716965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49642260146963327133144643 74463390220444990699716965)
        ·
          refine ⟨13961885666333435756196931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 74463390220444990699716965 13961885666333435756196931)
          ·
            refine ⟨20942828499500153634295397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13961885666333435756196931 20942828499500153634295397)
            ·
              refine ⟨3926780343656278806430387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20942828499500153634295397 3926780343656278806430387)
              ·
                refine ⟨5890170515484418209645581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3926780343656278806430387 5890170515484418209645581)
                ·
                  refine ⟨2208813943306656828617093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5890170515484418209645581 2208813943306656828617093)
                  ·
                    refine ⟨414152614369998155365705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2208813943306656828617093 414152614369998155365705)
                    ·
                      rfl

theorem cell22_1209839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4, 1, 3, 4].length) (baseStart_1209839 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1209839 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1209839 prefixEnd_1209839 := by exact prefixLift 1209839
  have htrace : WordTrace (prefixWord ++ tailWord_1209839) baseStart_1209839 baseEnd_1209839 := by
    simpa [prefixWord, tailWord_1209839, baseEnd_1209839] using wordTrace_append hprefix tailTrace_1209839
  have hstable : (prefixWord ++ tailWord_1209839).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1209839).length < 2 ^ (prefixWord ++ tailWord_1209839).sum := by decide
  have hdescent : baseEnd_1209839 < baseStart_1209839 := by decide
  rcases family_descends (prefixWord ++ tailWord_1209839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1209860 : List Nat := [2, 3, 2, 3, 3, 1, 1, 2, 5]
def baseStart_1209860 : Nat := 118140960795 + 1209860 * 2 ^ 59
def prefixEnd_1209860 : Nat := 4983230072969 + 3 ^ 40 * 1209860 * 2
def baseEnd_1209860 : Nat := 138053267699720366863547

theorem tailTrace_1209860 : CollatzResearch.WordTrace tailWord_1209860 prefixEnd_1209860 138053267699720366863547 := by
  unfold tailWord_1209860
  simp only [CollatzResearch.WordTrace]
  refine ⟨22063609698445661241321517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29418146264594214988428689 22063609698445661241321517)
  ·
    refine ⟨8273853636917122965495569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22063609698445661241321517 8273853636917122965495569)
    ·
      refine ⟨6205390227687842224121677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8273853636917122965495569 6205390227687842224121677)
      ·
        refine ⟨2327021335382940834045629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6205390227687842224121677 2327021335382940834045629)
        ·
          refine ⟨872633000768602812767111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2327021335382940834045629 872633000768602812767111)
          ·
            refine ⟨1308949501152904219150667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 872633000768602812767111 1308949501152904219150667)
            ·
              refine ⟨1963424251729356328726001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1308949501152904219150667 1963424251729356328726001)
              ·
                refine ⟨1472568188797017246544501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1963424251729356328726001 1472568188797017246544501)
                ·
                  refine ⟨138053267699720366863547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1472568188797017246544501 138053267699720366863547)
                  ·
                    rfl

theorem cell22_1209860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 1, 2, 5].length) (baseStart_1209860 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1209860 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1209860 prefixEnd_1209860 := by exact prefixLift 1209860
  have htrace : WordTrace (prefixWord ++ tailWord_1209860) baseStart_1209860 baseEnd_1209860 := by
    simpa [prefixWord, tailWord_1209860, baseEnd_1209860] using wordTrace_append hprefix tailTrace_1209860
  have hstable : (prefixWord ++ tailWord_1209860).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1209860).length < 2 ^ (prefixWord ++ tailWord_1209860).sum := by decide
  have hdescent : baseEnd_1209860 < baseStart_1209860 := by decide
  rcases family_descends (prefixWord ++ tailWord_1209860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1209884 : List Nat := [2, 2, 3, 1, 2, 1, 1, 1, 3, 6]
def baseStart_1209884 : Nat := 118140960795 + 1209884 * 2 ^ 59
def prefixEnd_1209884 : Nat := 4983230072969 + 3 ^ 40 * 1209884 * 2
def baseEnd_1209884 : Nat := 414168018789633037990567

theorem tailTrace_1209884 : CollatzResearch.WordTrace tailWord_1209884 prefixEnd_1209884 414168018789633037990567 := by
  unfold tailWord_1209884
  simp only [CollatzResearch.WordTrace]
  refine ⟨22064047374402187290758353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29418729832536249721011137 22064047374402187290758353)
  ·
    refine ⟨16548035530801640468068765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22064047374402187290758353 16548035530801640468068765)
    ·
      refine ⟨6205513324050615175525787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16548035530801640468068765 6205513324050615175525787)
      ·
        refine ⟨9308269986075922763288681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6205513324050615175525787 9308269986075922763288681)
        ·
          refine ⟨6981202489556942072466511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9308269986075922763288681 6981202489556942072466511)
          ·
            refine ⟨10471803734335413108699767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6981202489556942072466511 10471803734335413108699767)
            ·
              refine ⟨15707705601503119663049651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10471803734335413108699767 15707705601503119663049651)
              ·
                refine ⟨23561558402254679494574477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15707705601503119663049651 23561558402254679494574477)
                ·
                  refine ⟨8835584400845504810465429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23561558402254679494574477 8835584400845504810465429)
                  ·
                    refine ⟨414168018789633037990567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8835584400845504810465429 414168018789633037990567)
                    ·
                      rfl

theorem cell22_1209884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 1, 3, 6].length) (baseStart_1209884 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1209884 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1209884 prefixEnd_1209884 := by exact prefixLift 1209884
  have htrace : WordTrace (prefixWord ++ tailWord_1209884) baseStart_1209884 baseEnd_1209884 := by
    simpa [prefixWord, tailWord_1209884, baseEnd_1209884] using wordTrace_append hprefix tailTrace_1209884
  have hstable : (prefixWord ++ tailWord_1209884).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1209884).length < 2 ^ (prefixWord ++ tailWord_1209884).sum := by decide
  have hdescent : baseEnd_1209884 < baseStart_1209884 := by decide
  rcases family_descends (prefixWord ++ tailWord_1209884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1209916 : List Nat := [2, 2, 2, 2, 4, 2, 8]
def baseStart_1209916 : Nat := 118140960795 + 1209916 * 2 ^ 59
def prefixEnd_1209916 : Nat := 4983230072969 + 3 ^ 40 * 1209916 * 2
def baseEnd_1209916 : Nat := 15339961964577615599647

theorem tailTrace_1209916 : CollatzResearch.WordTrace tailWord_1209916 prefixEnd_1209916 15339961964577615599647 := by
  unfold tailWord_1209916
  simp only [CollatzResearch.WordTrace]
  refine ⟨22064630942344222023340801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29419507923125629364454401 22064630942344222023340801)
  ·
    refine ⟨16548473206758166517505601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22064630942344222023340801 16548473206758166517505601)
    ·
      refine ⟨12411354905068624888129201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16548473206758166517505601 12411354905068624888129201)
      ·
        refine ⟨9308516178801468666096901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12411354905068624888129201 9308516178801468666096901)
        ·
          refine ⟨1745346783525275374893169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9308516178801468666096901 1745346783525275374893169)
          ·
            refine ⟨1309010087643956531169877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1745346783525275374893169 1309010087643956531169877)
            ·
              refine ⟨15339961964577615599647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1309010087643956531169877 15339961964577615599647)
              ·
                rfl

theorem cell22_1209916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 8].length) (baseStart_1209916 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1209916 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1209916 prefixEnd_1209916 := by exact prefixLift 1209916
  have htrace : WordTrace (prefixWord ++ tailWord_1209916) baseStart_1209916 baseEnd_1209916 := by
    simpa [prefixWord, tailWord_1209916, baseEnd_1209916] using wordTrace_append hprefix tailTrace_1209916
  have hstable : (prefixWord ++ tailWord_1209916).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1209916).length < 2 ^ (prefixWord ++ tailWord_1209916).sum := by decide
  have hdescent : baseEnd_1209916 < baseStart_1209916 := by decide
  rcases family_descends (prefixWord ++ tailWord_1209916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1209933 : List Nat := [1, 6, 1, 1, 3, 1, 2, 7]
def baseStart_1209933 : Nat := 118140960795 + 1209933 * 2 ^ 59
def prefixEnd_1209933 : Nat := 4983230072969 + 3 ^ 40 * 1209933 * 2
def baseEnd_1209933 : Nat := 46020532499001471501713

theorem tailTrace_1209933 : CollatzResearch.WordTrace tailWord_1209933 prefixEnd_1209933 46020532499001471501713 := by
  unfold tailWord_1209933
  simp only [CollatzResearch.WordTrace]
  refine ⟨44129881925626855950050453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29419921283751237300033635 44129881925626855950050453)
  ·
    refine ⟨2068588215263758872658615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 44129881925626855950050453 2068588215263758872658615)
    ·
      refine ⟨3102882322895638308987923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2068588215263758872658615 3102882322895638308987923)
      ·
        refine ⟨4654323484343457463481885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3102882322895638308987923 4654323484343457463481885)
        ·
          refine ⟨1745371306628796548805707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4654323484343457463481885 1745371306628796548805707)
          ·
            refine ⟨2618056959943194823208561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1745371306628796548805707 2618056959943194823208561)
            ·
              refine ⟨1963542719957396117406421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2618056959943194823208561 1963542719957396117406421)
              ·
                refine ⟨46020532499001471501713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1963542719957396117406421 46020532499001471501713)
                ·
                  rfl

theorem cell22_1209933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 2, 7].length) (baseStart_1209933 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1209933 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1209933 prefixEnd_1209933 := by exact prefixLift 1209933
  have htrace : WordTrace (prefixWord ++ tailWord_1209933) baseStart_1209933 baseEnd_1209933 := by
    simpa [prefixWord, tailWord_1209933, baseEnd_1209933] using wordTrace_append hprefix tailTrace_1209933
  have hstable : (prefixWord ++ tailWord_1209933).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1209933).length < 2 ^ (prefixWord ++ tailWord_1209933).sum := by decide
  have hdescent : baseEnd_1209933 < baseStart_1209933 := by decide
  rcases family_descends (prefixWord ++ tailWord_1209933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1209991 : List Nat := [1, 1, 4, 2, 1, 3, 1, 2, 3, 4]
def baseStart_1209991 : Nat := 118140960795 + 1209991 * 2 ^ 59
def prefixEnd_1209991 : Nat := 4983230072969 + 3 ^ 40 * 1209991 * 2
def baseEnd_1209991 : Nat := 414204647076320425565239

theorem tailTrace_1209991 : CollatzResearch.WordTrace tailWord_1209991 prefixEnd_1209991 414204647076320425565239 := by
  unfold tailWord_1209991
  simp only [CollatzResearch.WordTrace]
  refine ⟨44131997359416731855661827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29421331572944487903774551 44131997359416731855661827)
  ·
    refine ⟨66197996039125097783492741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44131997359416731855661827 66197996039125097783492741)
    ·
      refine ⟨12412124257335955834404889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 66197996039125097783492741 12412124257335955834404889)
      ·
        refine ⟨9309093193001966875803667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12412124257335955834404889 9309093193001966875803667)
        ·
          refine ⟨13963639789502950313705501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9309093193001966875803667 13963639789502950313705501)
          ·
            refine ⟨5236364921063606367639563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13963639789502950313705501 5236364921063606367639563)
            ·
              refine ⟨7854547381595409551459345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5236364921063606367639563 7854547381595409551459345)
              ·
                refine ⟨5890910536196557163594509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7854547381595409551459345 5890910536196557163594509)
                ·
                  refine ⟨2209091451073708936347941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5890910536196557163594509 2209091451073708936347941)
                  ·
                    refine ⟨414204647076320425565239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2209091451073708936347941 414204647076320425565239)
                    ·
                      rfl

theorem cell22_1209991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 2, 3, 4].length) (baseStart_1209991 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1209991 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1209991 prefixEnd_1209991 := by exact prefixLift 1209991
  have htrace : WordTrace (prefixWord ++ tailWord_1209991) baseStart_1209991 baseEnd_1209991 := by
    simpa [prefixWord, tailWord_1209991, baseEnd_1209991] using wordTrace_append hprefix tailTrace_1209991
  have hstable : (prefixWord ++ tailWord_1209991).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1209991).length < 2 ^ (prefixWord ++ tailWord_1209991).sum := by decide
  have hdescent : baseEnd_1209991 < baseStart_1209991 := by decide
  rcases family_descends (prefixWord ++ tailWord_1209991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1210021 : List Nat := [1, 3, 1, 2, 1, 2, 4, 2, 1, 5]
def baseStart_1210021 : Nat := 118140960795 + 1210021 * 2 ^ 59
def prefixEnd_1210021 : Nat := 4983230072969 + 3 ^ 40 * 1210021 * 2
def baseEnd_1210021 : Nat := 414214916689410347315147

theorem tailTrace_1210021 : CollatzResearch.WordTrace tailWord_1210021 prefixEnd_1210021 414214916689410347315147 := by
  unfold tailWord_1210021
  simp only [CollatzResearch.WordTrace]
  refine ⟨44133091549308046979253917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29422061032872031319502611 44133091549308046979253917)
  ·
    refine ⟨16549909330990517617220219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44133091549308046979253917 16549909330990517617220219)
    ·
      refine ⟨24824863996485776425830329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16549909330990517617220219 24824863996485776425830329)
      ·
        refine ⟨18618647997364332319372747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24824863996485776425830329 18618647997364332319372747)
        ·
          refine ⟨27927971996046498479059121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18618647997364332319372747 27927971996046498479059121)
          ·
            refine ⟨20945978997034873859294341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27927971996046498479059121 20945978997034873859294341)
            ·
              refine ⟨3927371061944038848617689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20945978997034873859294341 3927371061944038848617689)
              ·
                refine ⟨2945528296458029136463267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3927371061944038848617689 2945528296458029136463267)
                ·
                  refine ⟨4418292444687043704694901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2945528296458029136463267 4418292444687043704694901)
                  ·
                    refine ⟨414214916689410347315147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4418292444687043704694901 414214916689410347315147)
                    ·
                      rfl

theorem cell22_1210021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 2, 1, 5].length) (baseStart_1210021 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1210021 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1210021 prefixEnd_1210021 := by exact prefixLift 1210021
  have htrace : WordTrace (prefixWord ++ tailWord_1210021) baseStart_1210021 baseEnd_1210021 := by
    simpa [prefixWord, tailWord_1210021, baseEnd_1210021] using wordTrace_append hprefix tailTrace_1210021
  have hstable : (prefixWord ++ tailWord_1210021).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1210021).length < 2 ^ (prefixWord ++ tailWord_1210021).sum := by decide
  have hdescent : baseEnd_1210021 < baseStart_1210021 := by decide
  rcases family_descends (prefixWord ++ tailWord_1210021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1210055 : List Nat := [1, 1, 4, 1, 1, 1, 7, 1, 2, 3]
def baseStart_1210055 : Nat := 118140960795 + 1210055 * 2 ^ 59
def prefixEnd_1210055 : Nat := 4983230072969 + 3 ^ 40 * 1210055 * 2
def baseEnd_1210055 : Nat := 414226555584245591965043

theorem tailTrace_1210055 : CollatzResearch.WordTrace tailWord_1210055 prefixEnd_1210055 414226555584245591965043 := by
  unfold tailWord_1210055
  simp only [CollatzResearch.WordTrace]
  refine ⟨44134331631184870785991619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29422887754123247190661079 44134331631184870785991619)
  ·
    refine ⟨66201497446777306178987429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44134331631184870785991619 66201497446777306178987429)
    ·
      refine ⟨12412780771270744908560143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 66201497446777306178987429 12412780771270744908560143)
      ·
        refine ⟨18619171156906117362840215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12412780771270744908560143 18619171156906117362840215)
        ·
          refine ⟨27928756735359176044260323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18619171156906117362840215 27928756735359176044260323)
          ·
            refine ⟨41893135103038764066390485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27928756735359176044260323 41893135103038764066390485)
            ·
              refine ⟨981870353977471032806027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 41893135103038764066390485 981870353977471032806027)
              ·
                refine ⟨1472805530966206549209041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 981870353977471032806027 1472805530966206549209041)
                ·
                  refine ⟨1104604148224654911906781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1472805530966206549209041 1104604148224654911906781)
                  ·
                    refine ⟨414226555584245591965043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1104604148224654911906781 414226555584245591965043)
                    ·
                      rfl

theorem cell22_1210055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 7, 1, 2, 3].length) (baseStart_1210055 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1210055 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1210055 prefixEnd_1210055 := by exact prefixLift 1210055
  have htrace : WordTrace (prefixWord ++ tailWord_1210055) baseStart_1210055 baseEnd_1210055 := by
    simpa [prefixWord, tailWord_1210055, baseEnd_1210055] using wordTrace_append hprefix tailTrace_1210055
  have hstable : (prefixWord ++ tailWord_1210055).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1210055).length < 2 ^ (prefixWord ++ tailWord_1210055).sum := by decide
  have hdescent : baseEnd_1210055 < baseStart_1210055 := by decide
  rcases family_descends (prefixWord ++ tailWord_1210055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1210068 : List Nat := [2, 4, 1, 3, 1, 2, 1, 8]
def baseStart_1210068 : Nat := 118140960795 + 1210068 * 2 ^ 59
def prefixEnd_1210068 : Nat := 4983230072969 + 3 ^ 40 * 1210068 * 2
def baseEnd_1210068 : Nat := 46025667305546432376667

theorem tailTrace_1210068 : CollatzResearch.WordTrace tailWord_1210068 prefixEnd_1210068 46025667305546432376667 := by
  unfold tailWord_1210068
  simp only [CollatzResearch.WordTrace]
  refine ⟨22067402890068887003107429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29423203853425182670809905 22067402890068887003107429)
  ·
    refine ⟨4137638041887916313082643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22067402890068887003107429 4137638041887916313082643)
    ·
      refine ⟨6206457062831874469623965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4137638041887916313082643 6206457062831874469623965)
      ·
        refine ⟨2327421398561952926108987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6206457062831874469623965 2327421398561952926108987)
        ·
          refine ⟨3491132097842929389163481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2327421398561952926108987 3491132097842929389163481)
          ·
            refine ⟨2618349073382197041872611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3491132097842929389163481 2618349073382197041872611)
            ·
              refine ⟨3927523610073295562808917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2618349073382197041872611 3927523610073295562808917)
              ·
                refine ⟨46025667305546432376667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3927523610073295562808917 46025667305546432376667)
                ·
                  rfl

theorem cell22_1210068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 1, 8].length) (baseStart_1210068 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1210068 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1210068 prefixEnd_1210068 := by exact prefixLift 1210068
  have htrace : WordTrace (prefixWord ++ tailWord_1210068) baseStart_1210068 baseEnd_1210068 := by
    simpa [prefixWord, tailWord_1210068, baseEnd_1210068] using wordTrace_append hprefix tailTrace_1210068
  have hstable : (prefixWord ++ tailWord_1210068).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1210068).length < 2 ^ (prefixWord ++ tailWord_1210068).sum := by decide
  have hdescent : baseEnd_1210068 < baseStart_1210068 := by decide
  rcases family_descends (prefixWord ++ tailWord_1210068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1210111 : List Nat := [1, 1, 2, 2, 1, 3, 2, 3, 2, 5]
def baseStart_1210111 : Nat := 118140960795 + 1210111 * 2 ^ 59
def prefixEnd_1210111 : Nat := 4983230072969 + 3 ^ 40 * 1210111 * 2
def baseEnd_1210111 : Nat := 414245725528680112564871

theorem tailTrace_1210111 : CollatzResearch.WordTrace tailWord_1210111 prefixEnd_1210111 414245725528680112564871 := by
  unfold tailWord_1210111
  simp only [CollatzResearch.WordTrace]
  refine ⟨44136374118981992350030187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29424249412654661566686791 44136374118981992350030187)
  ·
    refine ⟨66204561178472988525045281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44136374118981992350030187 66204561178472988525045281)
    ·
      refine ⟨49653420883854741393783961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66204561178472988525045281 49653420883854741393783961)
      ·
        refine ⟨37240065662891056045337971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49653420883854741393783961 37240065662891056045337971)
        ·
          refine ⟨55860098494336584068006957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37240065662891056045337971 55860098494336584068006957)
          ·
            refine ⟨20947536935376219025502609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55860098494336584068006957 20947536935376219025502609)
            ·
              refine ⟨15710652701532164269126957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20947536935376219025502609 15710652701532164269126957)
              ·
                refine ⟨5891494763074561600922609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15710652701532164269126957 5891494763074561600922609)
                ·
                  refine ⟨4418621072305921200691957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5891494763074561600922609 4418621072305921200691957)
                  ·
                    refine ⟨414245725528680112564871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4418621072305921200691957 414245725528680112564871)
                    ·
                      rfl

theorem cell22_1210111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 3, 2, 5].length) (baseStart_1210111 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1210111 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1210111 prefixEnd_1210111 := by exact prefixLift 1210111
  have htrace : WordTrace (prefixWord ++ tailWord_1210111) baseStart_1210111 baseEnd_1210111 := by
    simpa [prefixWord, tailWord_1210111, baseEnd_1210111] using wordTrace_append hprefix tailTrace_1210111
  have hstable : (prefixWord ++ tailWord_1210111).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1210111).length < 2 ^ (prefixWord ++ tailWord_1210111).sum := by decide
  have hdescent : baseEnd_1210111 < baseStart_1210111 := by decide
  rcases family_descends (prefixWord ++ tailWord_1210111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1210207 : List Nat := [1, 1, 2, 3, 1, 6, 1, 2, 2, 3]
def baseStart_1210207 : Nat := 118140960795 + 1210207 * 2 ^ 59
def prefixEnd_1210207 : Nat := 4983230072969 + 3 ^ 40 * 1210207 * 2
def baseEnd_1210207 : Nat := 414278588290567862164577

theorem tailTrace_1210207 : CollatzResearch.WordTrace tailWord_1210207 prefixEnd_1210207 414278588290567862164577 := by
  unfold tailWord_1210207
  simp only [CollatzResearch.WordTrace]
  refine ⟨44139875526634200745524875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29426583684422800497016583 44139875526634200745524875)
  ·
    refine ⟨66209813289951301118287313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44139875526634200745524875 66209813289951301118287313)
    ·
      refine ⟨49657359967463475838715485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66209813289951301118287313 49657359967463475838715485)
      ·
        refine ⟨18621509987798803439518307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49657359967463475838715485 18621509987798803439518307)
        ·
          refine ⟨27932264981698205159277461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18621509987798803439518307 27932264981698205159277461)
          ·
            refine ⟨1309324921017103366841131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 27932264981698205159277461 1309324921017103366841131)
            ·
              refine ⟨1963987381525655050261697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1309324921017103366841131 1963987381525655050261697)
              ·
                refine ⟨1472990536144241287696273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1963987381525655050261697 1472990536144241287696273)
                ·
                  refine ⟨1104742902108180965772205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1472990536144241287696273 1104742902108180965772205)
                  ·
                    refine ⟨414278588290567862164577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1104742902108180965772205 414278588290567862164577)
                    ·
                      rfl

theorem cell22_1210207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 1, 2, 2, 3].length) (baseStart_1210207 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1210207 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1210207 prefixEnd_1210207 := by exact prefixLift 1210207
  have htrace : WordTrace (prefixWord ++ tailWord_1210207) baseStart_1210207 baseEnd_1210207 := by
    simpa [prefixWord, tailWord_1210207, baseEnd_1210207] using wordTrace_append hprefix tailTrace_1210207
  have hstable : (prefixWord ++ tailWord_1210207).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1210207).length < 2 ^ (prefixWord ++ tailWord_1210207).sum := by decide
  have hdescent : baseEnd_1210207 < baseStart_1210207 := by decide
  rcases family_descends (prefixWord ++ tailWord_1210207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1210368 : List Nat := [2, 1, 1, 2, 1, 1, 1, 4, 1, 8]
def baseStart_1210368 : Nat := 118140960795 + 1210368 * 2 ^ 59
def prefixEnd_1210368 : Nat := 4983230072969 + 3 ^ 40 * 1210368 * 2
def baseEnd_1210368 : Nat := 414333701880817108889083

theorem tailTrace_1210368 : CollatzResearch.WordTrace tailWord_1210368 prefixEnd_1210368 414333701880817108889083 := by
  unfold tailWord_1210368
  simp only [CollatzResearch.WordTrace]
  refine ⟨22072873839525462621067879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29430498452700616828090505 22072873839525462621067879)
  ·
    refine ⟨33109310759288193931601819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22072873839525462621067879 33109310759288193931601819)
    ·
      refine ⟨49663966138932290897402729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33109310759288193931601819 49663966138932290897402729)
      ·
        refine ⟨37247974604199218173052047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49663966138932290897402729 37247974604199218173052047)
        ·
          refine ⟨55871961906298827259578071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37247974604199218173052047 55871961906298827259578071)
          ·
            refine ⟨83807942859448240889367107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55871961906298827259578071 83807942859448240889367107)
            ·
              refine ⟨125711914289172361334050661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83807942859448240889367107 125711914289172361334050661)
              ·
                refine ⟨23570983929219817750134499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 125711914289172361334050661 23570983929219817750134499)
                ·
                  refine ⟨35356475893829726625201749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23570983929219817750134499 35356475893829726625201749)
                  ·
                    refine ⟨414333701880817108889083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 35356475893829726625201749 414333701880817108889083)
                    ·
                      rfl

theorem cell22_1210368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 4, 1, 8].length) (baseStart_1210368 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1210368 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1210368 prefixEnd_1210368 := by exact prefixLift 1210368
  have htrace : WordTrace (prefixWord ++ tailWord_1210368) baseStart_1210368 baseEnd_1210368 := by
    simpa [prefixWord, tailWord_1210368, baseEnd_1210368] using wordTrace_append hprefix tailTrace_1210368
  have hstable : (prefixWord ++ tailWord_1210368).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1210368).length < 2 ^ (prefixWord ++ tailWord_1210368).sum := by decide
  have hdescent : baseEnd_1210368 < baseStart_1210368 := by decide
  rcases family_descends (prefixWord ++ tailWord_1210368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1210372 : List Nat := [2, 3, 2, 4, 1, 1, 9]
def baseStart_1210372 : Nat := 118140960795 + 1210372 * 2 ^ 59
def prefixEnd_1210372 : Nat := 4983230072969 + 3 ^ 40 * 1210372 * 2
def baseEnd_1210372 : Nat := 15345743376391201177373

theorem tailTrace_1210372 : CollatzResearch.WordTrace tailWord_1210372 prefixEnd_1210372 15345743376391201177373 := by
  unfold tailWord_1210372
  simp only [CollatzResearch.WordTrace]
  refine ⟨22072946785518216962640685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29430595714024289283520913 22072946785518216962640685)
  ·
    refine ⟨8277355044569331360990257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22072946785518216962640685 8277355044569331360990257)
    ·
      refine ⟨6208016283426998520742693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8277355044569331360990257 6208016283426998520742693)
      ·
        refine ⟨1164003053142562222639255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6208016283426998520742693 1164003053142562222639255)
        ·
          refine ⟨1746004579713843333958883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1164003053142562222639255 1746004579713843333958883)
          ·
            refine ⟨2619006869570765000938325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1746004579713843333958883 2619006869570765000938325)
            ·
              refine ⟨15345743376391201177373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2619006869570765000938325 15345743376391201177373)
              ·
                rfl

theorem cell22_1210372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 9].length) (baseStart_1210372 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1210372 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1210372 prefixEnd_1210372 := by exact prefixLift 1210372
  have htrace : WordTrace (prefixWord ++ tailWord_1210372) baseStart_1210372 baseEnd_1210372 := by
    simpa [prefixWord, tailWord_1210372, baseEnd_1210372] using wordTrace_append hprefix tailTrace_1210372
  have hstable : (prefixWord ++ tailWord_1210372).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1210372).length < 2 ^ (prefixWord ++ tailWord_1210372).sum := by decide
  have hdescent : baseEnd_1210372 < baseStart_1210372 := by decide
  rcases family_descends (prefixWord ++ tailWord_1210372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1210464 : List Nat := [2, 1, 1, 3, 2, 5, 1, 2, 1, 4]
def baseStart_1210464 : Nat := 118140960795 + 1210464 * 2 ^ 59
def prefixEnd_1210464 : Nat := 4983230072969 + 3 ^ 40 * 1210464 * 2
def baseEnd_1210464 : Nat := 414366564642704858488789

theorem tailTrace_1210464 : CollatzResearch.WordTrace tailWord_1210464 prefixEnd_1210464 414366564642704858488789 := by
  unfold tailWord_1210464
  simp only [CollatzResearch.WordTrace]
  refine ⟨22074624543351566818815223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29432832724468755758420297 22074624543351566818815223)
  ·
    refine ⟨33111936815027350228222835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22074624543351566818815223 33111936815027350228222835)
    ·
      refine ⟨49667905222541025342334253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33111936815027350228222835 49667905222541025342334253)
      ·
        refine ⟨18625464458452884503375345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49667905222541025342334253 18625464458452884503375345)
        ·
          refine ⟨13969098343839663377531509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18625464458452884503375345 13969098343839663377531509)
          ·
            refine ⟨1309602969734968441643579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13969098343839663377531509 1309602969734968441643579)
            ·
              refine ⟨1964404454602452662465369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1309602969734968441643579 1964404454602452662465369)
              ·
                refine ⟨1473303340951839496849027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1964404454602452662465369 1473303340951839496849027)
                ·
                  refine ⟨2209955011427759245273541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1473303340951839496849027 2209955011427759245273541)
                  ·
                    refine ⟨414366564642704858488789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2209955011427759245273541 414366564642704858488789)
                    ·
                      rfl

theorem cell22_1210464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 1, 2, 1, 4].length) (baseStart_1210464 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1210464 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1210464 prefixEnd_1210464 := by exact prefixLift 1210464
  have htrace : WordTrace (prefixWord ++ tailWord_1210464) baseStart_1210464 baseEnd_1210464 := by
    simpa [prefixWord, tailWord_1210464, baseEnd_1210464] using wordTrace_append hprefix tailTrace_1210464
  have hstable : (prefixWord ++ tailWord_1210464).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1210464).length < 2 ^ (prefixWord ++ tailWord_1210464).sum := by decide
  have hdescent : baseEnd_1210464 < baseStart_1210464 := by decide
  rcases family_descends (prefixWord ++ tailWord_1210464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1210477 : List Nat := [1, 5, 1, 1, 2, 1, 3, 2, 1, 5]
def baseStart_1210477 : Nat := 118140960795 + 1210477 * 2 ^ 59
def prefixEnd_1210477 : Nat := 4983230072969 + 3 ^ 40 * 1210477 * 2
def baseEnd_1210477 : Nat := 414371014808377157913749

theorem tailTrace_1210477 : CollatzResearch.WordTrace tailWord_1210477 prefixEnd_1210477 414371014808377157913749 := by
  unfold tailWord_1210477
  simp only [CollatzResearch.WordTrace]
  refine ⟨44149723235656036857853685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29433148823770691238569123 44149723235656036857853685)
  ·
    refine ⟨4139036553342753455423783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 44149723235656036857853685 4139036553342753455423783)
    ·
      refine ⟨6208554830014130183135675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4139036553342753455423783 6208554830014130183135675)
      ·
        refine ⟨9312832245021195274703513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6208554830014130183135675 9312832245021195274703513)
        ·
          refine ⟨6984624183765896456027635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9312832245021195274703513 6984624183765896456027635)
          ·
            refine ⟨10476936275648844684041453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6984624183765896456027635 10476936275648844684041453)
            ·
              refine ⟨3928851103368316756515545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10476936275648844684041453 3928851103368316756515545)
              ·
                refine ⟨2946638327526237567386659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3928851103368316756515545 2946638327526237567386659)
                ·
                  refine ⟨4419957491289356351079989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2946638327526237567386659 4419957491289356351079989)
                  ·
                    refine ⟨414371014808377157913749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4419957491289356351079989 414371014808377157913749)
                    ·
                      rfl

theorem cell22_1210477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 3, 2, 1, 5].length) (baseStart_1210477 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1210477 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1210477 prefixEnd_1210477 := by exact prefixLift 1210477
  have htrace : WordTrace (prefixWord ++ tailWord_1210477) baseStart_1210477 baseEnd_1210477 := by
    simpa [prefixWord, tailWord_1210477, baseEnd_1210477] using wordTrace_append hprefix tailTrace_1210477
  have hstable : (prefixWord ++ tailWord_1210477).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1210477).length < 2 ^ (prefixWord ++ tailWord_1210477).sum := by decide
  have hdescent : baseEnd_1210477 < baseStart_1210477 := by decide
  rcases family_descends (prefixWord ++ tailWord_1210477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1210492 : List Nat := [2, 2, 2, 1, 1, 4, 2, 2, 2, 4]
def baseStart_1210492 : Nat := 118140960795 + 1210492 * 2 ^ 59
def prefixEnd_1210492 : Nat := 4983230072969 + 3 ^ 40 * 1210492 * 2
def baseEnd_1210492 : Nat := 414376149614922118788703

theorem tailTrace_1210492 : CollatzResearch.WordTrace tailWord_1210492 prefixEnd_1210492 414376149614922118788703 := by
  unfold tailWord_1210492
  simp only [CollatzResearch.WordTrace]
  refine ⟨22075135165300847209824865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29433513553734462946433153 22075135165300847209824865)
  ·
    refine ⟨16556351373975635407368649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22075135165300847209824865 16556351373975635407368649)
    ·
      refine ⟨12417263530481726555526487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16556351373975635407368649 12417263530481726555526487)
      ·
        refine ⟨18625895295722589833289731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12417263530481726555526487 18625895295722589833289731)
        ·
          refine ⟨27938842943583884749934597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18625895295722589833289731 27938842943583884749934597)
          ·
            refine ⟨5238533051921978390612737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27938842943583884749934597 5238533051921978390612737)
            ·
              refine ⟨3928899788941483792959553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5238533051921978390612737 3928899788941483792959553)
              ·
                refine ⟨2946674841706112844719665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3928899788941483792959553 2946674841706112844719665)
                ·
                  refine ⟨2210006131279584633539749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2946674841706112844719665 2210006131279584633539749)
                  ·
                    refine ⟨414376149614922118788703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2210006131279584633539749 414376149614922118788703)
                    ·
                      rfl

theorem cell22_1210492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 2, 2, 2, 4].length) (baseStart_1210492 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1210492 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1210492 prefixEnd_1210492 := by exact prefixLift 1210492
  have htrace : WordTrace (prefixWord ++ tailWord_1210492) baseStart_1210492 baseEnd_1210492 := by
    simpa [prefixWord, tailWord_1210492, baseEnd_1210492] using wordTrace_append hprefix tailTrace_1210492
  have hstable : (prefixWord ++ tailWord_1210492).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1210492).length < 2 ^ (prefixWord ++ tailWord_1210492).sum := by decide
  have hdescent : baseEnd_1210492 < baseStart_1210492 := by decide
  rcases family_descends (prefixWord ++ tailWord_1210492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1210556 : List Nat := [2, 2, 2, 3, 3, 1, 2, 1, 3, 3]
def baseStart_1210556 : Nat := 118140960795 + 1210556 * 2 ^ 59
def prefixEnd_1210556 : Nat := 4983230072969 + 3 ^ 40 * 1210556 * 2
def baseEnd_1210556 : Nat := 414398058122847285188507

theorem tailTrace_1210556 : CollatzResearch.WordTrace tailWord_1210556 prefixEnd_1210556 414398058122847285188507 := by
  unfold tailWord_1210556
  simp only [CollatzResearch.WordTrace]
  refine ⟨22076302301184916674989761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29435069734913222233319681 22076302301184916674989761)
  ·
    refine ⟨16557226725888687506242321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22076302301184916674989761 16557226725888687506242321)
    ·
      refine ⟨12417920044416515629681741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16557226725888687506242321 12417920044416515629681741)
      ·
        refine ⟨4656720016656193361130653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12417920044416515629681741 4656720016656193361130653)
        ·
          refine ⟨1746270006246072510423995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4656720016656193361130653 1746270006246072510423995)
          ·
            refine ⟨2619405009369108765635993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1746270006246072510423995 2619405009369108765635993)
            ·
              refine ⟨1964553757026831574226995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2619405009369108765635993 1964553757026831574226995)
              ·
                refine ⟨2946830635540247361340493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1964553757026831574226995 2946830635540247361340493)
                ·
                  refine ⟨1105061488327592760502685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2946830635540247361340493 1105061488327592760502685)
                  ·
                    refine ⟨414398058122847285188507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1105061488327592760502685 414398058122847285188507)
                    ·
                      rfl

theorem cell22_1210556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 2, 1, 3, 3].length) (baseStart_1210556 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1210556 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1210556 prefixEnd_1210556 := by exact prefixLift 1210556
  have htrace : WordTrace (prefixWord ++ tailWord_1210556) baseStart_1210556 baseEnd_1210556 := by
    simpa [prefixWord, tailWord_1210556, baseEnd_1210556] using wordTrace_append hprefix tailTrace_1210556
  have hstable : (prefixWord ++ tailWord_1210556).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1210556).length < 2 ^ (prefixWord ++ tailWord_1210556).sum := by decide
  have hdescent : baseEnd_1210556 < baseStart_1210556 := by decide
  rcases family_descends (prefixWord ++ tailWord_1210556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1210614 : List Nat := [5, 1, 1, 1, 1, 1, 5, 1, 6]
def baseStart_1210614 : Nat := 118140960795 + 1210614 * 2 ^ 59
def prefixEnd_1210614 : Nat := 4983230072969 + 3 ^ 40 * 1210614 * 2
def baseEnd_1210614 : Nat := 138139304236051489079443

theorem tailTrace_1210614 : CollatzResearch.WordTrace tailWord_1210614 prefixEnd_1210614 138139304236051489079443 := by
  unfold tailWord_1210614
  simp only [CollatzResearch.WordTrace]
  refine ⟨2759670002259981828474431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 29436480024106472837060597 2759670002259981828474431)
  ·
    refine ⟨4139505003389972742711647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2759670002259981828474431 4139505003389972742711647)
    ·
      refine ⟨6209257505084959114067471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4139505003389972742711647 6209257505084959114067471)
      ·
        refine ⟨9313886257627438671101207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6209257505084959114067471 9313886257627438671101207)
        ·
          refine ⟨13970829386441158006651811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9313886257627438671101207 13970829386441158006651811)
          ·
            refine ⟨20956244079661737009977717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13970829386441158006651811 20956244079661737009977717)
            ·
              refine ⟨1964647882468287844685411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20956244079661737009977717 1964647882468287844685411)
              ·
                refine ⟨2946971823702431767028117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1964647882468287844685411 2946971823702431767028117)
                ·
                  refine ⟨138139304236051489079443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2946971823702431767028117 138139304236051489079443)
                  ·
                    rfl

theorem cell22_1210614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 5, 1, 6].length) (baseStart_1210614 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1210614 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1210614 prefixEnd_1210614 := by exact prefixLift 1210614
  have htrace : WordTrace (prefixWord ++ tailWord_1210614) baseStart_1210614 baseEnd_1210614 := by
    simpa [prefixWord, tailWord_1210614, baseEnd_1210614] using wordTrace_append hprefix tailTrace_1210614
  have hstable : (prefixWord ++ tailWord_1210614).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1210614).length < 2 ^ (prefixWord ++ tailWord_1210614).sum := by decide
  have hdescent : baseEnd_1210614 < baseStart_1210614 := by decide
  rcases family_descends (prefixWord ++ tailWord_1210614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1210627 : List Nat := [1, 1, 1, 3, 2, 3, 1, 2, 4, 4]
def baseStart_1210627 : Nat := 118140960795 + 1210627 * 2 ^ 59
def prefixEnd_1210627 : Nat := 4983230072969 + 3 ^ 40 * 1210627 * 2
def baseEnd_1210627 : Nat := 414422362873826766663289

theorem tailTrace_1210627 : CollatzResearch.WordTrace tailWord_1210627 prefixEnd_1210627 414422362873826766663289 := by
  unfold tailWord_1210627
  simp only [CollatzResearch.WordTrace]
  refine ⟨44155194185112612475814135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29436796123408408317209423 44155194185112612475814135)
  ·
    refine ⟨66232791277668918713721203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44155194185112612475814135 66232791277668918713721203)
    ·
      refine ⟨99349186916503378070581805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66232791277668918713721203 99349186916503378070581805)
      ·
        refine ⟨37255945093688766776468177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 99349186916503378070581805 37255945093688766776468177)
        ·
          refine ⟨27941958820266575082351133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37255945093688766776468177 27941958820266575082351133)
          ·
            refine ⟨10478234557599965655881675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27941958820266575082351133 10478234557599965655881675)
            ·
              refine ⟨15717351836399948483822513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10478234557599965655881675 15717351836399948483822513)
              ·
                refine ⟨11788013877299961362866885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15717351836399948483822513 11788013877299961362866885)
                ·
                  refine ⟨2210252601993742755537541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11788013877299961362866885 2210252601993742755537541)
                  ·
                    refine ⟨414422362873826766663289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2210252601993742755537541 414422362873826766663289)
                    ·
                      rfl

theorem cell22_1210627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 2, 4, 4].length) (baseStart_1210627 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1210627 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1210627 prefixEnd_1210627 := by exact prefixLift 1210627
  have htrace : WordTrace (prefixWord ++ tailWord_1210627) baseStart_1210627 baseEnd_1210627 := by
    simpa [prefixWord, tailWord_1210627, baseEnd_1210627] using wordTrace_append hprefix tailTrace_1210627
  have hstable : (prefixWord ++ tailWord_1210627).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1210627).length < 2 ^ (prefixWord ++ tailWord_1210627).sum := by decide
  have hdescent : baseEnd_1210627 < baseStart_1210627 := by decide
  rcases family_descends (prefixWord ++ tailWord_1210627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1210676 : List Nat := [2, 5, 1, 1, 1, 4, 1, 7]
def baseStart_1210676 : Nat := 118140960795 + 1210676 * 2 ^ 59
def prefixEnd_1210676 : Nat := 4983230072969 + 3 ^ 40 * 1210676 * 2
def baseEnd_1210676 : Nat := 46048792952800774687571

theorem tailTrace_1210676 : CollatzResearch.WordTrace tailWord_1210676 prefixEnd_1210676 46048792952800774687571 := by
  unfold tailWord_1210676
  simp only [CollatzResearch.WordTrace]
  refine ⟨22078490680967546922173941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29437987574623395896231921 22078490680967546922173941)
  ·
    refine ⟨2069858501340707523953807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 22078490680967546922173941 2069858501340707523953807)
    ·
      refine ⟨3104787752011061285930711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2069858501340707523953807 3104787752011061285930711)
      ·
        refine ⟨4657181628016591928896067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3104787752011061285930711 4657181628016591928896067)
        ·
          refine ⟨6985772442024887893344101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4657181628016591928896067 6985772442024887893344101)
          ·
            refine ⟨1309832332879666480002019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6985772442024887893344101 1309832332879666480002019)
            ·
              refine ⟨1964748499319499720003029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1309832332879666480002019 1964748499319499720003029)
              ·
                refine ⟨46048792952800774687571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1964748499319499720003029 46048792952800774687571)
                ·
                  rfl

theorem cell22_1210676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 1, 7].length) (baseStart_1210676 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1210676 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1210676 prefixEnd_1210676 := by exact prefixLift 1210676
  have htrace : WordTrace (prefixWord ++ tailWord_1210676) baseStart_1210676 baseEnd_1210676 := by
    simpa [prefixWord, tailWord_1210676, baseEnd_1210676] using wordTrace_append hprefix tailTrace_1210676
  have hstable : (prefixWord ++ tailWord_1210676).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1210676).length < 2 ^ (prefixWord ++ tailWord_1210676).sum := by decide
  have hdescent : baseEnd_1210676 < baseStart_1210676 := by decide
  rcases family_descends (prefixWord ++ tailWord_1210676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1210708 : List Nat := [2, 4, 1, 1, 2, 2, 1, 5, 1, 3]
def baseStart_1210708 : Nat := 118140960795 + 1210708 * 2 ^ 59
def prefixEnd_1210708 : Nat := 4983230072969 + 3 ^ 40 * 1210708 * 2
def baseEnd_1210708 : Nat := 414450090829169555388041

theorem tailTrace_1210708 : CollatzResearch.WordTrace tailWord_1210708 prefixEnd_1210708 414450090829169555388041 := by
  unfold tailWord_1210708
  simp only [CollatzResearch.WordTrace]
  refine ⟨22079074248909581654756389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29438765665212775539675185 22079074248909581654756389)
  ·
    refine ⟨4139826421670546560266823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22079074248909581654756389 4139826421670546560266823)
    ·
      refine ⟨6209739632505819840400235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4139826421670546560266823 6209739632505819840400235)
      ·
        refine ⟨9314609448758729760600353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6209739632505819840400235 9314609448758729760600353)
        ·
          refine ⟨6985957086569047320450265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9314609448758729760600353 6985957086569047320450265)
          ·
            refine ⟨5239467814926785490337699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6985957086569047320450265 5239467814926785490337699)
            ·
              refine ⟨7859201722390178235506549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5239467814926785490337699 7859201722390178235506549)
              ·
                refine ⟨736800161474079209578739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7859201722390178235506549 736800161474079209578739)
                ·
                  refine ⟨1105200242211118814368109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 736800161474079209578739 1105200242211118814368109)
                  ·
                    refine ⟨414450090829169555388041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1105200242211118814368109 414450090829169555388041)
                    ·
                      rfl

theorem cell22_1210708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 5, 1, 3].length) (baseStart_1210708 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1210708 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1210708 prefixEnd_1210708 := by exact prefixLift 1210708
  have htrace : WordTrace (prefixWord ++ tailWord_1210708) baseStart_1210708 baseEnd_1210708 := by
    simpa [prefixWord, tailWord_1210708, baseEnd_1210708] using wordTrace_append hprefix tailTrace_1210708
  have hstable : (prefixWord ++ tailWord_1210708).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1210708).length < 2 ^ (prefixWord ++ tailWord_1210708).sum := by decide
  have hdescent : baseEnd_1210708 < baseStart_1210708 := by decide
  rcases family_descends (prefixWord ++ tailWord_1210708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1210749 : List Nat := [1, 4, 1, 1, 2, 3, 2, 2, 6]
def baseStart_1210749 : Nat := 118140960795 + 1210749 * 2 ^ 59
def prefixEnd_1210749 : Nat := 4983230072969 + 3 ^ 40 * 1210749 * 2
def baseEnd_1210749 : Nat := 138154708655686371704305

theorem tailTrace_1210749 : CollatzResearch.WordTrace tailWord_1210749 prefixEnd_1210749 138154708655686371704305 := by
  unfold tailWord_1210749
  simp only [CollatzResearch.WordTrace]
  refine ⟨44159643890670627311755301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29439762593780418207836867 44159643890670627311755301)
  ·
    refine ⟨8279933229500742620954119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44159643890670627311755301 8279933229500742620954119)
    ·
      refine ⟨12419899844251113931431179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8279933229500742620954119 12419899844251113931431179)
      ·
        refine ⟨18629849766376670897146769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12419899844251113931431179 18629849766376670897146769)
        ·
          refine ⟨13972387324782503172860077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18629849766376670897146769 13972387324782503172860077)
          ·
            refine ⟨5239645246793438689822529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13972387324782503172860077 5239645246793438689822529)
            ·
              refine ⟨3929733935095079017366897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5239645246793438689822529 3929733935095079017366897)
              ·
                refine ⟨2947300451321309263025173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3929733935095079017366897 2947300451321309263025173)
                ·
                  refine ⟨138154708655686371704305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2947300451321309263025173 138154708655686371704305)
                  ·
                    rfl

theorem cell22_1210749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 2, 2, 6].length) (baseStart_1210749 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1210749 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1210749 prefixEnd_1210749 := by exact prefixLift 1210749
  have htrace : WordTrace (prefixWord ++ tailWord_1210749) baseStart_1210749 baseEnd_1210749 := by
    simpa [prefixWord, tailWord_1210749, baseEnd_1210749] using wordTrace_append hprefix tailTrace_1210749
  have hstable : (prefixWord ++ tailWord_1210749).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1210749).length < 2 ^ (prefixWord ++ tailWord_1210749).sum := by decide
  have hdescent : baseEnd_1210749 < baseStart_1210749 := by decide
  rcases family_descends (prefixWord ++ tailWord_1210749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1210783 : List Nat := [1, 1, 2, 5, 1, 1, 5, 2, 4]
def baseStart_1210783 : Nat := 118140960795 + 1210783 * 2 ^ 59
def prefixEnd_1210783 : Nat := 4983230072969 + 3 ^ 40 * 1210783 * 2
def baseEnd_1210783 : Nat := 138158588287298119920937

theorem tailTrace_1210783 : CollatzResearch.WordTrace tailWord_1210783 prefixEnd_1210783 138158588287298119920937 := by
  unfold tailWord_1210783
  simp only [CollatzResearch.WordTrace]
  refine ⟨44160883972547451118493003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29440589315031634078995335 44160883972547451118493003)
  ·
    refine ⟨66241325958821176677739505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44160883972547451118493003 66241325958821176677739505)
    ·
      refine ⟨49680994469115882508304629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66241325958821176677739505 49680994469115882508304629)
      ·
        refine ⟨4657593231479613985153559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 49680994469115882508304629 4657593231479613985153559)
        ·
          refine ⟨6986389847219420977730339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4657593231479613985153559 6986389847219420977730339)
          ·
            refine ⟨10479584770829131466595509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6986389847219420977730339 10479584770829131466595509)
            ·
              refine ⟨982461072265231074993329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10479584770829131466595509 982461072265231074993329)
              ·
                refine ⟨736845804198923306244997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 982461072265231074993329 736845804198923306244997)
                ·
                  refine ⟨138158588287298119920937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 736845804198923306244997 138158588287298119920937)
                  ·
                    rfl

theorem cell22_1210783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 5, 2, 4].length) (baseStart_1210783 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1210783 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1210783 prefixEnd_1210783 := by exact prefixLift 1210783
  have htrace : WordTrace (prefixWord ++ tailWord_1210783) baseStart_1210783 baseEnd_1210783 := by
    simpa [prefixWord, tailWord_1210783, baseEnd_1210783] using wordTrace_append hprefix tailTrace_1210783
  have hstable : (prefixWord ++ tailWord_1210783).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1210783).length < 2 ^ (prefixWord ++ tailWord_1210783).sum := by decide
  have hdescent : baseEnd_1210783 < baseStart_1210783 := by decide
  rcases family_descends (prefixWord ++ tailWord_1210783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1210834 : List Nat := [3, 2, 2, 4, 2, 1, 2, 2, 4]
def baseStart_1210834 : Nat := 118140960795 + 1210834 * 2 ^ 59
def prefixEnd_1210834 : Nat := 4983230072969 + 3 ^ 40 * 1210834 * 2
def baseEnd_1210834 : Nat := 138164407734715742245885

theorem tailTrace_1210834 : CollatzResearch.WordTrace tailWord_1210834 prefixEnd_1210834 138164407734715742245885 := by
  unfold tailWord_1210834
  simp only [CollatzResearch.WordTrace]
  refine ⟨11040686023840671707149889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29441829396908457885733037 11040686023840671707149889)
  ·
    refine ⟨8280514517880503780362417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11040686023840671707149889 8280514517880503780362417)
    ·
      refine ⟨6210385888410377835271813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8280514517880503780362417 6210385888410377835271813)
      ·
        refine ⟨1164447354076945844113465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6210385888410377835271813 1164447354076945844113465)
        ·
          refine ⟨873335515557709383085099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1164447354076945844113465 873335515557709383085099)
          ·
            refine ⟨1310003273336564074627649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 873335515557709383085099 1310003273336564074627649)
            ·
              refine ⟨982502455002423055970737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1310003273336564074627649 982502455002423055970737)
              ·
                refine ⟨736876841251817291978053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 982502455002423055970737 736876841251817291978053)
                ·
                  refine ⟨138164407734715742245885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 736876841251817291978053 138164407734715742245885)
                  ·
                    rfl

theorem cell22_1210834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 2, 2, 4].length) (baseStart_1210834 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1210834 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1210834 prefixEnd_1210834 := by exact prefixLift 1210834
  have htrace : WordTrace (prefixWord ++ tailWord_1210834) baseStart_1210834 baseEnd_1210834 := by
    simpa [prefixWord, tailWord_1210834, baseEnd_1210834] using wordTrace_append hprefix tailTrace_1210834
  have hstable : (prefixWord ++ tailWord_1210834).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1210834).length < 2 ^ (prefixWord ++ tailWord_1210834).sum := by decide
  have hdescent : baseEnd_1210834 < baseStart_1210834 := by decide
  rcases family_descends (prefixWord ++ tailWord_1210834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1210856 : List Nat := [2, 1, 4, 1, 1, 3, 2, 3, 5]
def baseStart_1210856 : Nat := 118140960795 + 1210856 * 2 ^ 59
def prefixEnd_1210856 : Nat := 4983230072969 + 3 ^ 40 * 1210856 * 2
def baseEnd_1210856 : Nat := 138166918084582167562529

theorem tailTrace_1210856 : CollatzResearch.WordTrace tailWord_1210856 prefixEnd_1210856 138166918084582167562529 := by
  unfold tailWord_1210856
  simp only [CollatzResearch.WordTrace]
  refine ⟨22081773250641492292950211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29442364334188656390600281 22081773250641492292950211)
  ·
    refine ⟨33122659875962238439425317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22081773250641492292950211 33122659875962238439425317)
    ·
      refine ⟨6210498726742919707392247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33122659875962238439425317 6210498726742919707392247)
      ·
        refine ⟨9315748090114379561088371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6210498726742919707392247 9315748090114379561088371)
        ·
          refine ⟨13973622135171569341632557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9315748090114379561088371 13973622135171569341632557)
          ·
            refine ⟨5240108300689338503112209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13973622135171569341632557 5240108300689338503112209)
            ·
              refine ⟨3930081225517003877334157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5240108300689338503112209 3930081225517003877334157)
              ·
                refine ⟨1473780459568876454000309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3930081225517003877334157 1473780459568876454000309)
                ·
                  refine ⟨138166918084582167562529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1473780459568876454000309 138166918084582167562529)
                  ·
                    rfl

theorem cell22_1210856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 2, 3, 5].length) (baseStart_1210856 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1210856 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1210856 prefixEnd_1210856 := by exact prefixLift 1210856
  have htrace : WordTrace (prefixWord ++ tailWord_1210856) baseStart_1210856 baseEnd_1210856 := by
    simpa [prefixWord, tailWord_1210856, baseEnd_1210856] using wordTrace_append hprefix tailTrace_1210856
  have hstable : (prefixWord ++ tailWord_1210856).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1210856).length < 2 ^ (prefixWord ++ tailWord_1210856).sum := by decide
  have hdescent : baseEnd_1210856 < baseStart_1210856 := by decide
  rcases family_descends (prefixWord ++ tailWord_1210856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1210901 : List Nat := [1, 3, 2, 1, 3, 1, 4, 1, 6]
def baseStart_1210901 : Nat := 118140960795 + 1210901 * 2 ^ 59
def prefixEnd_1210901 : Nat := 4983230072969 + 3 ^ 40 * 1210901 * 2
def baseEnd_1210901 : Nat := 138172052891127128437483

theorem tailTrace_1210901 : CollatzResearch.WordTrace tailWord_1210901 prefixEnd_1210901 138172052891127128437483 := by
  unfold tailWord_1210901
  simp only [CollatzResearch.WordTrace]
  refine ⟨44165187786119957271288557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29443458524079971514192371 44165187786119957271288557)
  ·
    refine ⟨16561945419794983976733209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44165187786119957271288557 16561945419794983976733209)
    ·
      refine ⟨12421459064846237982549907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16561945419794983976733209 12421459064846237982549907)
      ·
        refine ⟨18632188597269356973824861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12421459064846237982549907 18632188597269356973824861)
        ·
          refine ⟨6987070723976008865184323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18632188597269356973824861 6987070723976008865184323)
          ·
            refine ⟨10480606085964013297776485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6987070723976008865184323 10480606085964013297776485)
            ·
              refine ⟨1965113641118252493333091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10480606085964013297776485 1965113641118252493333091)
              ·
                refine ⟨2947670461677378739999637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1965113641118252493333091 2947670461677378739999637)
                ·
                  refine ⟨138172052891127128437483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2947670461677378739999637 138172052891127128437483)
                  ·
                    rfl

theorem cell22_1210901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 4, 1, 6].length) (baseStart_1210901 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1210901 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1210901 prefixEnd_1210901 := by exact prefixLift 1210901
  have htrace : WordTrace (prefixWord ++ tailWord_1210901) baseStart_1210901 baseEnd_1210901 := by
    simpa [prefixWord, tailWord_1210901, baseEnd_1210901] using wordTrace_append hprefix tailTrace_1210901
  have hstable : (prefixWord ++ tailWord_1210901).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1210901).length < 2 ^ (prefixWord ++ tailWord_1210901).sum := by decide
  have hdescent : baseEnd_1210901 < baseStart_1210901 := by decide
  rcases family_descends (prefixWord ++ tailWord_1210901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1210920 : List Nat := [2, 1, 5, 2, 1, 2, 2, 2, 1, 4]
def baseStart_1210920 : Nat := 118140960795 + 1210920 * 2 ^ 59
def prefixEnd_1210920 : Nat := 4983230072969 + 3 ^ 40 * 1210920 * 2
def baseEnd_1210920 : Nat := 414522662761671669087391

theorem tailTrace_1210920 : CollatzResearch.WordTrace tailWord_1210920 prefixEnd_1210920 414522662761671669087391 := by
  unfold tailWord_1210920
  simp only [CollatzResearch.WordTrace]
  refine ⟨22082940386525561758115107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29443920515367415677486809 22082940386525561758115107)
  ·
    refine ⟨33124410579788342637172661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22082940386525561758115107 33124410579788342637172661)
    ·
      refine ⟨3105413491855157122234937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 33124410579788342637172661 3105413491855157122234937)
      ·
        refine ⟨2329060118891367841676203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3105413491855157122234937 2329060118891367841676203)
        ·
          refine ⟨3493590178337051762514305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2329060118891367841676203 3493590178337051762514305)
          ·
            refine ⟨2620192633752788821885729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3493590178337051762514305 2620192633752788821885729)
            ·
              refine ⟨1965144475314591616414297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2620192633752788821885729 1965144475314591616414297)
              ·
                refine ⟨1473858356485943712310723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1965144475314591616414297 1473858356485943712310723)
                ·
                  refine ⟨2210787534728915568466085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1473858356485943712310723 2210787534728915568466085)
                  ·
                    refine ⟨414522662761671669087391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2210787534728915568466085 414522662761671669087391)
                    ·
                      rfl

theorem cell22_1210920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 2, 2, 1, 4].length) (baseStart_1210920 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1210920 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1210920 prefixEnd_1210920 := by exact prefixLift 1210920
  have htrace : WordTrace (prefixWord ++ tailWord_1210920) baseStart_1210920 baseEnd_1210920 := by
    simpa [prefixWord, tailWord_1210920, baseEnd_1210920] using wordTrace_append hprefix tailTrace_1210920
  have hstable : (prefixWord ++ tailWord_1210920).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1210920).length < 2 ^ (prefixWord ++ tailWord_1210920).sum := by decide
  have hdescent : baseEnd_1210920 < baseStart_1210920 := by decide
  rcases family_descends (prefixWord ++ tailWord_1210920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1210931 : List Nat := [1, 1, 1, 2, 4, 2, 2, 3, 2, 4]
def baseStart_1210931 : Nat := 118140960795 + 1210931 * 2 ^ 59
def prefixEnd_1210931 : Nat := 4983230072969 + 3 ^ 40 * 1210931 * 2
def baseEnd_1210931 : Nat := 414526428286471307062357

theorem tailTrace_1210931 : CollatzResearch.WordTrace tailWord_1210931 prefixEnd_1210931 414526428286471307062357 := by
  unfold tailWord_1210931
  simp only [CollatzResearch.WordTrace]
  refine ⟨44166281976011272394880647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29444187984007514929920431 44166281976011272394880647)
  ·
    refine ⟨66249422964016908592320971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44166281976011272394880647 66249422964016908592320971)
    ·
      refine ⟨99374134446025362888481457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66249422964016908592320971 99374134446025362888481457)
      ·
        refine ⟨74530600834519022166361093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99374134446025362888481457 74530600834519022166361093)
        ·
          refine ⟨13974487656472316656192705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 74530600834519022166361093 13974487656472316656192705)
          ·
            refine ⟨10480865742354237492144529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13974487656472316656192705 10480865742354237492144529)
            ·
              refine ⟨7860649306765678119108397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10480865742354237492144529 7860649306765678119108397)
              ·
                refine ⟨2947743490037129294665649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7860649306765678119108397 2947743490037129294665649)
                ·
                  refine ⟨2210807617527846970999237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2947743490037129294665649 2210807617527846970999237)
                  ·
                    refine ⟨414526428286471307062357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2210807617527846970999237 414526428286471307062357)
                    ·
                      rfl

theorem cell22_1210931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 3, 2, 4].length) (baseStart_1210931 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1210931 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1210931 prefixEnd_1210931 := by exact prefixLift 1210931
  have htrace : WordTrace (prefixWord ++ tailWord_1210931) baseStart_1210931 baseEnd_1210931 := by
    simpa [prefixWord, tailWord_1210931, baseEnd_1210931] using wordTrace_append hprefix tailTrace_1210931
  have hstable : (prefixWord ++ tailWord_1210931).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1210931).length < 2 ^ (prefixWord ++ tailWord_1210931).sum := by decide
  have hdescent : baseEnd_1210931 < baseStart_1210931 := by decide
  rcases family_descends (prefixWord ++ tailWord_1210931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1211008 : List Nat := [2, 1, 1, 2, 1, 6, 2, 2, 5]
def baseStart_1211008 : Nat := 118140960795 + 1211008 * 2 ^ 59
def prefixEnd_1211008 : Nat := 4983230072969 + 3 ^ 40 * 1211008 * 2
def baseEnd_1211008 : Nat := 138184262320022924295707

theorem tailTrace_1211008 : CollatzResearch.WordTrace tailWord_1211008 prefixEnd_1211008 138184262320022924295707 := by
  unfold tailWord_1211008
  simp only [CollatzResearch.WordTrace]
  refine ⟨22084545198366157272716839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29446060264488209696955785 22084545198366157272716839)
  ·
    refine ⟨33126817797549235909075259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22084545198366157272716839 33126817797549235909075259)
    ·
      refine ⟨49690226696323853863612889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33126817797549235909075259 49690226696323853863612889)
      ·
        refine ⟨37267670022242890397709667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49690226696323853863612889 37267670022242890397709667)
        ·
          refine ⟨55901505033364335596564501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37267670022242890397709667 55901505033364335596564501)
          ·
            refine ⟨2620383048438953231088961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 55901505033364335596564501 2620383048438953231088961)
            ·
              refine ⟨1965287286329214923316721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2620383048438953231088961 1965287286329214923316721)
              ·
                refine ⟨1473965464746911192487541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1965287286329214923316721 1473965464746911192487541)
                ·
                  refine ⟨138184262320022924295707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1473965464746911192487541 138184262320022924295707)
                  ·
                    rfl

theorem cell22_1211008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 2, 2, 5].length) (baseStart_1211008 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1211008 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1211008 prefixEnd_1211008 := by exact prefixLift 1211008
  have htrace : WordTrace (prefixWord ++ tailWord_1211008) baseStart_1211008 baseEnd_1211008 := by
    simpa [prefixWord, tailWord_1211008, baseEnd_1211008] using wordTrace_append hprefix tailTrace_1211008
  have hstable : (prefixWord ++ tailWord_1211008).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1211008).length < 2 ^ (prefixWord ++ tailWord_1211008).sum := by decide
  have hdescent : baseEnd_1211008 < baseStart_1211008 := by decide
  rcases family_descends (prefixWord ++ tailWord_1211008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1211012 : List Nat := [2, 3, 2, 1, 3, 2, 1, 4, 1, 3]
def baseStart_1211012 : Nat := 118140960795 + 1211012 * 2 ^ 59
def prefixEnd_1211012 : Nat := 4983230072969 + 3 ^ 40 * 1211012 * 2
def baseEnd_1211012 : Nat := 414554156241814095787109

theorem tailTrace_1211012 : CollatzResearch.WordTrace tailWord_1211012 prefixEnd_1211012 414554156241814095787109 := by
  unfold tailWord_1211012
  simp only [CollatzResearch.WordTrace]
  refine ⟨22084618144358911614289645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29446157525811882152386193 22084618144358911614289645)
  ·
    refine ⟨8281731804134591855358617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22084618144358911614289645 8281731804134591855358617)
    ·
      refine ⟨6211298853100943891518963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8281731804134591855358617 6211298853100943891518963)
      ·
        refine ⟨9316948279651415837278445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6211298853100943891518963 9316948279651415837278445)
        ·
          refine ⟨3493855604869280938979417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9316948279651415837278445 3493855604869280938979417)
          ·
            refine ⟨2620391703651960704234563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3493855604869280938979417 2620391703651960704234563)
            ·
              refine ⟨3930587555477941056351845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2620391703651960704234563 3930587555477941056351845)
              ·
                refine ⟨736985166652113948065971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3930587555477941056351845 736985166652113948065971)
                ·
                  refine ⟨1105477749978170922098957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 736985166652113948065971 1105477749978170922098957)
                  ·
                    refine ⟨414554156241814095787109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1105477749978170922098957 414554156241814095787109)
                    ·
                      rfl

theorem cell22_1211012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 1, 4, 1, 3].length) (baseStart_1211012 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1211012 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1211012 prefixEnd_1211012 := by exact prefixLift 1211012
  have htrace : WordTrace (prefixWord ++ tailWord_1211012) baseStart_1211012 baseEnd_1211012 := by
    simpa [prefixWord, tailWord_1211012, baseEnd_1211012] using wordTrace_append hprefix tailTrace_1211012
  have hstable : (prefixWord ++ tailWord_1211012).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1211012).length < 2 ^ (prefixWord ++ tailWord_1211012).sum := by decide
  have hdescent : baseEnd_1211012 < baseStart_1211012 := by decide
  rcases family_descends (prefixWord ++ tailWord_1211012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1211055 : List Nat := [1, 1, 2, 1, 2, 5, 4, 1, 1, 4]
def baseStart_1211055 : Nat := 118140960795 + 1211055 * 2 ^ 59
def prefixEnd_1211055 : Nat := 4983230072969 + 3 ^ 40 * 1211055 * 2
def baseEnd_1211055 : Nat := 414568876020576316961977

theorem tailTrace_1211055 : CollatzResearch.WordTrace tailWord_1211055 prefixEnd_1211055 414568876020576316961977 := by
  unfold tailWord_1211055
  simp only [CollatzResearch.WordTrace]
  refine ⟨44170804627562041572394619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29447203085041361048263079 44170804627562041572394619)
  ·
    refine ⟨66256206941343062358591929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44170804627562041572394619 66256206941343062358591929)
    ·
      refine ⟨49692155206007296768943947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66256206941343062358591929 49692155206007296768943947)
      ·
        refine ⟨74538232809010945153415921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49692155206007296768943947 74538232809010945153415921)
        ·
          refine ⟨55903674606758208865061941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74538232809010945153415921 55903674606758208865061941)
          ·
            refine ⟨5240969494383582081099557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 55903674606758208865061941 5240969494383582081099557)
            ·
              refine ⟨982681780196921640206167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5240969494383582081099557 982681780196921640206167)
              ·
                refine ⟨1474022670295382460309251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 982681780196921640206167 1474022670295382460309251)
                ·
                  refine ⟨2211034005443073690463877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1474022670295382460309251 2211034005443073690463877)
                  ·
                    refine ⟨414568876020576316961977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2211034005443073690463877 414568876020576316961977)
                    ·
                      rfl

theorem cell22_1211055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 4, 1, 1, 4].length) (baseStart_1211055 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1211055 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1211055 prefixEnd_1211055 := by exact prefixLift 1211055
  have htrace : WordTrace (prefixWord ++ tailWord_1211055) baseStart_1211055 baseEnd_1211055 := by
    simpa [prefixWord, tailWord_1211055, baseEnd_1211055] using wordTrace_append hprefix tailTrace_1211055
  have hstable : (prefixWord ++ tailWord_1211055).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1211055).length < 2 ^ (prefixWord ++ tailWord_1211055).sum := by decide
  have hdescent : baseEnd_1211055 < baseStart_1211055 := by decide
  rcases family_descends (prefixWord ++ tailWord_1211055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1211070 : List Nat := [4, 2, 1, 1, 2, 1, 1, 6, 4]
def baseStart_1211070 : Nat := 118140960795 + 1211070 * 2 ^ 59
def prefixEnd_1211070 : Nat := 4983230072969 + 3 ^ 40 * 1211070 * 2
def baseEnd_1211070 : Nat := 138191336942373759278977

theorem tailTrace_1211070 : CollatzResearch.WordTrace tailWord_1211070 prefixEnd_1211070 138191336942373759278977 := by
  unfold tailWord_1211070
  simp only [CollatzResearch.WordTrace]
  refine ⟨5521418965313462391773833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29447567815005132756127109 5521418965313462391773833)
  ·
    refine ⟨4141064223985096793830375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5521418965313462391773833 4141064223985096793830375)
    ·
      refine ⟨6211596335977645190745563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4141064223985096793830375 6211596335977645190745563)
      ·
        refine ⟨9317394503966467786118345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6211596335977645190745563 9317394503966467786118345)
        ·
          refine ⟨6988045877974850839588759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9317394503966467786118345 6988045877974850839588759)
          ·
            refine ⟨10482068816962276259383139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6988045877974850839588759 10482068816962276259383139)
            ·
              refine ⟨15723103225443414389074709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10482068816962276259383139 15723103225443414389074709)
              ·
                refine ⟨737020463692660049487877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 15723103225443414389074709 737020463692660049487877)
                ·
                  refine ⟨138191336942373759278977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 737020463692660049487877 138191336942373759278977)
                  ·
                    rfl

theorem cell22_1211070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 6, 4].length) (baseStart_1211070 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1211070 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1211070 prefixEnd_1211070 := by exact prefixLift 1211070
  have htrace : WordTrace (prefixWord ++ tailWord_1211070) baseStart_1211070 baseEnd_1211070 := by
    simpa [prefixWord, tailWord_1211070, baseEnd_1211070] using wordTrace_append hprefix tailTrace_1211070
  have hstable : (prefixWord ++ tailWord_1211070).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1211070).length < 2 ^ (prefixWord ++ tailWord_1211070).sum := by decide
  have hdescent : baseEnd_1211070 < baseStart_1211070 := by decide
  rcases family_descends (prefixWord ++ tailWord_1211070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1211100 : List Nat := [2, 2, 5, 1, 1, 1, 2, 1, 1, 6]
def baseStart_1211100 : Nat := 118140960795 + 1211100 * 2 ^ 59
def prefixEnd_1211100 : Nat := 4983230072969 + 3 ^ 40 * 1211100 * 2
def baseEnd_1211100 : Nat := 414584280440211199586839

theorem tailTrace_1211100 : CollatzResearch.WordTrace tailWord_1211100 prefixEnd_1211100 414584280440211199586839 := by
  unfold tailWord_1211100
  simp only [CollatzResearch.WordTrace]
  refine ⟨22086222956199507128891377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29448297274932676171855169 22086222956199507128891377)
  ·
    refine ⟨16564667217149630346668533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22086222956199507128891377 16564667217149630346668533)
    ·
      refine ⟨1552937551607777845000175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16564667217149630346668533 1552937551607777845000175)
      ·
        refine ⟨2329406327411666767500263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1552937551607777845000175 2329406327411666767500263)
        ·
          refine ⟨3494109491117500151250395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2329406327411666767500263 3494109491117500151250395)
          ·
            refine ⟨5241164236676250226875593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3494109491117500151250395 5241164236676250226875593)
            ·
              refine ⟨3930873177507187670156695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5241164236676250226875593 3930873177507187670156695)
              ·
                refine ⟨5896309766260781505235043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3930873177507187670156695 5896309766260781505235043)
                ·
                  refine ⟨8844464649391172257852565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5896309766260781505235043 8844464649391172257852565)
                  ·
                    refine ⟨414584280440211199586839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8844464649391172257852565 414584280440211199586839)
                    ·
                      rfl

theorem cell22_1211100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_1211100 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1211100 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1211100 prefixEnd_1211100 := by exact prefixLift 1211100
  have htrace : WordTrace (prefixWord ++ tailWord_1211100) baseStart_1211100 baseEnd_1211100 := by
    simpa [prefixWord, tailWord_1211100, baseEnd_1211100] using wordTrace_append hprefix tailTrace_1211100
  have hstable : (prefixWord ++ tailWord_1211100).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1211100).length < 2 ^ (prefixWord ++ tailWord_1211100).sum := by decide
  have hdescent : baseEnd_1211100 < baseStart_1211100 := by decide
  rcases family_descends (prefixWord ++ tailWord_1211100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1211113 : List Nat := [1, 2, 1, 1, 1, 2, 4, 2, 5, 3]
def baseStart_1211113 : Nat := 118140960795 + 1211113 * 2 ^ 59
def prefixEnd_1211113 : Nat := 4983230072969 + 3 ^ 40 * 1211113 * 2
def baseEnd_1211113 : Nat := 414588730605883499011799

theorem tailTrace_1211113 : CollatzResearch.WordTrace tailWord_1211113 prefixEnd_1211113 414588730605883499011799 := by
  unfold tailWord_1211113
  simp only [CollatzResearch.WordTrace]
  refine ⟨44172920061351917478005993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29448613374234611652003995 44172920061351917478005993)
  ·
    refine ⟨33129690046013938108504495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44172920061351917478005993 33129690046013938108504495)
    ·
      refine ⟨49694535069020907162756743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33129690046013938108504495 49694535069020907162756743)
      ·
        refine ⟨74541802603531360744135115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49694535069020907162756743 74541802603531360744135115)
        ·
          refine ⟨111812703905297041116202673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74541802603531360744135115 111812703905297041116202673)
          ·
            refine ⟨83859527928972780837152005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111812703905297041116202673 83859527928972780837152005)
            ·
              refine ⟨15723661486682396406966001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 83859527928972780837152005 15723661486682396406966001)
              ·
                refine ⟨11792746115011797305224501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15723661486682396406966001 11792746115011797305224501)
                ·
                  refine ⟨1105569948282355997364797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 11792746115011797305224501 1105569948282355997364797)
                  ·
                    refine ⟨414588730605883499011799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1105569948282355997364797 414588730605883499011799)
                    ·
                      rfl

theorem cell22_1211113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 2, 5, 3].length) (baseStart_1211113 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1211113 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1211113 prefixEnd_1211113 := by exact prefixLift 1211113
  have htrace : WordTrace (prefixWord ++ tailWord_1211113) baseStart_1211113 baseEnd_1211113 := by
    simpa [prefixWord, tailWord_1211113, baseEnd_1211113] using wordTrace_append hprefix tailTrace_1211113
  have hstable : (prefixWord ++ tailWord_1211113).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1211113).length < 2 ^ (prefixWord ++ tailWord_1211113).sum := by decide
  have hdescent : baseEnd_1211113 < baseStart_1211113 := by decide
  rcases family_descends (prefixWord ++ tailWord_1211113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1211130 : List Nat := [3, 1, 1, 1, 1, 3, 5, 1, 3, 3]
def baseStart_1211130 : Nat := 118140960795 + 1211130 * 2 ^ 59
def prefixEnd_1211130 : Nat := 4983230072969 + 3 ^ 40 * 1211130 * 2
def baseEnd_1211130 : Nat := 414594550053301121336747

theorem tailTrace_1211130 : CollatzResearch.WordTrace tailWord_1211130 prefixEnd_1211130 414594550053301121336747 := by
  unfold tailWord_1211130
  simp only [CollatzResearch.WordTrace]
  refine ⟨11043385025572582345343711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29449026734860219587583229 11043385025572582345343711)
  ·
    refine ⟨16565077538358873518015567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11043385025572582345343711 16565077538358873518015567)
    ·
      refine ⟨24847616307538310277023351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16565077538358873518015567 24847616307538310277023351)
      ·
        refine ⟨37271424461307465415535027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24847616307538310277023351 37271424461307465415535027)
        ·
          refine ⟨55907136691961198123302541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37271424461307465415535027 55907136691961198123302541)
          ·
            refine ⟨20965176259485449296238453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55907136691961198123302541 20965176259485449296238453)
            ·
              refine ⟨1965485274326760871522355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20965176259485449296238453 1965485274326760871522355)
              ·
                refine ⟨2948227911490141307283533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1965485274326760871522355 2948227911490141307283533)
                ·
                  refine ⟨1105585466808802990231325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2948227911490141307283533 1105585466808802990231325)
                  ·
                    refine ⟨414594550053301121336747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1105585466808802990231325 414594550053301121336747)
                    ·
                      rfl

theorem cell22_1211130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 5, 1, 3, 3].length) (baseStart_1211130 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1211130 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1211130 prefixEnd_1211130 := by exact prefixLift 1211130
  have htrace : WordTrace (prefixWord ++ tailWord_1211130) baseStart_1211130 baseEnd_1211130 := by
    simpa [prefixWord, tailWord_1211130, baseEnd_1211130] using wordTrace_append hprefix tailTrace_1211130
  have hstable : (prefixWord ++ tailWord_1211130).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1211130).length < 2 ^ (prefixWord ++ tailWord_1211130).sum := by decide
  have hdescent : baseEnd_1211130 < baseStart_1211130 := by decide
  rcases family_descends (prefixWord ++ tailWord_1211130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1211237 : List Nat := [1, 3, 1, 3, 1, 1, 5, 2, 2, 3]
def baseStart_1211237 : Nat := 118140960795 + 1211237 * 2 ^ 59
def prefixEnd_1211237 : Nat := 4983230072969 + 3 ^ 40 * 1211237 * 2
def baseEnd_1211237 : Nat := 414631178339988508911419

theorem tailTrace_1211237 : CollatzResearch.WordTrace tailWord_1211237 prefixEnd_1211237 414631178339988508911419 := by
  unfold tailWord_1211237
  simp only [CollatzResearch.WordTrace]
  refine ⟨44177442712902686655519965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29451628475268457770346643 44177442712902686655519965)
  ·
    refine ⟨16566541017338507495819987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44177442712902686655519965 16566541017338507495819987)
    ·
      refine ⟨24849811526007761243729981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16566541017338507495819987 24849811526007761243729981)
      ·
        refine ⟨9318679322252910466398743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24849811526007761243729981 9318679322252910466398743)
        ·
          refine ⟨13978018983379365699598115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9318679322252910466398743 13978018983379365699598115)
          ·
            refine ⟨20967028475069048549397173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13978018983379365699598115 20967028475069048549397173)
            ·
              refine ⟨1965658919537723301505985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20967028475069048549397173 1965658919537723301505985)
              ·
                refine ⟨1474244189653292476129489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1965658919537723301505985 1474244189653292476129489)
                ·
                  refine ⟨1105683142239969357097117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1474244189653292476129489 1105683142239969357097117)
                  ·
                    refine ⟨414631178339988508911419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1105683142239969357097117 414631178339988508911419)
                    ·
                      rfl

theorem cell22_1211237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 5, 2, 2, 3].length) (baseStart_1211237 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1211237 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1211237 prefixEnd_1211237 := by exact prefixLift 1211237
  have htrace : WordTrace (prefixWord ++ tailWord_1211237) baseStart_1211237 baseEnd_1211237 := by
    simpa [prefixWord, tailWord_1211237, baseEnd_1211237] using wordTrace_append hprefix tailTrace_1211237
  have hstable : (prefixWord ++ tailWord_1211237).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1211237).length < 2 ^ (prefixWord ++ tailWord_1211237).sum := by decide
  have hdescent : baseEnd_1211237 < baseStart_1211237 := by decide
  rcases family_descends (prefixWord ++ tailWord_1211237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1211254 : List Nat := [5, 1, 1, 3, 1, 3, 1, 1, 1, 5]
def baseStart_1211254 : Nat := 118140960795 + 1211254 * 2 ^ 59
def prefixEnd_1211254 : Nat := 4983230072969 + 3 ^ 40 * 1211254 * 2
def baseEnd_1211254 : Nat := 414636997787406131236367

theorem tailTrace_1211254 : CollatzResearch.WordTrace tailWord_1211254 prefixEnd_1211254 414636997787406131236367 := by
  unfold tailWord_1211254
  simp only [CollatzResearch.WordTrace]
  refine ⟨2761128922115068659930551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 29452041835894065705925877 2761128922115068659930551)
  ·
    refine ⟨4141693383172602989895827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2761128922115068659930551 4141693383172602989895827)
    ·
      refine ⟨6212540074758904484843741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4141693383172602989895827 6212540074758904484843741)
      ·
        refine ⟨2329702528034589181816403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6212540074758904484843741 2329702528034589181816403)
        ·
          refine ⟨3494553792051883772724605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2329702528034589181816403 3494553792051883772724605)
          ·
            refine ⟨1310457672019456414771727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3494553792051883772724605 1310457672019456414771727)
            ·
              refine ⟨1965686508029184622157591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1310457672019456414771727 1965686508029184622157591)
              ·
                refine ⟨2948529762043776933236387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1965686508029184622157591 2948529762043776933236387)
                ·
                  refine ⟨4422794643065665399854581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2948529762043776933236387 4422794643065665399854581)
                  ·
                    refine ⟨414636997787406131236367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4422794643065665399854581 414636997787406131236367)
                    ·
                      rfl

theorem cell22_1211254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 1, 1, 1, 5].length) (baseStart_1211254 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1211254 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1211254 prefixEnd_1211254 := by exact prefixLift 1211254
  have htrace : WordTrace (prefixWord ++ tailWord_1211254) baseStart_1211254 baseEnd_1211254 := by
    simpa [prefixWord, tailWord_1211254, baseEnd_1211254] using wordTrace_append hprefix tailTrace_1211254
  have hstable : (prefixWord ++ tailWord_1211254).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1211254).length < 2 ^ (prefixWord ++ tailWord_1211254).sum := by decide
  have hdescent : baseEnd_1211254 < baseStart_1211254 := by decide
  rcases family_descends (prefixWord ++ tailWord_1211254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1211263 : List Nat := [1, 1, 2, 2, 1, 1, 4, 2, 2, 6]
def baseStart_1211263 : Nat := 118140960795 + 1211263 * 2 ^ 59
def prefixEnd_1211263 : Nat := 4983230072969 + 3 ^ 40 * 1211263 * 2
def baseEnd_1211263 : Nat := 414640078671333107761339

theorem tailTrace_1211263 : CollatzResearch.WordTrace tailWord_1211263 prefixEnd_1211263 414640078671333107761339 := by
  unfold tailWord_1211263
  simp only [CollatzResearch.WordTrace]
  refine ⟨44178391010808493095966443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29452260673872328730644295 44178391010808493095966443)
  ·
    refine ⟨66267586516212739643949665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44178391010808493095966443 66267586516212739643949665)
    ·
      refine ⟨49700689887159554732962249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66267586516212739643949665 49700689887159554732962249)
      ·
        refine ⟨37275517415369666049721687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49700689887159554732962249 37275517415369666049721687)
        ·
          refine ⟨55913276123054499074582531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37275517415369666049721687 55913276123054499074582531)
          ·
            refine ⟨83869914184581748611873797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55913276123054499074582531 83869914184581748611873797)
            ·
              refine ⟨15725608909609077864726337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 83869914184581748611873797 15725608909609077864726337)
              ·
                refine ⟨11794206682206808398544753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15725608909609077864726337 11794206682206808398544753)
                ·
                  refine ⟨8845655011655106298908565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11794206682206808398544753 8845655011655106298908565)
                  ·
                    refine ⟨414640078671333107761339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8845655011655106298908565 414640078671333107761339)
                    ·
                      rfl

theorem cell22_1211263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 2, 2, 6].length) (baseStart_1211263 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1211263 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1211263 prefixEnd_1211263 := by exact prefixLift 1211263
  have htrace : WordTrace (prefixWord ++ tailWord_1211263) baseStart_1211263 baseEnd_1211263 := by
    simpa [prefixWord, tailWord_1211263, baseEnd_1211263] using wordTrace_append hprefix tailTrace_1211263
  have hstable : (prefixWord ++ tailWord_1211263).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1211263).length < 2 ^ (prefixWord ++ tailWord_1211263).sum := by decide
  have hdescent : baseEnd_1211263 < baseStart_1211263 := by decide
  rcases family_descends (prefixWord ++ tailWord_1211263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1211286 : List Nat := [5, 3, 1, 1, 1, 2, 1, 2, 2, 4]
def baseStart_1211286 : Nat := 118140960795 + 1211286 * 2 ^ 59
def prefixEnd_1211286 : Nat := 4983230072969 + 3 ^ 40 * 1211286 * 2
def baseEnd_1211286 : Nat := 414647952041368714436269

theorem tailTrace_1211286 : CollatzResearch.WordTrace tailWord_1211286 prefixEnd_1211286 414647952041368714436269 := by
  unfold tailWord_1211286
  simp only [CollatzResearch.WordTrace]
  refine ⟨2761201868107823001503357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 29452819926483445349369141 2761201868107823001503357)
  ·
    refine ⟨1035450700540433625563759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2761201868107823001503357 1035450700540433625563759)
    ·
      refine ⟨1553176050810650438345639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1035450700540433625563759 1553176050810650438345639)
      ·
        refine ⟨2329764076215975657518459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1553176050810650438345639 2329764076215975657518459)
        ·
          refine ⟨3494646114323963486277689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2329764076215975657518459 3494646114323963486277689)
          ·
            refine ⟨2620984585742972614708267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3494646114323963486277689 2620984585742972614708267)
            ·
              refine ⟨3931476878614458922062401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2620984585742972614708267 3931476878614458922062401)
              ·
                refine ⟨2948607658960844191546801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3931476878614458922062401 2948607658960844191546801)
                ·
                  refine ⟨2211455744220633143660101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2948607658960844191546801 2211455744220633143660101)
                  ·
                    refine ⟨414647952041368714436269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2211455744220633143660101 414647952041368714436269)
                    ·
                      rfl

theorem cell22_1211286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_1211286 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1211286 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1211286 prefixEnd_1211286 := by exact prefixLift 1211286
  have htrace : WordTrace (prefixWord ++ tailWord_1211286) baseStart_1211286 baseEnd_1211286 := by
    simpa [prefixWord, tailWord_1211286, baseEnd_1211286] using wordTrace_append hprefix tailTrace_1211286
  have hstable : (prefixWord ++ tailWord_1211286).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1211286).length < 2 ^ (prefixWord ++ tailWord_1211286).sum := by decide
  have hdescent : baseEnd_1211286 < baseStart_1211286 := by decide
  rcases family_descends (prefixWord ++ tailWord_1211286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1211295 : List Nat := [1, 1, 2, 5, 2, 1, 2, 1, 7]
def baseStart_1211295 : Nat := 118140960795 + 1211295 * 2 ^ 59
def prefixEnd_1211295 : Nat := 4983230072969 + 3 ^ 40 * 1211295 * 2
def baseEnd_1211295 : Nat := 138217010975098563653747

theorem tailTrace_1211295 : CollatzResearch.WordTrace tailWord_1211295 prefixEnd_1211295 138217010975098563653747 := by
  unfold tailWord_1211295
  simp only [CollatzResearch.WordTrace]
  refine ⟨44179558146692562561131339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29453038764461708374087559 44179558146692562561131339)
  ·
    refine ⟨66269337220038843841697009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44179558146692562561131339 66269337220038843841697009)
    ·
      refine ⟨49702002915029132881272757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66269337220038843841697009 49702002915029132881272757)
      ·
        refine ⟨4659562773283981207619321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 49702002915029132881272757 4659562773283981207619321)
        ·
          refine ⟨3494672079962985905714491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4659562773283981207619321 3494672079962985905714491)
          ·
            refine ⟨5242008119944478858571737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3494672079962985905714491 5242008119944478858571737)
            ·
              refine ⟨3931506089958359143928803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5242008119944478858571737 3931506089958359143928803)
              ·
                refine ⟨5897259134937538715893205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3931506089958359143928803 5897259134937538715893205)
                ·
                  refine ⟨138217010975098563653747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5897259134937538715893205 138217010975098563653747)
                  ·
                    rfl

theorem cell22_1211295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 2, 1, 7].length) (baseStart_1211295 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1211295 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1211295 prefixEnd_1211295 := by exact prefixLift 1211295
  have htrace : WordTrace (prefixWord ++ tailWord_1211295) baseStart_1211295 baseEnd_1211295 := by
    simpa [prefixWord, tailWord_1211295, baseEnd_1211295] using wordTrace_append hprefix tailTrace_1211295
  have hstable : (prefixWord ++ tailWord_1211295).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1211295).length < 2 ^ (prefixWord ++ tailWord_1211295).sum := by decide
  have hdescent : baseEnd_1211295 < baseStart_1211295 := by decide
  rcases family_descends (prefixWord ++ tailWord_1211295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1211350 : List Nat := [5, 2, 1, 1, 2, 3, 2, 2, 1, 3]
def baseStart_1211350 : Nat := 118140960795 + 1211350 * 2 ^ 59
def prefixEnd_1211350 : Nat := 4983230072969 + 3 ^ 40 * 1211350 * 2
def baseEnd_1211350 : Nat := 414669860549293880836073

theorem tailTrace_1211350 : CollatzResearch.WordTrace tailWord_1211350 prefixEnd_1211350 414669860549293880836073 := by
  unfold tailWord_1211350
  simp only [CollatzResearch.WordTrace]
  refine ⟨2761347760093331684648969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 29454376107662204636255669 2761347760093331684648969)
  ·
    refine ⟨2071010820069998763486727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2761347760093331684648969 2071010820069998763486727)
    ·
      refine ⟨3106516230104998145230091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2071010820069998763486727 3106516230104998145230091)
      ·
        refine ⟨4659774345157497217845137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3106516230104998145230091 4659774345157497217845137)
        ·
          refine ⟨3494830758868122913383853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4659774345157497217845137 3494830758868122913383853)
          ·
            refine ⟨1310561534575546092518945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3494830758868122913383853 1310561534575546092518945)
            ·
              refine ⟨982921150931659569389209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1310561534575546092518945 982921150931659569389209)
              ·
                refine ⟨737190863198744677041907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 982921150931659569389209 737190863198744677041907)
                ·
                  refine ⟨1105786294798117015562861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 737190863198744677041907 1105786294798117015562861)
                  ·
                    refine ⟨414669860549293880836073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1105786294798117015562861 414669860549293880836073)
                    ·
                      rfl

theorem cell22_1211350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 2, 2, 1, 3].length) (baseStart_1211350 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1211350 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1211350 prefixEnd_1211350 := by exact prefixLift 1211350
  have htrace : WordTrace (prefixWord ++ tailWord_1211350) baseStart_1211350 baseEnd_1211350 := by
    simpa [prefixWord, tailWord_1211350, baseEnd_1211350] using wordTrace_append hprefix tailTrace_1211350
  have hstable : (prefixWord ++ tailWord_1211350).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1211350).length < 2 ^ (prefixWord ++ tailWord_1211350).sum := by decide
  have hdescent : baseEnd_1211350 < baseStart_1211350 := by decide
  rcases family_descends (prefixWord ++ tailWord_1211350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1211406 : List Nat := [4, 1, 1, 2, 2, 4, 1, 2, 2, 3]
def baseStart_1211406 : Nat := 118140960795 + 1211406 * 2 ^ 59
def prefixEnd_1211406 : Nat := 4983230072969 + 3 ^ 40 * 1211406 * 2
def baseEnd_1211406 : Nat := 414689030493728401435901

theorem tailTrace_1211406 : CollatzResearch.WordTrace tailWord_1211406 prefixEnd_1211406 414689030493728401435901 := by
  unfold tailWord_1211406
  simp only [CollatzResearch.WordTrace]
  refine ⟨5522950831161303564802759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29455737766193619012281381 5522950831161303564802759)
  ·
    refine ⟨8284426246741955347204139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5522950831161303564802759 8284426246741955347204139)
    ·
      refine ⟨12426639370112933020806209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8284426246741955347204139 12426639370112933020806209)
      ·
        refine ⟨9319979527584699765604657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12426639370112933020806209 9319979527584699765604657)
        ·
          refine ⟨6989984645688524824203493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9319979527584699765604657 6989984645688524824203493)
          ·
            refine ⟨1310622121066598404538155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6989984645688524824203493 1310622121066598404538155)
            ·
              refine ⟨1965933181599897606807233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1310622121066598404538155 1965933181599897606807233)
              ·
                refine ⟨1474449886199923205105425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1965933181599897606807233 1474449886199923205105425)
                ·
                  refine ⟨1105837414649942403829069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1474449886199923205105425 1105837414649942403829069)
                  ·
                    refine ⟨414689030493728401435901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1105837414649942403829069 414689030493728401435901)
                    ·
                      rfl

theorem cell22_1211406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 1, 2, 2, 3].length) (baseStart_1211406 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1211406 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1211406 prefixEnd_1211406 := by exact prefixLift 1211406
  have htrace : WordTrace (prefixWord ++ tailWord_1211406) baseStart_1211406 baseEnd_1211406 := by
    simpa [prefixWord, tailWord_1211406, baseEnd_1211406] using wordTrace_append hprefix tailTrace_1211406
  have hstable : (prefixWord ++ tailWord_1211406).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1211406).length < 2 ^ (prefixWord ++ tailWord_1211406).sum := by decide
  have hdescent : baseEnd_1211406 < baseStart_1211406 := by decide
  rcases family_descends (prefixWord ++ tailWord_1211406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1211417 : List Nat := [1, 2, 1, 2, 1, 1, 5, 3, 3, 3]
def baseStart_1211417 : Nat := 118140960795 + 1211417 * 2 ^ 59
def prefixEnd_1211417 : Nat := 4983230072969 + 3 ^ 40 * 1211417 * 2
def baseEnd_1211417 : Nat := 414692796018528039410867

theorem tailTrace_1211417 : CollatzResearch.WordTrace tailWord_1211417 prefixEnd_1211417 414692796018528039410867 := by
  unfold tailWord_1211417
  simp only [CollatzResearch.WordTrace]
  refine ⟨44184007852250577397072505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29456005234833718264715003 44184007852250577397072505)
  ·
    refine ⟨33138005889187933047804379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44184007852250577397072505 33138005889187933047804379)
    ·
      refine ⟨49707008833781899571706569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33138005889187933047804379 49707008833781899571706569)
      ·
        refine ⟨37280256625336424678779927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49707008833781899571706569 37280256625336424678779927)
        ·
          refine ⟨55920384938004637018169891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37280256625336424678779927 55920384938004637018169891)
          ·
            refine ⟨83880577407006955527254837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55920384938004637018169891 83880577407006955527254837)
            ·
              refine ⟨7863804131906902080680141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 83880577407006955527254837 7863804131906902080680141)
              ·
                refine ⟨2948926549465088280255053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7863804131906902080680141 2948926549465088280255053)
                ·
                  refine ⟨1105847456049408105095645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2948926549465088280255053 1105847456049408105095645)
                  ·
                    refine ⟨414692796018528039410867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1105847456049408105095645 414692796018528039410867)
                    ·
                      rfl

theorem cell22_1211417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 3, 3, 3].length) (baseStart_1211417 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1211417 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1211417 prefixEnd_1211417 := by exact prefixLift 1211417
  have htrace : WordTrace (prefixWord ++ tailWord_1211417) baseStart_1211417 baseEnd_1211417 := by
    simpa [prefixWord, tailWord_1211417, baseEnd_1211417] using wordTrace_append hprefix tailTrace_1211417
  have hstable : (prefixWord ++ tailWord_1211417).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1211417).length < 2 ^ (prefixWord ++ tailWord_1211417).sum := by decide
  have hdescent : baseEnd_1211417 < baseStart_1211417 := by decide
  rcases family_descends (prefixWord ++ tailWord_1211417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1211477 : List Nat := [1, 3, 2, 2, 1, 2, 2, 2, 3, 4]
def baseStart_1211477 : Nat := 118140960795 + 1211477 * 2 ^ 59
def prefixEnd_1211477 : Nat := 4983230072969 + 3 ^ 40 * 1211477 * 2
def baseEnd_1211477 : Nat := 414713335244707882910683

theorem tailTrace_1211477 : CollatzResearch.WordTrace tailWord_1211477 prefixEnd_1211477 414713335244707882910683 := by
  unfold tailWord_1211477
  simp only [CollatzResearch.WordTrace]
  refine ⟨44186196232033207644256685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29457464154688805096171123 44186196232033207644256685)
  ·
    refine ⟨16569823587012452866596257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44186196232033207644256685 16569823587012452866596257)
    ·
      refine ⟨12427367690259339649947193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16569823587012452866596257 12427367690259339649947193)
      ·
        refine ⟨9320525767694504737460395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12427367690259339649947193 9320525767694504737460395)
        ·
          refine ⟨13980788651541757106190593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9320525767694504737460395 13980788651541757106190593)
          ·
            refine ⟨10485591488656317829642945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13980788651541757106190593 10485591488656317829642945)
            ·
              refine ⟨7864193616492238372232209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10485591488656317829642945 7864193616492238372232209)
              ·
                refine ⟨5898145212369178779174157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7864193616492238372232209 5898145212369178779174157)
                ·
                  refine ⟨2211804454638442042190309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5898145212369178779174157 2211804454638442042190309)
                  ·
                    refine ⟨414713335244707882910683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2211804454638442042190309 414713335244707882910683)
                    ·
                      rfl

theorem cell22_1211477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 2, 3, 4].length) (baseStart_1211477 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1211477 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1211477 prefixEnd_1211477 := by exact prefixLift 1211477
  have htrace : WordTrace (prefixWord ++ tailWord_1211477) baseStart_1211477 baseEnd_1211477 := by
    simpa [prefixWord, tailWord_1211477, baseEnd_1211477] using wordTrace_append hprefix tailTrace_1211477
  have hstable : (prefixWord ++ tailWord_1211477).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1211477).length < 2 ^ (prefixWord ++ tailWord_1211477).sum := by decide
  have hdescent : baseEnd_1211477 < baseStart_1211477 := by decide
  rcases family_descends (prefixWord ++ tailWord_1211477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1211556 : List Nat := [2, 3, 1, 2, 3, 3, 1, 1, 2, 4]
def baseStart_1211556 : Nat := 118140960795 + 1211556 * 2 ^ 59
def prefixEnd_1211556 : Nat := 4983230072969 + 3 ^ 40 * 1211556 * 2
def baseEnd_1211556 : Nat := 414740378559178010185441

theorem tailTrace_1211556 : CollatzResearch.WordTrace tailWord_1211556 prefixEnd_1211556 414740378559178010185441 := by
  unfold tailWord_1211556
  simp only [CollatzResearch.WordTrace]
  refine ⟨22094538799373502068191261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29459385065831336090921681 22094538799373502068191261)
  ·
    refine ⟨8285452049765063275571723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22094538799373502068191261 8285452049765063275571723)
    ·
      refine ⟨12428178074647594913357585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8285452049765063275571723 12428178074647594913357585)
      ·
        refine ⟨9321133555985696185018189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12428178074647594913357585 9321133555985696185018189)
        ·
          refine ⟨3495425083494636069381821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9321133555985696185018189 3495425083494636069381821)
          ·
            refine ⟨1310784406310488526018183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3495425083494636069381821 1310784406310488526018183)
            ·
              refine ⟨1966176609465732789027275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1310784406310488526018183 1966176609465732789027275)
              ·
                refine ⟨2949264914198599183540913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1966176609465732789027275 2949264914198599183540913)
                ·
                  refine ⟨2211948685648949387655685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2949264914198599183540913 2211948685648949387655685)
                  ·
                    refine ⟨414740378559178010185441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2211948685648949387655685 414740378559178010185441)
                    ·
                      rfl

theorem cell22_1211556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 1, 1, 2, 4].length) (baseStart_1211556 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1211556 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1211556 prefixEnd_1211556 := by exact prefixLift 1211556
  have htrace : WordTrace (prefixWord ++ tailWord_1211556) baseStart_1211556 baseEnd_1211556 := by
    simpa [prefixWord, tailWord_1211556, baseEnd_1211556] using wordTrace_append hprefix tailTrace_1211556
  have hstable : (prefixWord ++ tailWord_1211556).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1211556).length < 2 ^ (prefixWord ++ tailWord_1211556).sum := by decide
  have hdescent : baseEnd_1211556 < baseStart_1211556 := by decide
  rcases family_descends (prefixWord ++ tailWord_1211556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1211650 : List Nat := [3, 4, 1, 1, 3, 2, 2, 1, 5]
def baseStart_1211650 : Nat := 118140960795 + 1211650 * 2 ^ 59
def prefixEnd_1211650 : Nat := 4983230072969 + 3 ^ 40 * 1211650 * 2
def baseEnd_1211650 : Nat := 138257518893397699445051

theorem tailTrace_1211650 : CollatzResearch.WordTrace tailWord_1211650 prefixEnd_1211650 138257518893397699445051 := by
  unfold tailWord_1211650
  simp only [CollatzResearch.WordTrace]
  refine ⟨11048126515101614547576101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29461670706937638793536269 11048126515101614547576101)
  ·
    refine ⟨2071523721581552727670519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11048126515101614547576101 2071523721581552727670519)
    ·
      refine ⟨3107285582372329091505779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2071523721581552727670519 3107285582372329091505779)
      ·
        refine ⟨4660928373558493637258669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3107285582372329091505779 4660928373558493637258669)
        ·
          refine ⟨1747848140084435113972001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4660928373558493637258669 1747848140084435113972001)
          ·
            refine ⟨1310886105063326335479001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1747848140084435113972001 1310886105063326335479001)
            ·
              refine ⟨983164578797494751609251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1310886105063326335479001 983164578797494751609251)
              ·
                refine ⟨1474746868196242127413877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 983164578797494751609251 1474746868196242127413877)
                ·
                  refine ⟨138257518893397699445051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1474746868196242127413877 138257518893397699445051)
                  ·
                    rfl

theorem cell22_1211650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 2, 1, 5].length) (baseStart_1211650 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1211650 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1211650 prefixEnd_1211650 := by exact prefixLift 1211650
  have htrace : WordTrace (prefixWord ++ tailWord_1211650) baseStart_1211650 baseEnd_1211650 := by
    simpa [prefixWord, tailWord_1211650, baseEnd_1211650] using wordTrace_append hprefix tailTrace_1211650
  have hstable : (prefixWord ++ tailWord_1211650).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1211650).length < 2 ^ (prefixWord ++ tailWord_1211650).sum := by decide
  have hdescent : baseEnd_1211650 < baseStart_1211650 := by decide
  rcases family_descends (prefixWord ++ tailWord_1211650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1211738 : List Nat := [3, 1, 1, 2, 1, 2, 3, 5, 1, 3]
def baseStart_1211738 : Nat := 118140960795 + 1211738 * 2 ^ 59
def prefixEnd_1211738 : Nat := 4983230072969 + 3 ^ 40 * 1211738 * 2
def baseEnd_1211738 : Nat := 414802680878590202134883

theorem tailTrace_1211738 : CollatzResearch.WordTrace tailWord_1211738 prefixEnd_1211738 414802680878590202134883 := by
  unfold tailWord_1211738
  simp only [CollatzResearch.WordTrace]
  refine ⟨11048928921021912304876967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29463810456058432813005245 11048928921021912304876967)
  ·
    refine ⟨16573393381532868457315451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11048928921021912304876967 16573393381532868457315451)
    ·
      refine ⟨24860090072299302685973177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16573393381532868457315451 24860090072299302685973177)
      ·
        refine ⟨18645067554224477014479883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24860090072299302685973177 18645067554224477014479883)
        ·
          refine ⟨27967601331336715521719825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18645067554224477014479883 27967601331336715521719825)
          ·
            refine ⟨20975700998502536641289869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27967601331336715521719825 20975700998502536641289869)
            ·
              refine ⟨7865887874438451240483701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20975700998502536641289869 7865887874438451240483701)
              ·
                refine ⟨737426988228604803795347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7865887874438451240483701 737426988228604803795347)
                ·
                  refine ⟨1106140482342907205693021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 737426988228604803795347 1106140482342907205693021)
                  ·
                    refine ⟨414802680878590202134883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1106140482342907205693021 414802680878590202134883)
                    ·
                      rfl

theorem cell22_1211738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 5, 1, 3].length) (baseStart_1211738 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1211738 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1211738 prefixEnd_1211738 := by exact prefixLift 1211738
  have htrace : WordTrace (prefixWord ++ tailWord_1211738) baseStart_1211738 baseEnd_1211738 := by
    simpa [prefixWord, tailWord_1211738, baseEnd_1211738] using wordTrace_append hprefix tailTrace_1211738
  have hstable : (prefixWord ++ tailWord_1211738).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1211738).length < 2 ^ (prefixWord ++ tailWord_1211738).sum := by decide
  have hdescent : baseEnd_1211738 < baseStart_1211738 := by decide
  rcases family_descends (prefixWord ++ tailWord_1211738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1211749 : List Nat := [1, 3, 1, 3, 1, 2, 1, 1, 4, 5]
def baseStart_1211749 : Nat := 118140960795 + 1211749 * 2 ^ 59
def prefixEnd_1211749 : Nat := 4983230072969 + 3 ^ 40 * 1211749 * 2
def baseEnd_1211749 : Nat := 414806446403389840109849

theorem tailTrace_1211749 : CollatzResearch.WordTrace tailWord_1211749 prefixEnd_1211749 414806446403389840109849 := by
  unfold tailWord_1211749
  simp only [CollatzResearch.WordTrace]
  refine ⟨44196116887047798098158301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29464077924698532065438867 44196116887047798098158301)
  ·
    refine ⟨16573543832642924286809363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44196116887047798098158301 16573543832642924286809363)
    ·
      refine ⟨24860315748964386430214045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16573543832642924286809363 24860315748964386430214045)
      ·
        refine ⟨9322618405861644911330267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24860315748964386430214045 9322618405861644911330267)
        ·
          refine ⟨13983927608792467366995401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9322618405861644911330267 13983927608792467366995401)
          ·
            refine ⟨10487945706594350525246551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13983927608792467366995401 10487945706594350525246551)
            ·
              refine ⟨15731918559891525787869827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10487945706594350525246551 15731918559891525787869827)
              ·
                refine ⟨23597877839837288681804741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15731918559891525787869827 23597877839837288681804741)
                ·
                  refine ⟨4424602094969491627838389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23597877839837288681804741 4424602094969491627838389)
                  ·
                    refine ⟨414806446403389840109849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4424602094969491627838389 414806446403389840109849)
                    ·
                      rfl

theorem cell22_1211749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 1, 4, 5].length) (baseStart_1211749 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1211749 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1211749 prefixEnd_1211749 := by exact prefixLift 1211749
  have htrace : WordTrace (prefixWord ++ tailWord_1211749) baseStart_1211749 baseEnd_1211749 := by
    simpa [prefixWord, tailWord_1211749, baseEnd_1211749] using wordTrace_append hprefix tailTrace_1211749
  have hstable : (prefixWord ++ tailWord_1211749).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1211749).length < 2 ^ (prefixWord ++ tailWord_1211749).sum := by decide
  have hdescent : baseEnd_1211749 < baseStart_1211749 := by decide
  rcases family_descends (prefixWord ++ tailWord_1211749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1211751 : List Nat := [1, 1, 5, 1, 4, 1, 1, 1, 7]
def baseStart_1211751 : Nat := 118140960795 + 1211751 * 2 ^ 59
def prefixEnd_1211751 : Nat := 4983230072969 + 3 ^ 40 * 1211751 * 2
def baseEnd_1211751 : Nat := 138269043681420833853281

theorem tailTrace_1211751 : CollatzResearch.WordTrace tailWord_1211751 prefixEnd_1211751 138269043681420833853281 := by
  unfold tailWord_1211751
  simp only [CollatzResearch.WordTrace]
  refine ⟨44196189833040552439731107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29464126555360368293154071 44196189833040552439731107)
  ·
    refine ⟨66294284749560828659596661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44196189833040552439731107 66294284749560828659596661)
    ·
      refine ⟨6215089195271327686837187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 66294284749560828659596661 6215089195271327686837187)
      ·
        refine ⟨9322633792906991530255781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6215089195271327686837187 9322633792906991530255781)
        ·
          refine ⟨1747993836170060911922959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9322633792906991530255781 1747993836170060911922959)
          ·
            refine ⟨2621990754255091367884439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1747993836170060911922959 2621990754255091367884439)
            ·
              refine ⟨3932986131382637051826659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2621990754255091367884439 3932986131382637051826659)
              ·
                refine ⟨5899479197073955577739989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3932986131382637051826659 5899479197073955577739989)
                ·
                  refine ⟨138269043681420833853281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5899479197073955577739989 138269043681420833853281)
                  ·
                    rfl

theorem cell22_1211751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 1, 1, 7].length) (baseStart_1211751 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1211751 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1211751 prefixEnd_1211751 := by exact prefixLift 1211751
  have htrace : WordTrace (prefixWord ++ tailWord_1211751) baseStart_1211751 baseEnd_1211751 := by
    simpa [prefixWord, tailWord_1211751, baseEnd_1211751] using wordTrace_append hprefix tailTrace_1211751
  have hstable : (prefixWord ++ tailWord_1211751).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1211751).length < 2 ^ (prefixWord ++ tailWord_1211751).sum := by decide
  have hdescent : baseEnd_1211751 < baseStart_1211751 := by decide
  rcases family_descends (prefixWord ++ tailWord_1211751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1211781 : List Nat := [1, 3, 1, 1, 3, 1, 3, 4, 1, 4]
def baseStart_1211781 : Nat := 118140960795 + 1211781 * 2 ^ 59
def prefixEnd_1211781 : Nat := 4983230072969 + 3 ^ 40 * 1211781 * 2
def baseEnd_1211781 : Nat := 414817400657352423309751

theorem tailTrace_1211781 : CollatzResearch.WordTrace tailWord_1211781 prefixEnd_1211781 414817400657352423309751 := by
  unfold tailWord_1211781
  simp only [CollatzResearch.WordTrace]
  refine ⟨44197284022931867563323197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29464856015287911708882131 44197284022931867563323197)
  ·
    refine ⟨16573981508599450336246199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44197284022931867563323197 16573981508599450336246199)
    ·
      refine ⟨24860972262899175504369299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16573981508599450336246199 24860972262899175504369299)
      ·
        refine ⟨37291458394348763256553949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24860972262899175504369299 37291458394348763256553949)
        ·
          refine ⟨13984296897880786221207731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37291458394348763256553949 13984296897880786221207731)
          ·
            refine ⟨20976445346821179331811597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13984296897880786221207731 20976445346821179331811597)
            ·
              refine ⟨7866167005057942249429349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20976445346821179331811597 7866167005057942249429349)
              ·
                refine ⟨1474906313448364171768003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7866167005057942249429349 1474906313448364171768003)
                ·
                  refine ⟨2212359470172546257652005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1474906313448364171768003 2212359470172546257652005)
                  ·
                    refine ⟨414817400657352423309751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2212359470172546257652005 414817400657352423309751)
                    ·
                      rfl

theorem cell22_1211781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 4, 1, 4].length) (baseStart_1211781 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1211781 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1211781 prefixEnd_1211781 := by exact prefixLift 1211781
  have htrace : WordTrace (prefixWord ++ tailWord_1211781) baseStart_1211781 baseEnd_1211781 := by
    simpa [prefixWord, tailWord_1211781, baseEnd_1211781] using wordTrace_append hprefix tailTrace_1211781
  have hstable : (prefixWord ++ tailWord_1211781).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1211781).length < 2 ^ (prefixWord ++ tailWord_1211781).sum := by decide
  have hdescent : baseEnd_1211781 < baseStart_1211781 := by decide
  rcases family_descends (prefixWord ++ tailWord_1211781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1211811 : List Nat := [1, 1, 1, 4, 1, 3, 1, 3, 4, 3]
def baseStart_1211811 : Nat := 118140960795 + 1211811 * 2 ^ 59
def prefixEnd_1211811 : Nat := 4983230072969 + 3 ^ 40 * 1211811 * 2
def baseEnd_1211811 : Nat := 414827670270442345059659

theorem tailTrace_1211811 : CollatzResearch.WordTrace tailWord_1211811 prefixEnd_1211811 414827670270442345059659 := by
  unfold tailWord_1211811
  simp only [CollatzResearch.WordTrace]
  refine ⟨44198378212823182686915287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29465585475215455124610191 44198378212823182686915287)
  ·
    refine ⟨66297567319234774030372931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44198378212823182686915287 66297567319234774030372931)
    ·
      refine ⟨99446350978852161045559397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66297567319234774030372931 99446350978852161045559397)
      ·
        refine ⟨18646190808534780196042387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 99446350978852161045559397 18646190808534780196042387)
        ·
          refine ⟨27969286212802170294063581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18646190808534780196042387 27969286212802170294063581)
          ·
            refine ⟨10488482329800813860273843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27969286212802170294063581 10488482329800813860273843)
            ·
              refine ⟨15732723494701220790410765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10488482329800813860273843 15732723494701220790410765)
              ·
                refine ⟨5899771310512957796404037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15732723494701220790410765 5899771310512957796404037)
                ·
                  refine ⟨1106207120721179586825757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5899771310512957796404037 1106207120721179586825757)
                  ·
                    refine ⟨414827670270442345059659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1106207120721179586825757 414827670270442345059659)
                    ·
                      rfl

theorem cell22_1211811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 3, 4, 3].length) (baseStart_1211811 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1211811 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1211811 prefixEnd_1211811 := by exact prefixLift 1211811
  have htrace : WordTrace (prefixWord ++ tailWord_1211811) baseStart_1211811 baseEnd_1211811 := by
    simpa [prefixWord, tailWord_1211811, baseEnd_1211811] using wordTrace_append hprefix tailTrace_1211811
  have hstable : (prefixWord ++ tailWord_1211811).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1211811).length < 2 ^ (prefixWord ++ tailWord_1211811).sum := by decide
  have hdescent : baseEnd_1211811 < baseStart_1211811 := by decide
  rcases family_descends (prefixWord ++ tailWord_1211811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1211839 : List Nat := [1, 1, 2, 2, 2, 1, 1, 3, 2, 7]
def baseStart_1211839 : Nat := 118140960795 + 1211839 * 2 ^ 59
def prefixEnd_1211839 : Nat := 4983230072969 + 3 ^ 40 * 1211839 * 2
def baseEnd_1211839 : Nat := 414837255242659605359573

theorem tailTrace_1211839 : CollatzResearch.WordTrace tailWord_1211839 prefixEnd_1211839 414837255242659605359573 := by
  unfold tailWord_1211839
  simp only [CollatzResearch.WordTrace]
  refine ⟨44199399456721743468934571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29466266304481162312623047 44199399456721743468934571)
  ·
    refine ⟨66299099185082615203401857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44199399456721743468934571 66299099185082615203401857)
    ·
      refine ⟨49724324388811961402551393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66299099185082615203401857 49724324388811961402551393)
      ·
        refine ⟨37293243291608971051913545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49724324388811961402551393 37293243291608971051913545)
        ·
          refine ⟨27969932468706728288935159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37293243291608971051913545 27969932468706728288935159)
          ·
            refine ⟨41954898703060092433402739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27969932468706728288935159 41954898703060092433402739)
            ·
              refine ⟨62932348054590138650104109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41954898703060092433402739 62932348054590138650104109)
              ·
                refine ⟨23599630520471301993789041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 62932348054590138650104109 23599630520471301993789041)
                ·
                  refine ⟨17699722890353476495341781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23599630520471301993789041 17699722890353476495341781)
                  ·
                    refine ⟨414837255242659605359573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17699722890353476495341781 414837255242659605359573)
                    ·
                      rfl

theorem cell22_1211839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 3, 2, 7].length) (baseStart_1211839 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1211839 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1211839 prefixEnd_1211839 := by exact prefixLift 1211839
  have htrace : WordTrace (prefixWord ++ tailWord_1211839) baseStart_1211839 baseEnd_1211839 := by
    simpa [prefixWord, tailWord_1211839, baseEnd_1211839] using wordTrace_append hprefix tailTrace_1211839
  have hstable : (prefixWord ++ tailWord_1211839).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1211839).length < 2 ^ (prefixWord ++ tailWord_1211839).sum := by decide
  have hdescent : baseEnd_1211839 < baseStart_1211839 := by decide
  rcases family_descends (prefixWord ++ tailWord_1211839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1211856 : List Nat := [2, 1, 1, 1, 1, 2, 2, 4, 5, 3]
def baseStart_1211856 : Nat := 118140960795 + 1211856 * 2 ^ 59
def prefixEnd_1211856 : Nat := 4983230072969 + 3 ^ 40 * 1211856 * 2
def baseEnd_1211856 : Nat := 414843074690077227684521

theorem tailTrace_1211856 : CollatzResearch.WordTrace tailWord_1211856 prefixEnd_1211856 414843074690077227684521 := by
  unfold tailWord_1211856
  simp only [CollatzResearch.WordTrace]
  refine ⟨22100009748830077686151711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29466679665106770248202281 22100009748830077686151711)
  ·
    refine ⟨33150014623245116529227567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22100009748830077686151711 33150014623245116529227567)
    ·
      refine ⟨49725021934867674793841351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33150014623245116529227567 49725021934867674793841351)
      ·
        refine ⟨74587532902301512190762027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49725021934867674793841351 74587532902301512190762027)
        ·
          refine ⟨111881299353452268286143041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74587532902301512190762027 111881299353452268286143041)
          ·
            refine ⟨83910974515089201214607281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111881299353452268286143041 83910974515089201214607281)
            ·
              refine ⟨62933230886316900910955461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83910974515089201214607281 62933230886316900910955461)
              ·
                refine ⟨11799980791184418920804149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 62933230886316900910955461 11799980791184418920804149)
                ·
                  refine ⟨1106248199173539273825389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 11799980791184418920804149 1106248199173539273825389)
                  ·
                    refine ⟨414843074690077227684521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1106248199173539273825389 414843074690077227684521)
                    ·
                      rfl

theorem cell22_1211856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 4, 5, 3].length) (baseStart_1211856 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1211856 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1211856 prefixEnd_1211856 := by exact prefixLift 1211856
  have htrace : WordTrace (prefixWord ++ tailWord_1211856) baseStart_1211856 baseEnd_1211856 := by
    simpa [prefixWord, tailWord_1211856, baseEnd_1211856] using wordTrace_append hprefix tailTrace_1211856
  have hstable : (prefixWord ++ tailWord_1211856).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1211856).length < 2 ^ (prefixWord ++ tailWord_1211856).sum := by decide
  have hdescent : baseEnd_1211856 < baseStart_1211856 := by decide
  rcases family_descends (prefixWord ++ tailWord_1211856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1211862 : List Nat := [5, 2, 1, 1, 1, 3, 2, 2, 2, 3]
def baseStart_1211862 : Nat := 118140960795 + 1211862 * 2 ^ 59
def prefixEnd_1211862 : Nat := 4983230072969 + 3 ^ 40 * 1211862 * 2
def baseEnd_1211862 : Nat := 414845128612695212034503

theorem tailTrace_1211862 : CollatzResearch.WordTrace tailWord_1211862 prefixEnd_1211862 414845128612695212034503 := by
  unfold tailWord_1211862
  simp only [CollatzResearch.WordTrace]
  refine ⟨2762514895977401149813865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 29466825557092278931347893 2762514895977401149813865)
  ·
    refine ⟨2071886171983050862360399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2762514895977401149813865 2071886171983050862360399)
    ·
      refine ⟨3107829257974576293540599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2071886171983050862360399 3107829257974576293540599)
      ·
        refine ⟨4661743886961864440310899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3107829257974576293540599 4661743886961864440310899)
        ·
          refine ⟨6992615830442796660466349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4661743886961864440310899 6992615830442796660466349)
          ·
            refine ⟨2622230936416048747674881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6992615830442796660466349 2622230936416048747674881)
            ·
              refine ⟨1966673202312036560756161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2622230936416048747674881 1966673202312036560756161)
              ·
                refine ⟨1475004901734027420567121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1966673202312036560756161 1475004901734027420567121)
                ·
                  refine ⟨1106253676300520565425341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1475004901734027420567121 1106253676300520565425341)
                  ·
                    refine ⟨414845128612695212034503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1106253676300520565425341 414845128612695212034503)
                    ·
                      rfl

theorem cell22_1211862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 2, 2, 2, 3].length) (baseStart_1211862 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1211862 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1211862 prefixEnd_1211862 := by exact prefixLift 1211862
  have htrace : WordTrace (prefixWord ++ tailWord_1211862) baseStart_1211862 baseEnd_1211862 := by
    simpa [prefixWord, tailWord_1211862, baseEnd_1211862] using wordTrace_append hprefix tailTrace_1211862
  have hstable : (prefixWord ++ tailWord_1211862).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1211862).length < 2 ^ (prefixWord ++ tailWord_1211862).sum := by decide
  have hdescent : baseEnd_1211862 < baseStart_1211862 := by decide
  rcases family_descends (prefixWord ++ tailWord_1211862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1211890 : List Nat := [3, 2, 1, 4, 1, 2, 1, 2, 3, 3]
def baseStart_1211890 : Nat := 118140960795 + 1211890 * 2 ^ 59
def prefixEnd_1211890 : Nat := 4983230072969 + 3 ^ 40 * 1211890 * 2
def baseEnd_1211890 : Nat := 414854713584912472334417

theorem tailTrace_1211890 : CollatzResearch.WordTrace tailWord_1211890 prefixEnd_1211890 414854713584912472334417 := by
  unfold tailWord_1211890
  simp only [CollatzResearch.WordTrace]
  refine ⟨11050314894884244794760281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29467506386357986119360749 11050314894884244794760281)
  ·
    refine ⟨8287736171163183596070211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11050314894884244794760281 8287736171163183596070211)
    ·
      refine ⟨12431604256744775394105317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8287736171163183596070211 12431604256744775394105317)
      ·
        refine ⟨2330925798139645386394747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12431604256744775394105317 2330925798139645386394747)
        ·
          refine ⟨3496388697209468079592121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2330925798139645386394747 3496388697209468079592121)
          ·
            refine ⟨2622291522907101059694091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3496388697209468079592121 2622291522907101059694091)
            ·
              refine ⟨3933437284360651589541137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2622291522907101059694091 3933437284360651589541137)
              ·
                refine ⟨2950077963270488692155853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3933437284360651589541137 2950077963270488692155853)
                ·
                  refine ⟨1106279236226433259558445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2950077963270488692155853 1106279236226433259558445)
                  ·
                    refine ⟨414854713584912472334417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1106279236226433259558445 414854713584912472334417)
                    ·
                      rfl

theorem cell22_1211890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 1, 2, 3, 3].length) (baseStart_1211890 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1211890 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1211890 prefixEnd_1211890 := by exact prefixLift 1211890
  have htrace : WordTrace (prefixWord ++ tailWord_1211890) baseStart_1211890 baseEnd_1211890 := by
    simpa [prefixWord, tailWord_1211890, baseEnd_1211890] using wordTrace_append hprefix tailTrace_1211890
  have hstable : (prefixWord ++ tailWord_1211890).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1211890).length < 2 ^ (prefixWord ++ tailWord_1211890).sum := by decide
  have hdescent : baseEnd_1211890 < baseStart_1211890 := by decide
  rcases family_descends (prefixWord ++ tailWord_1211890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1211950 : List Nat := [4, 1, 3, 1, 2, 1, 1, 4, 1, 4]
def baseStart_1211950 : Nat := 118140960795 + 1211950 * 2 ^ 59
def prefixEnd_1211950 : Nat := 4983230072969 + 3 ^ 40 * 1211950 * 2
def baseEnd_1211950 : Nat := 414875252811092315834233

theorem tailTrace_1211950 : CollatzResearch.WordTrace tailWord_1211950 prefixEnd_1211950 414875252811092315834233 := by
  unfold tailWord_1211950
  simp only [CollatzResearch.WordTrace]
  refine ⟨5525430994914951178278163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29468965306213072950816869 5525430994914951178278163)
  ·
    refine ⟨8288146492372426767417245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5525430994914951178278163 8288146492372426767417245)
    ·
      refine ⟨3108054934639660037781467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8288146492372426767417245 3108054934639660037781467)
      ·
        refine ⟨4662082401959490056672201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3108054934639660037781467 4662082401959490056672201)
        ·
          refine ⟨3496561801469617542504151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4662082401959490056672201 3496561801469617542504151)
          ·
            refine ⟨5244842702204426313756227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3496561801469617542504151 5244842702204426313756227)
            ·
              refine ⟨7867264053306639470634341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5244842702204426313756227 7867264053306639470634341)
              ·
                refine ⟨1475112009994994900743939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7867264053306639470634341 1475112009994994900743939)
                ·
                  refine ⟨2212668014992492351115909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1475112009994994900743939 2212668014992492351115909)
                  ·
                    refine ⟨414875252811092315834233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2212668014992492351115909 414875252811092315834233)
                    ·
                      rfl

theorem cell22_1211950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 4, 1, 4].length) (baseStart_1211950 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1211950 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1211950 prefixEnd_1211950 := by exact prefixLift 1211950
  have htrace : WordTrace (prefixWord ++ tailWord_1211950) baseStart_1211950 baseEnd_1211950 := by
    simpa [prefixWord, tailWord_1211950, baseEnd_1211950] using wordTrace_append hprefix tailTrace_1211950
  have hstable : (prefixWord ++ tailWord_1211950).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1211950).length < 2 ^ (prefixWord ++ tailWord_1211950).sum := by decide
  have hdescent : baseEnd_1211950 < baseStart_1211950 := by decide
  rcases family_descends (prefixWord ++ tailWord_1211950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1211978 : List Nat := [3, 1, 2, 1, 1, 3, 3, 2, 2, 4]
def baseStart_1211978 : Nat := 118140960795 + 1211978 * 2 ^ 59
def prefixEnd_1211978 : Nat := 4983230072969 + 3 ^ 40 * 1211978 * 2
def baseEnd_1211978 : Nat := 414884837783309576134147

theorem tailTrace_1211978 : CollatzResearch.WordTrace tailWord_1211978 prefixEnd_1211978 414884837783309576134147 := by
  unfold tailWord_1211978
  simp only [CollatzResearch.WordTrace]
  refine ⟨11051117300804542552061147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29469646135478780138829725 11051117300804542552061147)
  ·
    refine ⟨16576675951206813828091721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11051117300804542552061147 16576675951206813828091721)
    ·
      refine ⟨12432506963405110371068791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16576675951206813828091721 12432506963405110371068791)
      ·
        refine ⟨18648760445107665556603187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12432506963405110371068791 18648760445107665556603187)
        ·
          refine ⟨27973140667661498334904781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18648760445107665556603187 27973140667661498334904781)
          ·
            refine ⟨10489927750373061875589293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27973140667661498334904781 10489927750373061875589293)
            ·
              refine ⟨3933722906389898203345985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10489927750373061875589293 3933722906389898203345985)
              ·
                refine ⟨2950292179792423652509489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3933722906389898203345985 2950292179792423652509489)
                ·
                  refine ⟨2212719134844317739382117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2950292179792423652509489 2212719134844317739382117)
                  ·
                    refine ⟨414884837783309576134147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2212719134844317739382117 414884837783309576134147)
                    ·
                      rfl

theorem cell22_1211978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3, 2, 2, 4].length) (baseStart_1211978 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1211978 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1211978 prefixEnd_1211978 := by exact prefixLift 1211978
  have htrace : WordTrace (prefixWord ++ tailWord_1211978) baseStart_1211978 baseEnd_1211978 := by
    simpa [prefixWord, tailWord_1211978, baseEnd_1211978] using wordTrace_append hprefix tailTrace_1211978
  have hstable : (prefixWord ++ tailWord_1211978).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1211978).length < 2 ^ (prefixWord ++ tailWord_1211978).sum := by decide
  have hdescent : baseEnd_1211978 < baseStart_1211978 := by decide
  rcases family_descends (prefixWord ++ tailWord_1211978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1212051 : List Nat := [1, 1, 1, 2, 1, 2, 2, 1, 1, 10]
def baseStart_1212051 : Nat := 118140960795 + 1212051 * 2 ^ 59
def prefixEnd_1212051 : Nat := 4983230072969 + 3 ^ 40 * 1212051 * 2
def baseEnd_1212051 : Nat := 414909827175161719058923

theorem tailTrace_1212051 : CollatzResearch.WordTrace tailWord_1212051 prefixEnd_1212051 414909827175161719058923 := by
  unfold tailWord_1212051
  simp only [CollatzResearch.WordTrace]
  refine ⟨44207131731953703675652007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29471421154635802450434671 44207131731953703675652007)
  ·
    refine ⟨66310697597930555513478011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44207131731953703675652007 66310697597930555513478011)
    ·
      refine ⟨99466046396895833270217017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66310697597930555513478011 99466046396895833270217017)
      ·
        refine ⟨74599534797671874952662763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99466046396895833270217017 74599534797671874952662763)
        ·
          refine ⟨111899302196507812428994145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74599534797671874952662763 111899302196507812428994145)
          ·
            refine ⟨83924476647380859321745609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111899302196507812428994145 83924476647380859321745609)
            ·
              refine ⟨62943357485535644491309207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83924476647380859321745609 62943357485535644491309207)
              ·
                refine ⟨94415036228303466736963811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62943357485535644491309207 94415036228303466736963811)
                ·
                  refine ⟨141622554342455200105445717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 94415036228303466736963811 141622554342455200105445717)
                  ·
                    refine ⟨414909827175161719058923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 141622554342455200105445717 414909827175161719058923)
                    ·
                      rfl

theorem cell22_1212051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 10].length) (baseStart_1212051 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1212051 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1212051 prefixEnd_1212051 := by exact prefixLift 1212051
  have htrace : WordTrace (prefixWord ++ tailWord_1212051) baseStart_1212051 baseEnd_1212051 := by
    simpa [prefixWord, tailWord_1212051, baseEnd_1212051] using wordTrace_append hprefix tailTrace_1212051
  have hstable : (prefixWord ++ tailWord_1212051).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1212051).length < 2 ^ (prefixWord ++ tailWord_1212051).sum := by decide
  have hdescent : baseEnd_1212051 < baseStart_1212051 := by decide
  rcases family_descends (prefixWord ++ tailWord_1212051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1212100 : List Nat := [2, 3, 3, 1, 1, 1, 4, 1, 6]
def baseStart_1212100 : Nat := 118140960795 + 1212100 * 2 ^ 59
def prefixEnd_1212100 : Nat := 4983230072969 + 3 ^ 40 * 1212100 * 2
def baseEnd_1212100 : Nat := 138308866958847308194591

theorem tailTrace_1212100 : CollatzResearch.WordTrace tailWord_1212100 prefixEnd_1212100 138308866958847308194591 := by
  unfold tailWord_1212100
  simp only [CollatzResearch.WordTrace]
  refine ⟨22104459454388092522092877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29472612605850790029457169 22104459454388092522092877)
  ·
    refine ⟨8289172295395534695784829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22104459454388092522092877 8289172295395534695784829)
    ·
      refine ⟨3108439610773325510919311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8289172295395534695784829 3108439610773325510919311)
      ·
        refine ⟨4662659416159988266378967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3108439610773325510919311 4662659416159988266378967)
        ·
          refine ⟨6993989124239982399568451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4662659416159988266378967 6993989124239982399568451)
          ·
            refine ⟨10490983686359973599352677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6993989124239982399568451 10490983686359973599352677)
            ·
              refine ⟨1967059441192495049878627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10490983686359973599352677 1967059441192495049878627)
              ·
                refine ⟨2950589161788742574817941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1967059441192495049878627 2950589161788742574817941)
                ·
                  refine ⟨138308866958847308194591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2950589161788742574817941 138308866958847308194591)
                  ·
                    rfl

theorem cell22_1212100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 4, 1, 6].length) (baseStart_1212100 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1212100 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1212100 prefixEnd_1212100 := by exact prefixLift 1212100
  have htrace : WordTrace (prefixWord ++ tailWord_1212100) baseStart_1212100 baseEnd_1212100 := by
    simpa [prefixWord, tailWord_1212100, baseEnd_1212100] using wordTrace_append hprefix tailTrace_1212100
  have hstable : (prefixWord ++ tailWord_1212100).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1212100).length < 2 ^ (prefixWord ++ tailWord_1212100).sum := by decide
  have hdescent : baseEnd_1212100 < baseStart_1212100 := by decide
  rcases family_descends (prefixWord ++ tailWord_1212100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1212113 : List Nat := [1, 2, 2, 1, 2, 4, 1, 2, 1, 6]
def baseStart_1212113 : Nat := 118140960795 + 1212113 * 2 ^ 59
def prefixEnd_1212113 : Nat := 4983230072969 + 3 ^ 40 * 1212113 * 2
def baseEnd_1212113 : Nat := 414931051042214224008733

theorem tailTrace_1212113 : CollatzResearch.WordTrace tailWord_1212113 prefixEnd_1212113 414931051042214224008733 := by
  unfold tailWord_1212113
  simp only [CollatzResearch.WordTrace]
  refine ⟨44209393057729088264408993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29472928705152725509605995 44209393057729088264408993)
  ·
    refine ⟨33157044793296816198306745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44209393057729088264408993 33157044793296816198306745)
    ·
      refine ⟨24867783594972612148730059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33157044793296816198306745 24867783594972612148730059)
      ·
        refine ⟨37301675392458918223095089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24867783594972612148730059 37301675392458918223095089)
        ·
          refine ⟨27976256544344188667321317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37301675392458918223095089 27976256544344188667321317)
          ·
            refine ⟨5245548102064535375122747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27976256544344188667321317 5245548102064535375122747)
            ·
              refine ⟨7868322153096803062684121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5245548102064535375122747 7868322153096803062684121)
              ·
                refine ⟨5901241614822602297013091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7868322153096803062684121 5901241614822602297013091)
                ·
                  refine ⟨8851862422233903445519637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5901241614822602297013091 8851862422233903445519637)
                  ·
                    refine ⟨414931051042214224008733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8851862422233903445519637 414931051042214224008733)
                    ·
                      rfl

theorem cell22_1212113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 2, 1, 6].length) (baseStart_1212113 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1212113 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1212113 prefixEnd_1212113 := by exact prefixLift 1212113
  have htrace : WordTrace (prefixWord ++ tailWord_1212113) baseStart_1212113 baseEnd_1212113 := by
    simpa [prefixWord, tailWord_1212113, baseEnd_1212113] using wordTrace_append hprefix tailTrace_1212113
  have hstable : (prefixWord ++ tailWord_1212113).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1212113).length < 2 ^ (prefixWord ++ tailWord_1212113).sum := by decide
  have hdescent : baseEnd_1212113 < baseStart_1212113 := by decide
  rcases family_descends (prefixWord ++ tailWord_1212113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1212194 : List Nat := [3, 3, 1, 1, 2, 1, 2, 5, 1, 3]
def baseStart_1212194 : Nat := 118140960795 + 1212194 * 2 ^ 59
def prefixEnd_1212194 : Nat := 4983230072969 + 3 ^ 40 * 1212194 * 2
def baseEnd_1212194 : Nat := 414958778997557012733485

theorem tailTrace_1212194 : CollatzResearch.WordTrace tailWord_1212194 prefixEnd_1212194 414958778997557012733485 := by
  unfold tailWord_1212194
  simp only [CollatzResearch.WordTrace]
  refine ⟨11053086842608909774526909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29474898246957092732071757 11053086842608909774526909)
  ·
    refine ⟨4144907565978341165447591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11053086842608909774526909 4144907565978341165447591)
    ·
      refine ⟨6217361348967511748171387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4144907565978341165447591 6217361348967511748171387)
      ·
        refine ⟨9326042023451267622257081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6217361348967511748171387 9326042023451267622257081)
        ·
          refine ⟨6994531517588450716692811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9326042023451267622257081 6994531517588450716692811)
          ·
            refine ⟨10491797276382676075039217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6994531517588450716692811 10491797276382676075039217)
            ·
              refine ⟨7868847957287007056279413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10491797276382676075039217 7868847957287007056279413)
              ·
                refine ⟨737704495995656911526195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7868847957287007056279413 737704495995656911526195)
                ·
                  refine ⟨1106556743993485367289293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 737704495995656911526195 1106556743993485367289293)
                  ·
                    refine ⟨414958778997557012733485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1106556743993485367289293 414958778997557012733485)
                    ·
                      rfl

theorem cell22_1212194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 5, 1, 3].length) (baseStart_1212194 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1212194 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1212194 prefixEnd_1212194 := by exact prefixLift 1212194
  have htrace : WordTrace (prefixWord ++ tailWord_1212194) baseStart_1212194 baseEnd_1212194 := by
    simpa [prefixWord, tailWord_1212194, baseEnd_1212194] using wordTrace_append hprefix tailTrace_1212194
  have hstable : (prefixWord ++ tailWord_1212194).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1212194).length < 2 ^ (prefixWord ++ tailWord_1212194).sum := by decide
  have hdescent : baseEnd_1212194 < baseStart_1212194 := by decide
  rcases family_descends (prefixWord ++ tailWord_1212194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1212220 : List Nat := [2, 2, 2, 2, 1, 1, 3, 2, 3, 4]
def baseStart_1212220 : Nat := 118140960795 + 1212220 * 2 ^ 59
def prefixEnd_1212220 : Nat := 4983230072969 + 3 ^ 40 * 1212220 * 2
def baseEnd_1212220 : Nat := 414967679328901611583405

theorem tailTrace_1212220 : CollatzResearch.WordTrace tailWord_1212220 prefixEnd_1212220 414967679328901611583405 := by
  unfold tailWord_1212220
  simp only [CollatzResearch.WordTrace]
  refine ⟨22106647834170722769277057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29475530445560963692369409 22106647834170722769277057)
  ·
    refine ⟨16579985875628042076957793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22106647834170722769277057 16579985875628042076957793)
    ·
      refine ⟨12434989406721031557718345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16579985875628042076957793 12434989406721031557718345)
      ·
        refine ⟨9326242055040773668288759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12434989406721031557718345 9326242055040773668288759)
        ·
          refine ⟨13989363082561160502433139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9326242055040773668288759 13989363082561160502433139)
          ·
            refine ⟨20984044623841740753649709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13989363082561160502433139 20984044623841740753649709)
            ·
              refine ⟨7869016733940652782618641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20984044623841740753649709 7869016733940652782618641)
              ·
                refine ⟨5901762550455489586963981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7869016733940652782618641 5901762550455489586963981)
                ·
                  refine ⟨2213160956420808595111493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5901762550455489586963981 2213160956420808595111493)
                  ·
                    refine ⟨414967679328901611583405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2213160956420808595111493 414967679328901611583405)
                    ·
                      rfl

theorem cell22_1212220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 2, 3, 4].length) (baseStart_1212220 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1212220 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1212220 prefixEnd_1212220 := by exact prefixLift 1212220
  have htrace : WordTrace (prefixWord ++ tailWord_1212220) baseStart_1212220 baseEnd_1212220 := by
    simpa [prefixWord, tailWord_1212220, baseEnd_1212220] using wordTrace_append hprefix tailTrace_1212220
  have hstable : (prefixWord ++ tailWord_1212220).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1212220).length < 2 ^ (prefixWord ++ tailWord_1212220).sum := by decide
  have hdescent : baseEnd_1212220 < baseStart_1212220 := by decide
  rcases family_descends (prefixWord ++ tailWord_1212220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1212222 : List Nat := [4, 2, 1, 2, 2, 2, 1, 1, 2, 5]
def baseStart_1212222 : Nat := 118140960795 + 1212222 * 2 ^ 59
def prefixEnd_1212222 : Nat := 4983230072969 + 3 ^ 40 * 1212222 * 2
def baseEnd_1212222 : Nat := 414968363969774273033399

theorem tailTrace_1212222 : CollatzResearch.WordTrace tailWord_1212222 prefixEnd_1212222 414968363969774273033399 := by
  unfold tailWord_1212222
  simp only [CollatzResearch.WordTrace]
  refine ⟨5526671076791774985015865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29475579076222799920084613 5526671076791774985015865)
  ·
    refine ⟨4145003307593831238761899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5526671076791774985015865 4145003307593831238761899)
    ·
      refine ⟨6217504961390746858142849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4145003307593831238761899 6217504961390746858142849)
      ·
        refine ⟨4663128721043060143607137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6217504961390746858142849 4663128721043060143607137)
        ·
          refine ⟨3497346540782295107705353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4663128721043060143607137 3497346540782295107705353)
          ·
            refine ⟨2623009905586721330779015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3497346540782295107705353 2623009905586721330779015)
            ·
              refine ⟨3934514858380081996168523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2623009905586721330779015 3934514858380081996168523)
              ·
                refine ⟨5901772287570122994252785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3934514858380081996168523 5901772287570122994252785)
                ·
                  refine ⟨4426329215677592245689589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5901772287570122994252785 4426329215677592245689589)
                  ·
                    refine ⟨414968363969774273033399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4426329215677592245689589 414968363969774273033399)
                    ·
                      rfl

theorem cell22_1212222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 1, 1, 2, 5].length) (baseStart_1212222 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1212222 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1212222 prefixEnd_1212222 := by exact prefixLift 1212222
  have htrace : WordTrace (prefixWord ++ tailWord_1212222) baseStart_1212222 baseEnd_1212222 := by
    simpa [prefixWord, tailWord_1212222, baseEnd_1212222] using wordTrace_append hprefix tailTrace_1212222
  have hstable : (prefixWord ++ tailWord_1212222).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1212222).length < 2 ^ (prefixWord ++ tailWord_1212222).sum := by decide
  have hdescent : baseEnd_1212222 < baseStart_1212222 := by decide
  rcases family_descends (prefixWord ++ tailWord_1212222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1212250 : List Nat := [3, 1, 1, 2, 1, 3, 1, 4, 1, 5]
def baseStart_1212250 : Nat := 118140960795 + 1212250 * 2 ^ 59
def prefixEnd_1212250 : Nat := 4983230072969 + 3 ^ 40 * 1212250 * 2
def baseEnd_1212250 : Nat := 414977948941991533333313

theorem tailTrace_1212250 : CollatzResearch.WordTrace tailWord_1212250 prefixEnd_1212250 414977948941991533333313 := by
  unfold tailWord_1212250
  simp only [CollatzResearch.WordTrace]
  refine ⟨11053597464558190165536551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29476259905488507108097469 11053597464558190165536551)
  ·
    refine ⟨16580396196837285248304827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11053597464558190165536551 16580396196837285248304827)
    ·
      refine ⟨24870594295255927872457241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16580396196837285248304827 24870594295255927872457241)
      ·
        refine ⟨18652945721441945904342931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24870594295255927872457241 18652945721441945904342931)
        ·
          refine ⟨27979418582162918856514397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18652945721441945904342931 27979418582162918856514397)
          ·
            refine ⟨10492281968311094571192899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27979418582162918856514397 10492281968311094571192899)
            ·
              refine ⟨15738422952466641856789349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10492281968311094571192899 15738422952466641856789349)
              ·
                refine ⟨2950954303587495348148003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15738422952466641856789349 2950954303587495348148003)
                ·
                  refine ⟨4426431455381243022222005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2950954303587495348148003 4426431455381243022222005)
                  ·
                    refine ⟨414977948941991533333313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4426431455381243022222005 414977948941991533333313)
                    ·
                      rfl

theorem cell22_1212250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 4, 1, 5].length) (baseStart_1212250 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1212250 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1212250 prefixEnd_1212250 := by exact prefixLift 1212250
  have htrace : WordTrace (prefixWord ++ tailWord_1212250) baseStart_1212250 baseEnd_1212250 := by
    simpa [prefixWord, tailWord_1212250, baseEnd_1212250] using wordTrace_append hprefix tailTrace_1212250
  have hstable : (prefixWord ++ tailWord_1212250).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1212250).length < 2 ^ (prefixWord ++ tailWord_1212250).sum := by decide
  have hdescent : baseEnd_1212250 < baseStart_1212250 := by decide
  rcases family_descends (prefixWord ++ tailWord_1212250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1212265 : List Nat := [1, 2, 1, 1, 1, 3, 1, 6, 2, 4]
def baseStart_1212265 : Nat := 118140960795 + 1212265 * 2 ^ 59
def prefixEnd_1212265 : Nat := 4983230072969 + 3 ^ 40 * 1212265 * 2
def baseEnd_1212265 : Nat := 414983083748536494208267

theorem tailTrace_1212265 : CollatzResearch.WordTrace tailWord_1212265 prefixEnd_1212265 414983083748536494208267 := by
  unfold tailWord_1212265
  simp only [CollatzResearch.WordTrace]
  refine ⟨44214936953178418223942249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29476624635452278815961499 44214936953178418223942249)
  ·
    refine ⟨33161202714883813667956687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44214936953178418223942249 33161202714883813667956687)
    ·
      refine ⟨49741804072325720501935031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33161202714883813667956687 49741804072325720501935031)
      ·
        refine ⟨74612706108488580752902547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49741804072325720501935031 74612706108488580752902547)
        ·
          refine ⟨111919059162732871129353821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74612706108488580752902547 111919059162732871129353821)
          ·
            refine ⟨41969647186024826673507683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 111919059162732871129353821 41969647186024826673507683)
            ·
              refine ⟨62954470779037240010261525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41969647186024826673507683 62954470779037240010261525)
              ·
                refine ⟨2950990817767370625481009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 62954470779037240010261525 2950990817767370625481009)
                ·
                  refine ⟨2213243113325527969110757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2950990817767370625481009 2213243113325527969110757)
                  ·
                    refine ⟨414983083748536494208267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2213243113325527969110757 414983083748536494208267)
                    ·
                      rfl

theorem cell22_1212265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 6, 2, 4].length) (baseStart_1212265 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1212265 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1212265 prefixEnd_1212265 := by exact prefixLift 1212265
  have htrace : WordTrace (prefixWord ++ tailWord_1212265) baseStart_1212265 baseEnd_1212265 := by
    simpa [prefixWord, tailWord_1212265, baseEnd_1212265] using wordTrace_append hprefix tailTrace_1212265
  have hstable : (prefixWord ++ tailWord_1212265).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1212265).length < 2 ^ (prefixWord ++ tailWord_1212265).sum := by decide
  have hdescent : baseEnd_1212265 < baseStart_1212265 := by decide
  rcases family_descends (prefixWord ++ tailWord_1212265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1212415 : List Nat := [1, 1, 2, 2, 1, 2, 1, 12]
def baseStart_1212415 : Nat := 118140960795 + 1212415 * 2 ^ 59
def prefixEnd_1212415 : Nat := 4983230072969 + 3 ^ 40 * 1212415 * 2
def baseEnd_1212415 : Nat := 46114936868220678106423

theorem tailTrace_1212415 : CollatzResearch.WordTrace tailWord_1212415 prefixEnd_1212415 46114936868220678106423 := by
  unfold tailWord_1212415
  simp only [CollatzResearch.WordTrace]
  refine ⟨44220407902634993841902699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29480271935089995894601799 44220407902634993841902699)
  ·
    refine ⟨66330611853952490762854049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44220407902634993841902699 66330611853952490762854049)
    ·
      refine ⟨49747958890464368072140537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66330611853952490762854049 49747958890464368072140537)
      ·
        refine ⟨37310969167848276054105403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49747958890464368072140537 37310969167848276054105403)
        ·
          refine ⟨55966453751772414081158105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37310969167848276054105403 55966453751772414081158105)
          ·
            refine ⟨41974840313829310560868579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55966453751772414081158105 41974840313829310560868579)
            ·
              refine ⟨62962260470743965841302869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41974840313829310560868579 62962260470743965841302869)
              ·
                refine ⟨46114936868220678106423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 62962260470743965841302869 46114936868220678106423)
                ·
                  rfl

theorem cell22_1212415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 12].length) (baseStart_1212415 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1212415 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1212415 prefixEnd_1212415 := by exact prefixLift 1212415
  have htrace : WordTrace (prefixWord ++ tailWord_1212415) baseStart_1212415 baseEnd_1212415 := by
    simpa [prefixWord, tailWord_1212415, baseEnd_1212415] using wordTrace_append hprefix tailTrace_1212415
  have hstable : (prefixWord ++ tailWord_1212415).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1212415).length < 2 ^ (prefixWord ++ tailWord_1212415).sum := by decide
  have hdescent : baseEnd_1212415 < baseStart_1212415 := by decide
  rcases family_descends (prefixWord ++ tailWord_1212415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1212417 : List Nat := [1, 2, 4, 1, 2, 1, 3, 1, 1, 6]
def baseStart_1212417 : Nat := 118140960795 + 1212417 * 2 ^ 59
def prefixEnd_1212417 : Nat := 4983230072969 + 3 ^ 40 * 1212417 * 2
def baseEnd_1212417 : Nat := 415035116454858764407801

theorem tailTrace_1212417 : CollatzResearch.WordTrace tailWord_1212417 prefixEnd_1212417 415035116454858764407801 := by
  unfold tailWord_1212417
  simp only [CollatzResearch.WordTrace]
  refine ⟨44220480848627748183475505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29480320565751832122317003 44220480848627748183475505)
  ·
    refine ⟨33165360636470811137606629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44220480848627748183475505 33165360636470811137606629)
    ·
      refine ⟨6218505119338277088301243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33165360636470811137606629 6218505119338277088301243)
      ·
        refine ⟨9327757679007415632451865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6218505119338277088301243 9327757679007415632451865)
        ·
          refine ⟨6995818259255561724338899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9327757679007415632451865 6995818259255561724338899)
          ·
            refine ⟨10493727388883342586508349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6995818259255561724338899 10493727388883342586508349)
            ·
              refine ⟨3935147770831253469940631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10493727388883342586508349 3935147770831253469940631)
              ·
                refine ⟨5902721656246880204910947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3935147770831253469940631 5902721656246880204910947)
                ·
                  refine ⟨8854082484370320307366421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5902721656246880204910947 8854082484370320307366421)
                  ·
                    refine ⟨415035116454858764407801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8854082484370320307366421 415035116454858764407801)
                    ·
                      rfl

theorem cell22_1212417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 1, 1, 6].length) (baseStart_1212417 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1212417 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1212417 prefixEnd_1212417 := by exact prefixLift 1212417
  have htrace : WordTrace (prefixWord ++ tailWord_1212417) baseStart_1212417 baseEnd_1212417 := by
    simpa [prefixWord, tailWord_1212417, baseEnd_1212417] using wordTrace_append hprefix tailTrace_1212417
  have hstable : (prefixWord ++ tailWord_1212417).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1212417).length < 2 ^ (prefixWord ++ tailWord_1212417).sum := by decide
  have hdescent : baseEnd_1212417 < baseStart_1212417 := by decide
  rcases family_descends (prefixWord ++ tailWord_1212417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1212464 : List Nat := [2, 1, 1, 1, 2, 5, 2, 2, 3, 3]
def baseStart_1212464 : Nat := 118140960795 + 1212464 * 2 ^ 59
def prefixEnd_1212464 : Nat := 4983230072969 + 3 ^ 40 * 1212464 * 2
def baseEnd_1212464 : Nat := 415051205515366308482657

theorem tailTrace_1212464 : CollatzResearch.WordTrace tailWord_1212464 prefixEnd_1212464 415051205515366308482657 := by
  unfold tailWord_1212464
  simp only [CollatzResearch.WordTrace]
  refine ⟨22111097539728737605218223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29481463386304983473624297 22111097539728737605218223)
  ·
    refine ⟨33166646309593106407827335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22111097539728737605218223 33166646309593106407827335)
    ·
      refine ⟨49749969464389659611741003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33166646309593106407827335 49749969464389659611741003)
      ·
        refine ⟨74624954196584489417611505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49749969464389659611741003 74624954196584489417611505)
        ·
          refine ⟨55968715647438367063208629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74624954196584489417611505 55968715647438367063208629)
          ·
            refine ⟨5247067091947346912175809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 55968715647438367063208629 5247067091947346912175809)
            ·
              refine ⟨3935300318960510184131857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5247067091947346912175809 3935300318960510184131857)
              ·
                refine ⟨2951475239220382638098893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3935300318960510184131857 2951475239220382638098893)
                ·
                  refine ⟨1106803214707643489287085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2951475239220382638098893 1106803214707643489287085)
                  ·
                    refine ⟨415051205515366308482657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1106803214707643489287085 415051205515366308482657)
                    ·
                      rfl

theorem cell22_1212464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2, 2, 3, 3].length) (baseStart_1212464 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1212464 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1212464 prefixEnd_1212464 := by exact prefixLift 1212464
  have htrace : WordTrace (prefixWord ++ tailWord_1212464) baseStart_1212464 baseEnd_1212464 := by
    simpa [prefixWord, tailWord_1212464, baseEnd_1212464] using wordTrace_append hprefix tailTrace_1212464
  have hstable : (prefixWord ++ tailWord_1212464).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1212464).length < 2 ^ (prefixWord ++ tailWord_1212464).sum := by decide
  have hdescent : baseEnd_1212464 < baseStart_1212464 := by decide
  rcases family_descends (prefixWord ++ tailWord_1212464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1212477 : List Nat := [1, 4, 1, 3, 1, 1, 1, 1, 9]
def baseStart_1212477 : Nat := 118140960795 + 1212477 * 2 ^ 59
def prefixEnd_1212477 : Nat := 4983230072969 + 3 ^ 40 * 1212477 * 2
def baseEnd_1212477 : Nat := 138351885227012869302539

theorem tailTrace_1212477 : CollatzResearch.WordTrace tailWord_1212477 prefixEnd_1212477 138351885227012869302539 := by
  unfold tailWord_1212477
  simp only [CollatzResearch.WordTrace]
  refine ⟨44222669228410378430659685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29481779485606918953773123 44222669228410378430659685)
  ·
    refine ⟨8291750480326945955748691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44222669228410378430659685 8291750480326945955748691)
    ·
      refine ⟨12437625720490418933623037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8291750480326945955748691 12437625720490418933623037)
      ·
        refine ⟨4664109645183907100108639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12437625720490418933623037 4664109645183907100108639)
        ·
          refine ⟨6996164467775860650162959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4664109645183907100108639 6996164467775860650162959)
          ·
            refine ⟨10494246701663790975244439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6996164467775860650162959 10494246701663790975244439)
            ·
              refine ⟨15741370052495686462866659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10494246701663790975244439 15741370052495686462866659)
              ·
                refine ⟨23612055078743529694299989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15741370052495686462866659 23612055078743529694299989)
                ·
                  refine ⟨138351885227012869302539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 23612055078743529694299989 138351885227012869302539)
                  ·
                    rfl

theorem cell22_1212477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 1, 9].length) (baseStart_1212477 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1212477 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1212477 prefixEnd_1212477 := by exact prefixLift 1212477
  have htrace : WordTrace (prefixWord ++ tailWord_1212477) baseStart_1212477 baseEnd_1212477 := by
    simpa [prefixWord, tailWord_1212477, baseEnd_1212477] using wordTrace_append hprefix tailTrace_1212477
  have hstable : (prefixWord ++ tailWord_1212477).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1212477).length < 2 ^ (prefixWord ++ tailWord_1212477).sum := by decide
  have hdescent : baseEnd_1212477 < baseStart_1212477 := by decide
  rcases family_descends (prefixWord ++ tailWord_1212477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1212492 : List Nat := [2, 2, 1, 3, 1, 1, 2, 1, 4, 5]
def baseStart_1212492 : Nat := 118140960795 + 1212492 * 2 ^ 59
def prefixEnd_1212492 : Nat := 4983230072969 + 3 ^ 40 * 1212492 * 2
def baseEnd_1212492 : Nat := 415060790487583568782571

theorem tailTrace_1212492 : CollatzResearch.WordTrace tailWord_1212492 prefixEnd_1212492 415060790487583568782571 := by
  unfold tailWord_1212492
  simp only [CollatzResearch.WordTrace]
  refine ⟨22111608161678017996227865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29482144215570690661637153 22111608161678017996227865)
  ·
    refine ⟨16583706121258513497170899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22111608161678017996227865 16583706121258513497170899)
    ·
      refine ⟨24875559181887770245756349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16583706121258513497170899 24875559181887770245756349)
      ·
        refine ⟨9328334693207913842158631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24875559181887770245756349 9328334693207913842158631)
        ·
          refine ⟨13992502039811870763237947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9328334693207913842158631 13992502039811870763237947)
          ·
            refine ⟨20988753059717806144856921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13992502039811870763237947 20988753059717806144856921)
            ·
              refine ⟨15741564794788354608642691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20988753059717806144856921 15741564794788354608642691)
              ·
                refine ⟨23612347192182531912964037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15741564794788354608642691 23612347192182531912964037)
                ·
                  refine ⟨4427315098534224733680757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23612347192182531912964037 4427315098534224733680757)
                  ·
                    refine ⟨415060790487583568782571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4427315098534224733680757 415060790487583568782571)
                    ·
                      rfl

theorem cell22_1212492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 1, 4, 5].length) (baseStart_1212492 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1212492 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1212492 prefixEnd_1212492 := by exact prefixLift 1212492
  have htrace : WordTrace (prefixWord ++ tailWord_1212492) baseStart_1212492 baseEnd_1212492 := by
    simpa [prefixWord, tailWord_1212492, baseEnd_1212492] using wordTrace_append hprefix tailTrace_1212492
  have hstable : (prefixWord ++ tailWord_1212492).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1212492).length < 2 ^ (prefixWord ++ tailWord_1212492).sum := by decide
  have hdescent : baseEnd_1212492 < baseStart_1212492 := by decide
  rcases family_descends (prefixWord ++ tailWord_1212492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1212498 : List Nat := [3, 2, 2, 1, 4, 2, 1, 1, 3, 3]
def baseStart_1212498 : Nat := 118140960795 + 1212498 * 2 ^ 59
def prefixEnd_1212498 : Nat := 4983230072969 + 3 ^ 40 * 1212498 * 2
def baseEnd_1212498 : Nat := 415062844410201553132553

theorem tailTrace_1212498 : CollatzResearch.WordTrace tailWord_1212498 prefixEnd_1212498 415062844410201553132553 := by
  unfold tailWord_1212498
  simp only [CollatzResearch.WordTrace]
  refine ⟨11055858790333574754293537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29482290107556199344782765 11055858790333574754293537)
  ·
    refine ⟨8291894092750181065720153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11055858790333574754293537 8291894092750181065720153)
    ·
      refine ⟨6218920569562635799290115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8291894092750181065720153 6218920569562635799290115)
      ·
        refine ⟨9328380854343953698935173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6218920569562635799290115 9328380854343953698935173)
        ·
          refine ⟨1749071410189491318550345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9328380854343953698935173 1749071410189491318550345)
          ·
            refine ⟨1311803557642118488912759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1749071410189491318550345 1311803557642118488912759)
            ·
              refine ⟨1967705336463177733369139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1311803557642118488912759 1967705336463177733369139)
              ·
                refine ⟨2951558004694766600053709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1967705336463177733369139 2951558004694766600053709)
                ·
                  refine ⟨1106834251760537475020141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2951558004694766600053709 1106834251760537475020141)
                  ·
                    refine ⟨415062844410201553132553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1106834251760537475020141 415062844410201553132553)
                    ·
                      rfl

theorem cell22_1212498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 1, 1, 3, 3].length) (baseStart_1212498 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1212498 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1212498 prefixEnd_1212498 := by exact prefixLift 1212498
  have htrace : WordTrace (prefixWord ++ tailWord_1212498) baseStart_1212498 baseEnd_1212498 := by
    simpa [prefixWord, tailWord_1212498, baseEnd_1212498] using wordTrace_append hprefix tailTrace_1212498
  have hstable : (prefixWord ++ tailWord_1212498).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1212498).length < 2 ^ (prefixWord ++ tailWord_1212498).sum := by decide
  have hdescent : baseEnd_1212498 < baseStart_1212498 := by decide
  rcases family_descends (prefixWord ++ tailWord_1212498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1212524 : List Nat := [2, 2, 1, 1, 3, 4, 1, 1, 3, 4]
def baseStart_1212524 : Nat := 118140960795 + 1212524 * 2 ^ 59
def prefixEnd_1212524 : Nat := 4983230072969 + 3 ^ 40 * 1212524 * 2
def baseEnd_1212524 : Nat := 415071744741546151982473

theorem tailTrace_1212524 : CollatzResearch.WordTrace tailWord_1212524 prefixEnd_1212524 415071744741546151982473 := by
  unfold tailWord_1212524
  simp only [CollatzResearch.WordTrace]
  refine ⟨22112191729620052728810313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29482922306160070305080417 22112191729620052728810313)
  ·
    refine ⟨16584143797215039546607735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22112191729620052728810313 16584143797215039546607735)
    ·
      refine ⟨24876215695822559319911603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16584143797215039546607735 24876215695822559319911603)
      ·
        refine ⟨37314323543733838979867405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24876215695822559319911603 37314323543733838979867405)
        ·
          refine ⟨13992871328900189617450277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37314323543733838979867405 13992871328900189617450277)
          ·
            refine ⟨2623663374168785553271927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13992871328900189617450277 2623663374168785553271927)
            ·
              refine ⟨3935495061253178329907891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2623663374168785553271927 3935495061253178329907891)
              ·
                refine ⟨5903242591879767494861837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3935495061253178329907891 5903242591879767494861837)
                ·
                  refine ⟨2213715971954912810573189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5903242591879767494861837 2213715971954912810573189)
                  ·
                    refine ⟨415071744741546151982473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2213715971954912810573189 415071744741546151982473)
                    ·
                      rfl

theorem cell22_1212524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 4].length) (baseStart_1212524 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1212524 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1212524 prefixEnd_1212524 := by exact prefixLift 1212524
  have htrace : WordTrace (prefixWord ++ tailWord_1212524) baseStart_1212524 baseEnd_1212524 := by
    simpa [prefixWord, tailWord_1212524, baseEnd_1212524] using wordTrace_append hprefix tailTrace_1212524
  have hstable : (prefixWord ++ tailWord_1212524).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1212524).length < 2 ^ (prefixWord ++ tailWord_1212524).sum := by decide
  have hdescent : baseEnd_1212524 < baseStart_1212524 := by decide
  rcases family_descends (prefixWord ++ tailWord_1212524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1212706 : List Nat := [3, 3, 1, 1, 3, 1, 1, 1, 3, 5]
def baseStart_1212706 : Nat := 118140960795 + 1212706 * 2 ^ 59
def prefixEnd_1212706 : Nat := 4983230072969 + 3 ^ 40 * 1212706 * 2
def baseEnd_1212706 : Nat := 415134047060958343931915

theorem tailTrace_1212706 : CollatzResearch.WordTrace tailWord_1212706 prefixEnd_1212706 415134047060958343931915 := by
  unfold tailWord_1212706
  simp only [CollatzResearch.WordTrace]
  refine ⟨11057755386145187635186493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29487347696387167027163981 11057755386145187635186493)
  ·
    refine ⟨4146658269804445363194935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11057755386145187635186493 4146658269804445363194935)
    ·
      refine ⟨6219987404706668044792403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4146658269804445363194935 6219987404706668044792403)
      ·
        refine ⟨9329981107060002067188605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6219987404706668044792403 9329981107060002067188605)
        ·
          refine ⟨3498742915147500775195727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9329981107060002067188605 3498742915147500775195727)
          ·
            refine ⟨5248114372721251162793591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3498742915147500775195727 5248114372721251162793591)
            ·
              refine ⟨7872171559081876744190387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5248114372721251162793591 7872171559081876744190387)
              ·
                refine ⟨11808257338622815116285581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7872171559081876744190387 11808257338622815116285581)
                ·
                  refine ⟨4428096501983555668607093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11808257338622815116285581 4428096501983555668607093)
                  ·
                    refine ⟨415134047060958343931915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4428096501983555668607093 415134047060958343931915)
                    ·
                      rfl

theorem cell22_1212706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 1, 3, 5].length) (baseStart_1212706 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1212706 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1212706 prefixEnd_1212706 := by exact prefixLift 1212706
  have htrace : WordTrace (prefixWord ++ tailWord_1212706) baseStart_1212706 baseEnd_1212706 := by
    simpa [prefixWord, tailWord_1212706, baseEnd_1212706] using wordTrace_append hprefix tailTrace_1212706
  have hstable : (prefixWord ++ tailWord_1212706).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1212706).length < 2 ^ (prefixWord ++ tailWord_1212706).sum := by decide
  have hdescent : baseEnd_1212706 < baseStart_1212706 := by decide
  rcases family_descends (prefixWord ++ tailWord_1212706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1212723 : List Nat := [1, 1, 1, 2, 5, 1, 4, 2, 2, 3]
def baseStart_1212723 : Nat := 118140960795 + 1212723 * 2 ^ 59
def prefixEnd_1212723 : Nat := 4983230072969 + 3 ^ 40 * 1212723 * 2
def baseEnd_1212723 : Nat := 415139866508375966256863

theorem tailTrace_1212723 : CollatzResearch.WordTrace tailWord_1212723 prefixEnd_1212723 415139866508375966256863 := by
  unfold tailWord_1212723
  simp only [CollatzResearch.WordTrace]
  refine ⟨44231641585519162444114823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29487761057012774962743215 44231641585519162444114823)
  ·
    refine ⟨66347462378278743666172235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44231641585519162444114823 66347462378278743666172235)
    ·
      refine ⟨99521193567418115499258353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66347462378278743666172235 99521193567418115499258353)
      ·
        refine ⟨74640895175563586624443765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99521193567418115499258353 74640895175563586624443765)
        ·
          refine ⟨6997583922709086246041603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 74640895175563586624443765 6997583922709086246041603)
          ·
            refine ⟨10496375884063629369062405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6997583922709086246041603 10496375884063629369062405)
            ·
              refine ⟨1968070478261930506699201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10496375884063629369062405 1968070478261930506699201)
              ·
                refine ⟨1476052858696447880024401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1968070478261930506699201 1476052858696447880024401)
                ·
                  refine ⟨1107039644022335910018301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1476052858696447880024401 1107039644022335910018301)
                  ·
                    refine ⟨415139866508375966256863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1107039644022335910018301 415139866508375966256863)
                    ·
                      rfl

theorem cell22_1212723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 4, 2, 2, 3].length) (baseStart_1212723 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1212723 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1212723 prefixEnd_1212723 := by exact prefixLift 1212723
  have htrace : WordTrace (prefixWord ++ tailWord_1212723) baseStart_1212723 baseEnd_1212723 := by
    simpa [prefixWord, tailWord_1212723, baseEnd_1212723] using wordTrace_append hprefix tailTrace_1212723
  have hstable : (prefixWord ++ tailWord_1212723).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1212723).length < 2 ^ (prefixWord ++ tailWord_1212723).sum := by decide
  have hdescent : baseEnd_1212723 < baseStart_1212723 := by decide
  rcases family_descends (prefixWord ++ tailWord_1212723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1212740 : List Nat := [2, 3, 4, 1, 2, 1, 2, 1, 1, 5]
def baseStart_1212740 : Nat := 118140960795 + 1212740 * 2 ^ 59
def prefixEnd_1212740 : Nat := 4983230072969 + 3 ^ 40 * 1212740 * 2
def baseEnd_1212740 : Nat := 415145685955793588581811

theorem tailTrace_1212740 : CollatzResearch.WordTrace tailWord_1212740 prefixEnd_1212740 415145685955793588581811 := by
  unfold tailWord_1212740
  simp only [CollatzResearch.WordTrace]
  refine ⟨22116130813228787173741837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29488174417638382898322449 22116130813228787173741837)
  ·
    refine ⟨8293549054960795190153189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22116130813228787173741837 8293549054960795190153189)
    ·
      refine ⟨1555040447805149098153723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8293549054960795190153189 1555040447805149098153723)
      ·
        refine ⟨2332560671707723647230585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1555040447805149098153723 2332560671707723647230585)
        ·
          refine ⟨1749420503780792735422939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2332560671707723647230585 1749420503780792735422939)
          ·
            refine ⟨2624130755671189103134409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1749420503780792735422939 2624130755671189103134409)
            ·
              refine ⟨1968098066753391827350807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2624130755671189103134409 1968098066753391827350807)
              ·
                refine ⟨2952147100130087741026211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1968098066753391827350807 2952147100130087741026211)
                ·
                  refine ⟨4428220650195131611539317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2952147100130087741026211 4428220650195131611539317)
                  ·
                    refine ⟨415145685955793588581811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4428220650195131611539317 415145685955793588581811)
                    ·
                      rfl

theorem cell22_1212740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_1212740 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1212740 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1212740 prefixEnd_1212740 := by exact prefixLift 1212740
  have htrace : WordTrace (prefixWord ++ tailWord_1212740) baseStart_1212740 baseEnd_1212740 := by
    simpa [prefixWord, tailWord_1212740, baseEnd_1212740] using wordTrace_append hprefix tailTrace_1212740
  have hstable : (prefixWord ++ tailWord_1212740).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1212740).length < 2 ^ (prefixWord ++ tailWord_1212740).sum := by decide
  have hdescent : baseEnd_1212740 < baseStart_1212740 := by decide
  rcases family_descends (prefixWord ++ tailWord_1212740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1212779 : List Nat := [1, 1, 1, 1, 2, 2, 2, 2, 3, 7]
def baseStart_1212779 : Nat := 118140960795 + 1212779 * 2 ^ 59
def prefixEnd_1212779 : Nat := 4983230072969 + 3 ^ 40 * 1212779 * 2
def baseEnd_1212779 : Nat := 415159036452810486856691

theorem tailTrace_1212779 : CollatzResearch.WordTrace tailWord_1212779 prefixEnd_1212779 415159036452810486856691 := by
  unfold tailWord_1212779
  simp only [CollatzResearch.WordTrace]
  refine ⟨44233684073316284008153391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29489122715544189338768927 44233684073316284008153391)
  ·
    refine ⟨66350526109974426012230087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44233684073316284008153391 66350526109974426012230087)
    ·
      refine ⟨99525789164961639018345131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66350526109974426012230087 99525789164961639018345131)
      ·
        refine ⟨149288683747442458527517697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99525789164961639018345131 149288683747442458527517697)
        ·
          refine ⟨111966512810581843895638273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 149288683747442458527517697 111966512810581843895638273)
          ·
            refine ⟨83974884607936382921728705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111966512810581843895638273 83974884607936382921728705)
            ·
              refine ⟨62981163455952287191296529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83974884607936382921728705 62981163455952287191296529)
              ·
                refine ⟨47235872591964215393472397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62981163455952287191296529 47235872591964215393472397)
                ·
                  refine ⟨17713452221986580772552149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47235872591964215393472397 17713452221986580772552149)
                  ·
                    refine ⟨415159036452810486856691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17713452221986580772552149 415159036452810486856691)
                    ·
                      rfl

theorem cell22_1212779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 7].length) (baseStart_1212779 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1212779 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1212779 prefixEnd_1212779 := by exact prefixLift 1212779
  have htrace : WordTrace (prefixWord ++ tailWord_1212779) baseStart_1212779 baseEnd_1212779 := by
    simpa [prefixWord, tailWord_1212779, baseEnd_1212779] using wordTrace_append hprefix tailTrace_1212779
  have hstable : (prefixWord ++ tailWord_1212779).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1212779).length < 2 ^ (prefixWord ++ tailWord_1212779).sum := by decide
  have hdescent : baseEnd_1212779 < baseStart_1212779 := by decide
  rcases family_descends (prefixWord ++ tailWord_1212779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1212781 : List Nat := [1, 5, 1, 1, 1, 2, 3, 1, 7]
def baseStart_1212781 : Nat := 118140960795 + 1212781 * 2 ^ 59
def prefixEnd_1212781 : Nat := 4983230072969 + 3 ^ 40 * 1212781 * 2
def baseEnd_1212781 : Nat := 138386573697894382768895

theorem tailTrace_1212781 : CollatzResearch.WordTrace tailWord_1212781 prefixEnd_1212781 138386573697894382768895 := by
  unfold tailWord_1212781
  simp only [CollatzResearch.WordTrace]
  refine ⟨44233757019309038349726197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29489171346206025566484131 44233757019309038349726197)
  ·
    refine ⟨4146914720560222345286831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 44233757019309038349726197 4146914720560222345286831)
    ·
      refine ⟨6220372080840333517930247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4146914720560222345286831 6220372080840333517930247)
      ·
        refine ⟨9330558121260500276895371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6220372080840333517930247 9330558121260500276895371)
        ·
          refine ⟨13995837181890750415343057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9330558121260500276895371 13995837181890750415343057)
          ·
            refine ⟨10496877886418062811507293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13995837181890750415343057 10496877886418062811507293)
            ·
              refine ⟨3936329207406773554315235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10496877886418062811507293 3936329207406773554315235)
              ·
                refine ⟨5904493811110160331472853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3936329207406773554315235 5904493811110160331472853)
                ·
                  refine ⟨138386573697894382768895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5904493811110160331472853 138386573697894382768895)
                  ·
                    rfl

theorem cell22_1212781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 3, 1, 7].length) (baseStart_1212781 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1212781 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1212781 prefixEnd_1212781 := by exact prefixLift 1212781
  have htrace : WordTrace (prefixWord ++ tailWord_1212781) baseStart_1212781 baseEnd_1212781 := by
    simpa [prefixWord, tailWord_1212781, baseEnd_1212781] using wordTrace_append hprefix tailTrace_1212781
  have hstable : (prefixWord ++ tailWord_1212781).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1212781).length < 2 ^ (prefixWord ++ tailWord_1212781).sum := by decide
  have hdescent : baseEnd_1212781 < baseStart_1212781 := by decide
  rcases family_descends (prefixWord ++ tailWord_1212781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1212856 : List Nat := [2, 1, 2, 1, 2, 2, 1, 1, 6, 4]
def baseStart_1212856 : Nat := 118140960795 + 1212856 * 2 ^ 59
def prefixEnd_1212856 : Nat := 4983230072969 + 3 ^ 40 * 1212856 * 2
def baseEnd_1212856 : Nat := 415185395126407952681455

theorem tailTrace_1212856 : CollatzResearch.WordTrace tailWord_1212856 prefixEnd_1212856 415185395126407952681455 := by
  unfold tailWord_1212856
  simp only [CollatzResearch.WordTrace]
  refine ⟨22118246247018663079353211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29490994996024884105804281 22118246247018663079353211)
  ·
    refine ⟨33177369370527994619029817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22118246247018663079353211 33177369370527994619029817)
    ·
      refine ⟨24883027027895995964272363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33177369370527994619029817 24883027027895995964272363)
      ·
        refine ⟨37324540541843993946408545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24883027027895995964272363 37324540541843993946408545)
        ·
          refine ⟨27993405406382995459806409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37324540541843993946408545 27993405406382995459806409)
          ·
            refine ⟨20995054054787246594854807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27993405406382995459806409 20995054054787246594854807)
            ·
              refine ⟨31492581082180869892282211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20995054054787246594854807 31492581082180869892282211)
              ·
                refine ⟨47238871623271304838423317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31492581082180869892282211 47238871623271304838423317)
                ·
                  refine ⟨2214322107340842414301093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 47238871623271304838423317 2214322107340842414301093)
                  ·
                    refine ⟨415185395126407952681455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2214322107340842414301093 415185395126407952681455)
                    ·
                      rfl

theorem cell22_1212856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 6, 4].length) (baseStart_1212856 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1212856 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1212856 prefixEnd_1212856 := by exact prefixLift 1212856
  have htrace : WordTrace (prefixWord ++ tailWord_1212856) baseStart_1212856 baseEnd_1212856 := by
    simpa [prefixWord, tailWord_1212856, baseEnd_1212856] using wordTrace_append hprefix tailTrace_1212856
  have hstable : (prefixWord ++ tailWord_1212856).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1212856).length < 2 ^ (prefixWord ++ tailWord_1212856).sum := by decide
  have hdescent : baseEnd_1212856 < baseStart_1212856 := by decide
  rcases family_descends (prefixWord ++ tailWord_1212856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1212871 : List Nat := [1, 1, 4, 1, 1, 4, 2, 8]
def baseStart_1212871 : Nat := 118140960795 + 1212871 * 2 ^ 59
def prefixEnd_1212871 : Nat := 4983230072969 + 3 ^ 40 * 1212871 * 2
def baseEnd_1212871 : Nat := 46132281103661434839601

theorem tailTrace_1212871 : CollatzResearch.WordTrace tailWord_1212871 prefixEnd_1212871 46132281103661434839601 := by
  unfold tailWord_1212871
  simp only [CollatzResearch.WordTrace]
  refine ⟨44237039588982983720502467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29491359725988655813668311 44237039588982983720502467)
  ·
    refine ⟨66355559383474475580753701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44237039588982983720502467 66355559383474475580753701)
    ·
      refine ⟨12441667384401464171391319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 66355559383474475580753701 12441667384401464171391319)
      ·
        refine ⟨18662501076602196257086979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12441667384401464171391319 18662501076602196257086979)
        ·
          refine ⟨27993751614903294385630469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18662501076602196257086979 27993751614903294385630469)
          ·
            refine ⟨5248828427794367697305713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27993751614903294385630469 5248828427794367697305713)
            ·
              refine ⟨3936621320845775772979285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5248828427794367697305713 3936621320845775772979285)
              ·
                refine ⟨46132281103661434839601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3936621320845775772979285 46132281103661434839601)
                ·
                  rfl

theorem cell22_1212871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 2, 8].length) (baseStart_1212871 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1212871 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1212871 prefixEnd_1212871 := by exact prefixLift 1212871
  have htrace : WordTrace (prefixWord ++ tailWord_1212871) baseStart_1212871 baseEnd_1212871 := by
    simpa [prefixWord, tailWord_1212871, baseEnd_1212871] using wordTrace_append hprefix tailTrace_1212871
  have hstable : (prefixWord ++ tailWord_1212871).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1212871).length < 2 ^ (prefixWord ++ tailWord_1212871).sum := by decide
  have hdescent : baseEnd_1212871 < baseStart_1212871 := by decide
  rcases family_descends (prefixWord ++ tailWord_1212871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1212918 : List Nat := [5, 1, 1, 1, 2, 1, 1, 2, 2, 6]
def baseStart_1212918 : Nat := 118140960795 + 1212918 * 2 ^ 59
def prefixEnd_1212918 : Nat := 4983230072969 + 3 ^ 40 * 1212918 * 2
def baseEnd_1212918 : Nat := 415206618993460457631265

theorem tailTrace_1212918 : CollatzResearch.WordTrace tailWord_1212918 prefixEnd_1212918 415206618993460457631265 := by
  unfold tailWord_1212918
  simp only [CollatzResearch.WordTrace]
  refine ⟨2764922113738294421716463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 29492502546541807164975605 2764922113738294421716463)
  ·
    refine ⟨4147383170607441632574695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2764922113738294421716463 4147383170607441632574695)
    ·
      refine ⟨6221074755911162448862043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4147383170607441632574695 6221074755911162448862043)
      ·
        refine ⟨9331612133866743673293065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6221074755911162448862043 9331612133866743673293065)
        ·
          refine ⟨6998709100400057754969799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9331612133866743673293065 6998709100400057754969799)
          ·
            refine ⟨10498063650600086632454699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6998709100400057754969799 10498063650600086632454699)
            ·
              refine ⟨15747095475900129948682049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10498063650600086632454699 15747095475900129948682049)
              ·
                refine ⟨11810321606925097461511537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15747095475900129948682049 11810321606925097461511537)
                ·
                  refine ⟨8857741205193823096133653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11810321606925097461511537 8857741205193823096133653)
                  ·
                    refine ⟨415206618993460457631265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8857741205193823096133653 415206618993460457631265)
                    ·
                      rfl

theorem cell22_1212918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 2, 2, 6].length) (baseStart_1212918 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1212918 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1212918 prefixEnd_1212918 := by exact prefixLift 1212918
  have htrace : WordTrace (prefixWord ++ tailWord_1212918) baseStart_1212918 baseEnd_1212918 := by
    simpa [prefixWord, tailWord_1212918, baseEnd_1212918] using wordTrace_append hprefix tailTrace_1212918
  have hstable : (prefixWord ++ tailWord_1212918).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1212918).length < 2 ^ (prefixWord ++ tailWord_1212918).sum := by decide
  have hdescent : baseEnd_1212918 < baseStart_1212918 := by decide
  rcases family_descends (prefixWord ++ tailWord_1212918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1212931 : List Nat := [1, 1, 1, 3, 2, 1, 3, 2, 1, 7]
def baseStart_1212931 : Nat := 118140960795 + 1212931 * 2 ^ 59
def prefixEnd_1212931 : Nat := 4983230072969 + 3 ^ 40 * 1212931 * 2
def baseEnd_1212931 : Nat := 415211069159132757056225

theorem tailTrace_1212931 : CollatzResearch.WordTrace tailWord_1212931 prefixEnd_1212931 415211069159132757056225 := by
  unfold tailWord_1212931
  simp only [CollatzResearch.WordTrace]
  refine ⟨44239227968765613967686647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29492818645843742645124431 44239227968765613967686647)
  ·
    refine ⟨66358841953148420951529971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44239227968765613967686647 66358841953148420951529971)
    ·
      refine ⟨99538262929722631427294957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66358841953148420951529971 99538262929722631427294957)
      ·
        refine ⟨37326848598645986785235609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 99538262929722631427294957 37326848598645986785235609)
        ·
          refine ⟨27995136448984490088926707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37326848598645986785235609 27995136448984490088926707)
          ·
            refine ⟨41992704673476735133390061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27995136448984490088926707 41992704673476735133390061)
            ·
              refine ⟨15747264252553775675021273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41992704673476735133390061 15747264252553775675021273)
              ·
                refine ⟨11810448189415331756265955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15747264252553775675021273 11810448189415331756265955)
                ·
                  refine ⟨17715672284122997634398933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11810448189415331756265955 17715672284122997634398933)
                  ·
                    refine ⟨415211069159132757056225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17715672284122997634398933 415211069159132757056225)
                    ·
                      rfl

theorem cell22_1212931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 2, 1, 7].length) (baseStart_1212931 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1212931 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1212931 prefixEnd_1212931 := by exact prefixLift 1212931
  have htrace : WordTrace (prefixWord ++ tailWord_1212931) baseStart_1212931 baseEnd_1212931 := by
    simpa [prefixWord, tailWord_1212931, baseEnd_1212931] using wordTrace_append hprefix tailTrace_1212931
  have hstable : (prefixWord ++ tailWord_1212931).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1212931).length < 2 ^ (prefixWord ++ tailWord_1212931).sum := by decide
  have hdescent : baseEnd_1212931 < baseStart_1212931 := by decide
  rcases family_descends (prefixWord ++ tailWord_1212931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1212978 : List Nat := [3, 2, 1, 1, 2, 1, 4, 2, 6]
def baseStart_1212978 : Nat := 118140960795 + 1212978 * 2 ^ 59
def prefixEnd_1212978 : Nat := 4983230072969 + 3 ^ 40 * 1212978 * 2
def baseEnd_1212978 : Nat := 138409052739880100377027

theorem tailTrace_1212978 : CollatzResearch.WordTrace tailWord_1212978 prefixEnd_1212978 138409052739880100377027 := by
  unfold tailWord_1212978
  simp only [CollatzResearch.WordTrace]
  refine ⟨11060235549898835248661897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29493961466396893996431725 11060235549898835248661897)
  ·
    refine ⟨8295176662424126436496423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11060235549898835248661897 8295176662424126436496423)
    ·
      refine ⟨12442764993636189654744635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8295176662424126436496423 12442764993636189654744635)
      ·
        refine ⟨18664147490454284482116953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12442764993636189654744635 18664147490454284482116953)
        ·
          refine ⟨13998110617840713361587715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18664147490454284482116953 13998110617840713361587715)
          ·
            refine ⟨20997165926761070042381573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13998110617840713361587715 20997165926761070042381573)
            ·
              refine ⟨3936968611267700632946545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20997165926761070042381573 3936968611267700632946545)
              ·
                refine ⟨2952726458450775474709909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3936968611267700632946545 2952726458450775474709909)
                ·
                  refine ⟨138409052739880100377027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2952726458450775474709909 138409052739880100377027)
                  ·
                    rfl

theorem cell22_1212978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4, 2, 6].length) (baseStart_1212978 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1212978 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1212978 prefixEnd_1212978 := by exact prefixLift 1212978
  have htrace : WordTrace (prefixWord ++ tailWord_1212978) baseStart_1212978 baseEnd_1212978 := by
    simpa [prefixWord, tailWord_1212978, baseEnd_1212978] using wordTrace_append hprefix tailTrace_1212978
  have hstable : (prefixWord ++ tailWord_1212978).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1212978).length < 2 ^ (prefixWord ++ tailWord_1212978).sum := by decide
  have hdescent : baseEnd_1212978 < baseStart_1212978 := by decide
  rcases family_descends (prefixWord ++ tailWord_1212978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1213010 : List Nat := [3, 2, 2, 1, 2, 1, 1, 3, 4, 3]
def baseStart_1213010 : Nat := 118140960795 + 1213010 * 2 ^ 59
def prefixEnd_1213010 : Nat := 4983230072969 + 3 ^ 40 * 1213010 * 2
def baseEnd_1213010 : Nat := 415238112473602884330983

theorem tailTrace_1213010 : CollatzResearch.WordTrace tailWord_1213010 prefixEnd_1213010 415238112473602884330983 := by
  unfold tailWord_1213010
  simp only [CollatzResearch.WordTrace]
  refine ⟨11060527333869852614953121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29494739556986273639874989 11060527333869852614953121)
  ·
    refine ⟨8295395500402389461214841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11060527333869852614953121 8295395500402389461214841)
    ·
      refine ⟨6221546625301792095911131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8295395500402389461214841 6221546625301792095911131)
      ·
        refine ⟨9332319937952688143866697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6221546625301792095911131 9332319937952688143866697)
        ·
          refine ⟨6999239953464516107900023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9332319937952688143866697 6999239953464516107900023)
          ·
            refine ⟨10498859930196774161850035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6999239953464516107900023 10498859930196774161850035)
            ·
              refine ⟨15748289895295161242775053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10498859930196774161850035 15748289895295161242775053)
              ·
                refine ⟨5905608710735685466040645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15748289895295161242775053 5905608710735685466040645)
                ·
                  refine ⟨1107301633262941024882621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5905608710735685466040645 1107301633262941024882621)
                  ·
                    refine ⟨415238112473602884330983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1107301633262941024882621 415238112473602884330983)
                    ·
                      rfl

theorem cell22_1213010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 3, 4, 3].length) (baseStart_1213010 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1213010 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1213010 prefixEnd_1213010 := by exact prefixLift 1213010
  have htrace : WordTrace (prefixWord ++ tailWord_1213010) baseStart_1213010 baseEnd_1213010 := by
    simpa [prefixWord, tailWord_1213010, baseEnd_1213010] using wordTrace_append hprefix tailTrace_1213010
  have hstable : (prefixWord ++ tailWord_1213010).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1213010).length < 2 ^ (prefixWord ++ tailWord_1213010).sum := by decide
  have hdescent : baseEnd_1213010 < baseStart_1213010 := by decide
  rcases family_descends (prefixWord ++ tailWord_1213010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1213042 : List Nat := [3, 2, 1, 2, 4, 1, 2, 1, 2, 4]
def baseStart_1213042 : Nat := 118140960795 + 1213042 * 2 ^ 59
def prefixEnd_1213042 : Nat := 4983230072969 + 3 ^ 40 * 1213042 * 2
def baseEnd_1213042 : Nat := 415249066727565467530885

theorem tailTrace_1213042 : CollatzResearch.WordTrace tailWord_1213042 prefixEnd_1213042 415249066727565467530885 := by
  unfold tailWord_1213042
  simp only [CollatzResearch.WordTrace]
  refine ⟨11060819117840869981244345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29495517647575653283318253 11060819117840869981244345)
  ·
    refine ⟨8295614338380652485933259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11060819117840869981244345 8295614338380652485933259)
    ·
      refine ⟨12443421507570978728899889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8295614338380652485933259 12443421507570978728899889)
      ·
        refine ⟨9332566130678234046674917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12443421507570978728899889 9332566130678234046674917)
        ·
          refine ⟨1749856149502168883751547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9332566130678234046674917 1749856149502168883751547)
          ·
            refine ⟨2624784224253253325627321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1749856149502168883751547 2624784224253253325627321)
            ·
              refine ⟨1968588168189939994220491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2624784224253253325627321 1968588168189939994220491)
              ·
                refine ⟨2952882252284909991330737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1968588168189939994220491 2952882252284909991330737)
                ·
                  refine ⟨2214661689213682493498053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2952882252284909991330737 2214661689213682493498053)
                  ·
                    refine ⟨415249066727565467530885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2214661689213682493498053 415249066727565467530885)
                    ·
                      rfl

theorem cell22_1213042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 2, 1, 2, 4].length) (baseStart_1213042 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1213042 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1213042 prefixEnd_1213042 := by exact prefixLift 1213042
  have htrace : WordTrace (prefixWord ++ tailWord_1213042) baseStart_1213042 baseEnd_1213042 := by
    simpa [prefixWord, tailWord_1213042, baseEnd_1213042] using wordTrace_append hprefix tailTrace_1213042
  have hstable : (prefixWord ++ tailWord_1213042).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1213042).length < 2 ^ (prefixWord ++ tailWord_1213042).sum := by decide
  have hdescent : baseEnd_1213042 < baseStart_1213042 := by decide
  rcases family_descends (prefixWord ++ tailWord_1213042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1213085 : List Nat := [1, 4, 2, 1, 1, 1, 4, 3, 5]
def baseStart_1213085 : Nat := 118140960795 + 1213085 * 2 ^ 59
def prefixEnd_1213085 : Nat := 4983230072969 + 3 ^ 40 * 1213085 * 2
def baseEnd_1213085 : Nat := 138421262168775896235251

theorem tailTrace_1213085 : CollatzResearch.WordTrace tailWord_1213085 prefixEnd_1213085 138421262168775896235251 := by
  unfold tailWord_1213085
  simp only [CollatzResearch.WordTrace]
  refine ⟨44244844810207698268792709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29496563206805132179195139 44244844810207698268792709)
  ·
    refine ⟨8295908401913943425398633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44244844810207698268792709 8295908401913943425398633)
    ·
      refine ⟨6221931301435457569048975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8295908401913943425398633 6221931301435457569048975)
      ·
        refine ⟨9332896952153186353573463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6221931301435457569048975 9332896952153186353573463)
        ·
          refine ⟨13999345428229779530360195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9332896952153186353573463 13999345428229779530360195)
          ·
            refine ⟨20999018142344669295540293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13999345428229779530360195 20999018142344669295540293)
            ·
              refine ⟨3937315901689625492913805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20999018142344669295540293 3937315901689625492913805)
              ·
                refine ⟨1476493463133609559842677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3937315901689625492913805 1476493463133609559842677)
                ·
                  refine ⟨138421262168775896235251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1476493463133609559842677 138421262168775896235251)
                  ·
                    rfl

theorem cell22_1213085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4, 3, 5].length) (baseStart_1213085 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1213085 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1213085 prefixEnd_1213085 := by exact prefixLift 1213085
  have htrace : WordTrace (prefixWord ++ tailWord_1213085) baseStart_1213085 baseEnd_1213085 := by
    simpa [prefixWord, tailWord_1213085, baseEnd_1213085] using wordTrace_append hprefix tailTrace_1213085
  have hstable : (prefixWord ++ tailWord_1213085).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1213085).length < 2 ^ (prefixWord ++ tailWord_1213085).sum := by decide
  have hdescent : baseEnd_1213085 < baseStart_1213085 := by decide
  rcases family_descends (prefixWord ++ tailWord_1213085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1213113 : List Nat := [1, 2, 1, 4, 1, 1, 1, 1, 10]
def baseStart_1213113 : Nat := 118140960795 + 1213113 * 2 ^ 59
def prefixEnd_1213113 : Nat := 4983230072969 + 3 ^ 40 * 1213113 * 2
def baseEnd_1213113 : Nat := 138424457159514983001889

theorem tailTrace_1213113 : CollatzResearch.WordTrace tailWord_1213113 prefixEnd_1213113 138424457159514983001889 := by
  unfold tailWord_1213113
  simp only [CollatzResearch.WordTrace]
  refine ⟨44245866054106259050811993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29497244036070839367207995 44245866054106259050811993)
  ·
    refine ⟨33184399540579694288108995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44245866054106259050811993 33184399540579694288108995)
    ·
      refine ⟨49776599310869541432163493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33184399540579694288108995 49776599310869541432163493)
      ·
        refine ⟨9333112370788039018530655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49776599310869541432163493 9333112370788039018530655)
        ·
          refine ⟨13999668556182058527795983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9333112370788039018530655 13999668556182058527795983)
          ·
            refine ⟨20999502834273087791693975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13999668556182058527795983 20999502834273087791693975)
            ·
              refine ⟨31499254251409631687540963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20999502834273087791693975 31499254251409631687540963)
              ·
                refine ⟨47248881377114447531311445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31499254251409631687540963 47248881377114447531311445)
                ·
                  refine ⟨138424457159514983001889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 47248881377114447531311445 138424457159514983001889)
                  ·
                    rfl

theorem cell22_1213113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 1, 10].length) (baseStart_1213113 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1213113 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1213113 prefixEnd_1213113 := by exact prefixLift 1213113
  have htrace : WordTrace (prefixWord ++ tailWord_1213113) baseStart_1213113 baseEnd_1213113 := by
    simpa [prefixWord, tailWord_1213113, baseEnd_1213113] using wordTrace_append hprefix tailTrace_1213113
  have hstable : (prefixWord ++ tailWord_1213113).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1213113).length < 2 ^ (prefixWord ++ tailWord_1213113).sum := by decide
  have hdescent : baseEnd_1213113 < baseStart_1213113 := by decide
  rcases family_descends (prefixWord ++ tailWord_1213113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1213130 : List Nat := [3, 1, 2, 1, 4, 1, 1, 3, 6]
def baseStart_1213130 : Nat := 118140960795 + 1213130 * 2 ^ 59
def prefixEnd_1213130 : Nat := 4983230072969 + 3 ^ 40 * 1213130 * 2
def baseEnd_1213130 : Nat := 138426396975320857110205

theorem tailTrace_1213130 : CollatzResearch.WordTrace tailWord_1213130 prefixEnd_1213130 138426396975320857110205 := by
  unfold tailWord_1213130
  simp only [CollatzResearch.WordTrace]
  refine ⟨11061621523761167738545211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29497657396696447302787229 11061621523761167738545211)
  ·
    refine ⟨16592432285641751607817817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11061621523761167738545211 16592432285641751607817817)
    ·
      refine ⟨12444324214231313705863363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16592432285641751607817817 12444324214231313705863363)
      ·
        refine ⟨18666486321346970558795045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12444324214231313705863363 18666486321346970558795045)
        ·
          refine ⟨3499966185252556979774071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18666486321346970558795045 3499966185252556979774071)
          ·
            refine ⟨5249949277878835469661107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3499966185252556979774071 5249949277878835469661107)
            ·
              refine ⟨7874923916818253204491661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5249949277878835469661107 7874923916818253204491661)
              ·
                refine ⟨2953096468806844951684373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7874923916818253204491661 2953096468806844951684373)
                ·
                  refine ⟨138426396975320857110205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2953096468806844951684373 138426396975320857110205)
                  ·
                    rfl

theorem cell22_1213130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 3, 6].length) (baseStart_1213130 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1213130 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1213130 prefixEnd_1213130 := by exact prefixLift 1213130
  have htrace : WordTrace (prefixWord ++ tailWord_1213130) baseStart_1213130 baseEnd_1213130 := by
    simpa [prefixWord, tailWord_1213130, baseEnd_1213130] using wordTrace_append hprefix tailTrace_1213130
  have hstable : (prefixWord ++ tailWord_1213130).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1213130).length < 2 ^ (prefixWord ++ tailWord_1213130).sum := by decide
  have hdescent : baseEnd_1213130 < baseStart_1213130 := by decide
  rcases family_descends (prefixWord ++ tailWord_1213130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1213237 : List Nat := [1, 3, 3, 1, 3, 1, 1, 4, 5]
def baseStart_1213237 : Nat := 118140960795 + 1213237 * 2 ^ 59
def prefixEnd_1213237 : Nat := 4983230072969 + 3 ^ 40 * 1213237 * 2
def baseEnd_1213237 : Nat := 138438606404216652968429

theorem tailTrace_1213237 : CollatzResearch.WordTrace tailWord_1213237 prefixEnd_1213237 138438606404216652968429 := by
  unfold tailWord_1213237
  simp only [CollatzResearch.WordTrace]
  refine ⟨44250388705657028228325965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29500259137104685485550643 44250388705657028228325965)
  ·
    refine ⟨16593895764621385585622237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44250388705657028228325965 16593895764621385585622237)
    ·
      refine ⟨6222710911733019594608339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16593895764621385585622237 6222710911733019594608339)
      ·
        refine ⟨9334066367599529391912509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6222710911733019594608339 9334066367599529391912509)
        ·
          refine ⟨3500274887849823521967191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9334066367599529391912509 3500274887849823521967191)
          ·
            refine ⟨5250412331774735282950787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3500274887849823521967191 5250412331774735282950787)
            ·
              refine ⟨7875618497662102924426181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5250412331774735282950787 7875618497662102924426181)
              ·
                refine ⟨1476678468311644298329909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7875618497662102924426181 1476678468311644298329909)
                ·
                  refine ⟨138438606404216652968429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1476678468311644298329909 138438606404216652968429)
                  ·
                    rfl

theorem cell22_1213237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 4, 5].length) (baseStart_1213237 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1213237 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1213237 prefixEnd_1213237 := by exact prefixLift 1213237
  have htrace : WordTrace (prefixWord ++ tailWord_1213237) baseStart_1213237 baseEnd_1213237 := by
    simpa [prefixWord, tailWord_1213237, baseEnd_1213237] using wordTrace_append hprefix tailTrace_1213237
  have hstable : (prefixWord ++ tailWord_1213237).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1213237).length < 2 ^ (prefixWord ++ tailWord_1213237).sum := by decide
  have hdescent : baseEnd_1213237 < baseStart_1213237 := by decide
  rcases family_descends (prefixWord ++ tailWord_1213237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1213284 : List Nat := [2, 3, 1, 1, 4, 2, 1, 3, 1, 4]
def baseStart_1213284 : Nat := 118140960795 + 1213284 * 2 ^ 59
def prefixEnd_1213284 : Nat := 4983230072969 + 3 ^ 40 * 1213284 * 2
def baseEnd_1213284 : Nat := 415331908273157502980143

theorem tailTrace_1213284 : CollatzResearch.WordTrace tailWord_1213284 prefixEnd_1213284 415331908273157502980143 := by
  unfold tailWord_1213284
  simp only [CollatzResearch.WordTrace]
  refine ⟨22126051468243377627643453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29501401957657836836857937 22126051468243377627643453)
  ·
    refine ⟨8297269300591266610366295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22126051468243377627643453 8297269300591266610366295)
    ·
      refine ⟨12445903950886899915549443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8297269300591266610366295 12445903950886899915549443)
      ·
        refine ⟨18668855926330349873324165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12445903950886899915549443 18668855926330349873324165)
        ·
          refine ⟨3500410486186940601248281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18668855926330349873324165 3500410486186940601248281)
          ·
            refine ⟨2625307864640205450936211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3500410486186940601248281 2625307864640205450936211)
            ·
              refine ⟨3937961796960308176404317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2625307864640205450936211 3937961796960308176404317)
              ·
                refine ⟨1476735673860115566151619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3937961796960308176404317 1476735673860115566151619)
                ·
                  refine ⟨2215103510790173349227429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1476735673860115566151619 2215103510790173349227429)
                  ·
                    refine ⟨415331908273157502980143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2215103510790173349227429 415331908273157502980143)
                    ·
                      rfl

theorem cell22_1213284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 1, 3, 1, 4].length) (baseStart_1213284 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1213284 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1213284 prefixEnd_1213284 := by exact prefixLift 1213284
  have htrace : WordTrace (prefixWord ++ tailWord_1213284) baseStart_1213284 baseEnd_1213284 := by
    simpa [prefixWord, tailWord_1213284, baseEnd_1213284] using wordTrace_append hprefix tailTrace_1213284
  have hstable : (prefixWord ++ tailWord_1213284).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1213284).length < 2 ^ (prefixWord ++ tailWord_1213284).sum := by decide
  have hdescent : baseEnd_1213284 < baseStart_1213284 := by decide
  rcases family_descends (prefixWord ++ tailWord_1213284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1213410 : List Nat := [3, 3, 3, 1, 1, 2, 1, 4, 1, 3]
def baseStart_1213410 : Nat := 118140960795 + 1213410 * 2 ^ 59
def prefixEnd_1213410 : Nat := 4983230072969 + 3 ^ 40 * 1213410 * 2
def baseEnd_1213410 : Nat := 415375040648135174329757

theorem tailTrace_1213410 : CollatzResearch.WordTrace tailWord_1213410 prefixEnd_1213410 415375040648135174329757 := by
  unfold tailWord_1213410
  simp only [CollatzResearch.WordTrace]
  refine ⟨11064174633507569693593421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29504465689353519182915789 11064174633507569693593421)
  ·
    refine ⟨4149065487565338635097533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11064174633507569693593421 4149065487565338635097533)
    ·
      refine ⟨1555899557837001988161575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4149065487565338635097533 1555899557837001988161575)
      ·
        refine ⟨2333849336755502982242363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1555899557837001988161575 2333849336755502982242363)
        ·
          refine ⟨3500774005133254473363545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2333849336755502982242363 3500774005133254473363545)
          ·
            refine ⟨2625580503849940855022659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3500774005133254473363545 2625580503849940855022659)
            ·
              refine ⟨3938370755774911282533989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2625580503849940855022659 3938370755774911282533989)
              ·
                refine ⟨738444516707795865475123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3938370755774911282533989 738444516707795865475123)
                ·
                  refine ⟨1107666775061693798212685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 738444516707795865475123 1107666775061693798212685)
                  ·
                    refine ⟨415375040648135174329757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1107666775061693798212685 415375040648135174329757)
                    ·
                      rfl

theorem cell22_1213410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 1, 4, 1, 3].length) (baseStart_1213410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1213410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1213410 prefixEnd_1213410 := by exact prefixLift 1213410
  have htrace : WordTrace (prefixWord ++ tailWord_1213410) baseStart_1213410 baseEnd_1213410 := by
    simpa [prefixWord, tailWord_1213410, baseEnd_1213410] using wordTrace_append hprefix tailTrace_1213410
  have hstable : (prefixWord ++ tailWord_1213410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1213410).length < 2 ^ (prefixWord ++ tailWord_1213410).sum := by decide
  have hdescent : baseEnd_1213410 < baseStart_1213410 := by decide
  rcases family_descends (prefixWord ++ tailWord_1213410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1213451 : List Nat := [1, 1, 1, 1, 6, 3, 2, 3, 4]
def baseStart_1213451 : Nat := 118140960795 + 1213451 * 2 ^ 59
def prefixEnd_1213451 : Nat := 4983230072969 + 3 ^ 40 * 1213451 * 2
def baseEnd_1213451 : Nat := 138463025262008244684877

theorem tailTrace_1213451 : CollatzResearch.WordTrace tailWord_1213451 prefixEnd_1213451 138463025262008244684877 := by
  unfold tailWord_1213451
  simp only [CollatzResearch.WordTrace]
  refine ⟨44258193926881742776616207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29505462617921161851077471 44258193926881742776616207)
  ·
    refine ⟨66387290890322614164924311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44258193926881742776616207 66387290890322614164924311)
    ·
      refine ⟨99580936335483921247386467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66387290890322614164924311 99580936335483921247386467)
      ·
        refine ⟨149371404503225881871079701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99580936335483921247386467 149371404503225881871079701)
        ·
          refine ⟨7001784586088713212706861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 149371404503225881871079701 7001784586088713212706861)
          ·
            refine ⟨2625669219783267454765073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7001784586088713212706861 2625669219783267454765073)
            ·
              refine ⟨1969251914837450591073805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2625669219783267454765073 1969251914837450591073805)
              ·
                refine ⟨738469468064043971652677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1969251914837450591073805 738469468064043971652677)
                ·
                  refine ⟨138463025262008244684877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 738469468064043971652677 138463025262008244684877)
                  ·
                    rfl

theorem cell22_1213451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 2, 3, 4].length) (baseStart_1213451 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1213451 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1213451 prefixEnd_1213451 := by exact prefixLift 1213451
  have htrace : WordTrace (prefixWord ++ tailWord_1213451) baseStart_1213451 baseEnd_1213451 := by
    simpa [prefixWord, tailWord_1213451, baseEnd_1213451] using wordTrace_append hprefix tailTrace_1213451
  have hstable : (prefixWord ++ tailWord_1213451).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1213451).length < 2 ^ (prefixWord ++ tailWord_1213451).sum := by decide
  have hdescent : baseEnd_1213451 < baseStart_1213451 := by decide
  rcases family_descends (prefixWord ++ tailWord_1213451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1213496 : List Nat := [2, 1, 2, 1, 5, 3, 2, 6]
def baseStart_1213496 : Nat := 118140960795 + 1213496 * 2 ^ 59
def prefixEnd_1213496 : Nat := 4983230072969 + 3 ^ 40 * 1213496 * 2
def baseEnd_1213496 : Nat := 46156053356184401853277

theorem tailTrace_1213496 : CollatzResearch.WordTrace tailWord_1213496 prefixEnd_1213496 46156053356184401853277 := by
  unfold tailWord_1213496
  simp only [CollatzResearch.WordTrace]
  refine ⟨22129917605859357731002171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29506556807812476974669561 22129917605859357731002171)
  ·
    refine ⟨33194876408789036596503257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22129917605859357731002171 33194876408789036596503257)
    ·
      refine ⟨24896157306591777447377443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33194876408789036596503257 24896157306591777447377443)
      ·
        refine ⟨37344235959887666171066165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24896157306591777447377443 37344235959887666171066165)
        ·
          refine ⟨3501022121239468703537453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 37344235959887666171066165 3501022121239468703537453)
          ·
            refine ⟨1312883295464800763826545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3501022121239468703537453 1312883295464800763826545)
            ·
              refine ⟨984662471598600572869909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1312883295464800763826545 984662471598600572869909)
              ·
                refine ⟨46156053356184401853277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 984662471598600572869909 46156053356184401853277)
                ·
                  rfl

theorem cell22_1213496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 2, 6].length) (baseStart_1213496 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1213496 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1213496 prefixEnd_1213496 := by exact prefixLift 1213496
  have htrace : WordTrace (prefixWord ++ tailWord_1213496) baseStart_1213496 baseEnd_1213496 := by
    simpa [prefixWord, tailWord_1213496, baseEnd_1213496] using wordTrace_append hprefix tailTrace_1213496
  have hstable : (prefixWord ++ tailWord_1213496).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1213496).length < 2 ^ (prefixWord ++ tailWord_1213496).sum := by decide
  have hdescent : baseEnd_1213496 < baseStart_1213496 := by decide
  rcases family_descends (prefixWord ++ tailWord_1213496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1213507 : List Nat := [1, 1, 1, 3, 1, 2, 3, 1, 9]
def baseStart_1213507 : Nat := 118140960795 + 1213507 * 2 ^ 59
def prefixEnd_1213507 : Nat := 4983230072969 + 3 ^ 40 * 1213507 * 2
def baseEnd_1213507 : Nat := 138469415243486418218153

theorem tailTrace_1213507 : CollatzResearch.WordTrace tailWord_1213507 prefixEnd_1213507 138469415243486418218153 := by
  unfold tailWord_1213507
  simp only [CollatzResearch.WordTrace]
  refine ⟨44260236414678864340654775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29506824276452576227103183 44260236414678864340654775)
  ·
    refine ⟨66390354622018296510982163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44260236414678864340654775 66390354622018296510982163)
    ·
      refine ⟨99585531933027444766473245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66390354622018296510982163 99585531933027444766473245)
      ·
        refine ⟨37344574474885291787427467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 99585531933027444766473245 37344574474885291787427467)
        ·
          refine ⟨56016861712327937681141201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37344574474885291787427467 56016861712327937681141201)
          ·
            refine ⟨42012646284245953260855901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56016861712327937681141201 42012646284245953260855901)
            ·
              refine ⟨15754742356592232472820963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42012646284245953260855901 15754742356592232472820963)
              ·
                refine ⟨23632113534888348709231445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15754742356592232472820963 23632113534888348709231445)
                ·
                  refine ⟨138469415243486418218153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 23632113534888348709231445 138469415243486418218153)
                  ·
                    rfl

theorem cell22_1213507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 1, 9].length) (baseStart_1213507 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1213507 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1213507 prefixEnd_1213507 := by exact prefixLift 1213507
  have htrace : WordTrace (prefixWord ++ tailWord_1213507) baseStart_1213507 baseEnd_1213507 := by
    simpa [prefixWord, tailWord_1213507, baseEnd_1213507] using wordTrace_append hprefix tailTrace_1213507
  have hstable : (prefixWord ++ tailWord_1213507).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1213507).length < 2 ^ (prefixWord ++ tailWord_1213507).sum := by decide
  have hdescent : baseEnd_1213507 < baseStart_1213507 := by decide
  rcases family_descends (prefixWord ++ tailWord_1213507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1213524 : List Nat := [2, 4, 1, 1, 1, 1, 4, 1, 7]
def baseStart_1213524 : Nat := 118140960795 + 1213524 * 2 ^ 59
def prefixEnd_1213524 : Nat := 4983230072969 + 3 ^ 40 * 1213524 * 2
def baseEnd_1213524 : Nat := 138471355059292292326469

theorem tailTrace_1213524 : CollatzResearch.WordTrace tailWord_1213524 prefixEnd_1213524 138471355059292292326469 := by
  unfold tailWord_1213524
  simp only [CollatzResearch.WordTrace]
  refine ⟨22130428227808638122011813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29507237637078184162682417 22130428227808638122011813)
  ·
    refine ⟨4149455292714119647877215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22130428227808638122011813 4149455292714119647877215)
    ·
      refine ⟨6224182939071179471815823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4149455292714119647877215 6224182939071179471815823)
      ·
        refine ⟨9336274408606769207723735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6224182939071179471815823 9336274408606769207723735)
        ·
          refine ⟨14004411612910153811585603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9336274408606769207723735 14004411612910153811585603)
          ·
            refine ⟨21006617419365230717378405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14004411612910153811585603 21006617419365230717378405)
            ·
              refine ⟨3938740766130980759508451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21006617419365230717378405 3938740766130980759508451)
              ·
                refine ⟨5908111149196471139262677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3938740766130980759508451 5908111149196471139262677)
                ·
                  refine ⟨138471355059292292326469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5908111149196471139262677 138471355059292292326469)
                  ·
                    rfl

theorem cell22_1213524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 4, 1, 7].length) (baseStart_1213524 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1213524 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1213524 prefixEnd_1213524 := by exact prefixLift 1213524
  have htrace : WordTrace (prefixWord ++ tailWord_1213524) baseStart_1213524 baseEnd_1213524 := by
    simpa [prefixWord, tailWord_1213524, baseEnd_1213524] using wordTrace_append hprefix tailTrace_1213524
  have hstable : (prefixWord ++ tailWord_1213524).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1213524).length < 2 ^ (prefixWord ++ tailWord_1213524).sum := by decide
  have hdescent : baseEnd_1213524 < baseStart_1213524 := by decide
  rcases family_descends (prefixWord ++ tailWord_1213524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1213534 : List Nat := [4, 4, 1, 1, 1, 3, 2, 1, 2, 3]
def baseStart_1213534 : Nat := 118140960795 + 1213534 * 2 ^ 59
def prefixEnd_1213534 : Nat := 4983230072969 + 3 ^ 40 * 1213534 * 2
def baseEnd_1213534 : Nat := 415417488382240184229377

theorem tailTrace_1213534 : CollatzResearch.WordTrace tailWord_1213534 prefixEnd_1213534 415417488382240184229377 := by
  unfold tailWord_1213534
  simp only [CollatzResearch.WordTrace]
  refine ⟨5532652648197630993985957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29507480790387365301258437 5532652648197630993985957)
  ·
    refine ⟨1037372371537055811372367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5532652648197630993985957 1037372371537055811372367)
    ·
      refine ⟨1556058557305583717058551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1037372371537055811372367 1556058557305583717058551)
      ·
        refine ⟨2334087835958375575587827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1556058557305583717058551 2334087835958375575587827)
        ·
          refine ⟨3501131753937563363381741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2334087835958375575587827 3501131753937563363381741)
          ·
            refine ⟨1312924407726586261268153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3501131753937563363381741 1312924407726586261268153)
            ·
              refine ⟨984693305794939695951115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1312924407726586261268153 984693305794939695951115)
              ·
                refine ⟨1477039958692409543926673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 984693305794939695951115 1477039958692409543926673)
                ·
                  refine ⟨1107779969019307157945005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1477039958692409543926673 1107779969019307157945005)
                  ·
                    refine ⟨415417488382240184229377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1107779969019307157945005 415417488382240184229377)
                    ·
                      rfl

theorem cell22_1213534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 2, 1, 2, 3].length) (baseStart_1213534 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1213534 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1213534 prefixEnd_1213534 := by exact prefixLift 1213534
  have htrace : WordTrace (prefixWord ++ tailWord_1213534) baseStart_1213534 baseEnd_1213534 := by
    simpa [prefixWord, tailWord_1213534, baseEnd_1213534] using wordTrace_append hprefix tailTrace_1213534
  have hstable : (prefixWord ++ tailWord_1213534).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1213534).length < 2 ^ (prefixWord ++ tailWord_1213534).sum := by decide
  have hdescent : baseEnd_1213534 < baseStart_1213534 := by decide
  rcases family_descends (prefixWord ++ tailWord_1213534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1213601 : List Nat := [1, 2, 3, 3, 1, 1, 4, 1, 1, 5]
def baseStart_1213601 : Nat := 118140960795 + 1213601 * 2 ^ 59
def prefixEnd_1213601 : Nat := 4983230072969 + 3 ^ 40 * 1213601 * 2
def baseEnd_1213601 : Nat := 415440423851474342804171

theorem tailTrace_1213601 : CollatzResearch.WordTrace tailWord_1213601 prefixEnd_1213601 415440423851474342804171 := by
  unfold tailWord_1213601
  simp only [CollatzResearch.WordTrace]
  refine ⟨44263664876338318394576657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29509109917558878929717771 44263664876338318394576657)
  ·
    refine ⟨33197748657253738795932493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44263664876338318394576657 33197748657253738795932493)
    ·
      refine ⟨12449155746470152048474685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33197748657253738795932493 12449155746470152048474685)
      ·
        refine ⟨4668433404926307018178007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12449155746470152048474685 4668433404926307018178007)
        ·
          refine ⟨7002650107389460527267011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4668433404926307018178007 7002650107389460527267011)
          ·
            refine ⟨10503975161084190790900517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7002650107389460527267011 10503975161084190790900517)
            ·
              refine ⟨1969495342703285773293847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10503975161084190790900517 1969495342703285773293847)
              ·
                refine ⟨2954243014054928659940771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1969495342703285773293847 2954243014054928659940771)
                ·
                  refine ⟨4431364521082392989911157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2954243014054928659940771 4431364521082392989911157)
                  ·
                    refine ⟨415440423851474342804171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4431364521082392989911157 415440423851474342804171)
                    ·
                      rfl

theorem cell22_1213601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 4, 1, 1, 5].length) (baseStart_1213601 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1213601 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1213601 prefixEnd_1213601 := by exact prefixLift 1213601
  have htrace : WordTrace (prefixWord ++ tailWord_1213601) baseStart_1213601 baseEnd_1213601 := by
    simpa [prefixWord, tailWord_1213601, baseEnd_1213601] using wordTrace_append hprefix tailTrace_1213601
  have hstable : (prefixWord ++ tailWord_1213601).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1213601).length < 2 ^ (prefixWord ++ tailWord_1213601).sum := by decide
  have hdescent : baseEnd_1213601 < baseStart_1213601 := by decide
  rcases family_descends (prefixWord ++ tailWord_1213601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1213622 : List Nat := [5, 1, 3, 2, 1, 1, 1, 3, 1, 4]
def baseStart_1213622 : Nat := 118140960795 + 1213622 * 2 ^ 59
def prefixEnd_1213622 : Nat := 4983230072969 + 3 ^ 40 * 1213622 * 2
def baseEnd_1213622 : Nat := 415447612580637288029107

theorem tailTrace_1213622 : CollatzResearch.WordTrace tailWord_1213622 prefixEnd_1213622 415447612580637288029107 := by
  unfold tailWord_1213622
  simp only [CollatzResearch.WordTrace]
  refine ⟨2766526925578889936318195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 29509620539508159320727413 2766526925578889936318195)
  ·
    refine ⟨4149790388368334904477293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2766526925578889936318195 4149790388368334904477293)
    ·
      refine ⟨1556171395638125589178985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4149790388368334904477293 1556171395638125589178985)
      ·
        refine ⟨1167128546728594191884239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1556171395638125589178985 1167128546728594191884239)
        ·
          refine ⟨1750692820092891287826359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1167128546728594191884239 1750692820092891287826359)
          ·
            refine ⟨2626039230139336931739539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1750692820092891287826359 2626039230139336931739539)
            ·
              refine ⟨3939058845209005397609309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2626039230139336931739539 3939058845209005397609309)
              ·
                refine ⟨1477147066953377024103491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3939058845209005397609309 1477147066953377024103491)
                ·
                  refine ⟨2215720600430065536155237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1477147066953377024103491 2215720600430065536155237)
                  ·
                    refine ⟨415447612580637288029107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2215720600430065536155237 415447612580637288029107)
                    ·
                      rfl

theorem cell22_1213622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 1, 3, 1, 4].length) (baseStart_1213622 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1213622 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1213622 prefixEnd_1213622 := by exact prefixLift 1213622
  have htrace : WordTrace (prefixWord ++ tailWord_1213622) baseStart_1213622 baseEnd_1213622 := by
    simpa [prefixWord, tailWord_1213622, baseEnd_1213622] using wordTrace_append hprefix tailTrace_1213622
  have hstable : (prefixWord ++ tailWord_1213622).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1213622).length < 2 ^ (prefixWord ++ tailWord_1213622).sum := by decide
  have hdescent : baseEnd_1213622 < baseStart_1213622 := by decide
  rcases family_descends (prefixWord ++ tailWord_1213622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1213652 : List Nat := [2, 4, 1, 4, 2, 1, 1, 1, 1, 5]
def baseStart_1213652 : Nat := 118140960795 + 1213652 * 2 ^ 59
def prefixEnd_1213652 : Nat := 4983230072969 + 3 ^ 40 * 1213652 * 2
def baseEnd_1213652 : Nat := 415457882193727209779015

theorem tailTrace_1213652 : CollatzResearch.WordTrace tailWord_1213652 prefixEnd_1213652 415457882193727209779015 := by
  unfold tailWord_1213652
  simp only [CollatzResearch.WordTrace]
  refine ⟨22132762499576777052341605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29510349999435702736455473 22132762499576777052341605)
  ·
    refine ⟨4149892968670645697314051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22132762499576777052341605 4149892968670645697314051)
    ·
      refine ⟨6224839453005968545971077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4149892968670645697314051 6224839453005968545971077)
      ·
        refine ⟨1167157397438619102369577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6224839453005968545971077 1167157397438619102369577)
        ·
          refine ⟨875368048078964326777183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1167157397438619102369577 875368048078964326777183)
          ·
            refine ⟨1313052072118446490165775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 875368048078964326777183 1313052072118446490165775)
            ·
              refine ⟨1969578108177669735248663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1313052072118446490165775 1969578108177669735248663)
              ·
                refine ⟨2954367162266504602872995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1969578108177669735248663 2954367162266504602872995)
                ·
                  refine ⟨4431550743399756904309493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2954367162266504602872995 4431550743399756904309493)
                  ·
                    refine ⟨415457882193727209779015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4431550743399756904309493 415457882193727209779015)
                    ·
                      rfl

theorem cell22_1213652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 1, 1, 1, 5].length) (baseStart_1213652 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1213652 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1213652 prefixEnd_1213652 := by exact prefixLift 1213652
  have htrace : WordTrace (prefixWord ++ tailWord_1213652) baseStart_1213652 baseEnd_1213652 := by
    simpa [prefixWord, tailWord_1213652, baseEnd_1213652] using wordTrace_append hprefix tailTrace_1213652
  have hstable : (prefixWord ++ tailWord_1213652).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1213652).length < 2 ^ (prefixWord ++ tailWord_1213652).sum := by decide
  have hdescent : baseEnd_1213652 < baseStart_1213652 := by decide
  rcases family_descends (prefixWord ++ tailWord_1213652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1213697 : List Nat := [1, 2, 4, 1, 1, 4, 3, 2, 1, 3]
def baseStart_1213697 : Nat := 118140960795 + 1213697 * 2 ^ 59
def prefixEnd_1213697 : Nat := 4983230072969 + 3 ^ 40 * 1213697 * 2
def baseEnd_1213697 : Nat := 415473286613362092403877

theorem tailTrace_1213697 : CollatzResearch.WordTrace tailWord_1213697 prefixEnd_1213697 415473286613362092403877 := by
  unfold tailWord_1213697
  simp only [CollatzResearch.WordTrace]
  refine ⟨44267166283990526790071345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29511444189327017860047563 44267166283990526790071345)
  ·
    refine ⟨33200374712992895092553509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44267166283990526790071345 33200374712992895092553509)
    ·
      refine ⟨6225070258686167829853783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33200374712992895092553509 6225070258686167829853783)
      ·
        refine ⟨9337605388029251744780675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6225070258686167829853783 9337605388029251744780675)
        ·
          refine ⟨14006408082043877617171013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9337605388029251744780675 14006408082043877617171013)
          ·
            refine ⟨2626201515383227053219565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14006408082043877617171013 2626201515383227053219565)
            ·
              refine ⟨984825568268710144957337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2626201515383227053219565 984825568268710144957337)
              ·
                refine ⟨738619176201532608718003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 984825568268710144957337 738619176201532608718003)
                ·
                  refine ⟨1107928764302298913077005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 738619176201532608718003 1107928764302298913077005)
                  ·
                    refine ⟨415473286613362092403877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1107928764302298913077005 415473286613362092403877)
                    ·
                      rfl

theorem cell22_1213697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 3, 2, 1, 3].length) (baseStart_1213697 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1213697 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1213697 prefixEnd_1213697 := by exact prefixLift 1213697
  have htrace : WordTrace (prefixWord ++ tailWord_1213697) baseStart_1213697 baseEnd_1213697 := by
    simpa [prefixWord, tailWord_1213697, baseEnd_1213697] using wordTrace_append hprefix tailTrace_1213697
  have hstable : (prefixWord ++ tailWord_1213697).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1213697).length < 2 ^ (prefixWord ++ tailWord_1213697).sum := by decide
  have hdescent : baseEnd_1213697 < baseStart_1213697 := by decide
  rcases family_descends (prefixWord ++ tailWord_1213697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1213706 : List Nat := [3, 1, 2, 2, 1, 1, 1, 4, 3, 4]
def baseStart_1213706 : Nat := 118140960795 + 1213706 * 2 ^ 59
def prefixEnd_1213706 : Nat := 4983230072969 + 3 ^ 40 * 1213706 * 2
def baseEnd_1213706 : Nat := 415476367497289068928849

theorem tailTrace_1213706 : CollatzResearch.WordTrace tailWord_1213706 prefixEnd_1213706 415476367497289068928849 := by
  unfold tailWord_1213706
  simp only [CollatzResearch.WordTrace]
  refine ⟨11066873635239480331787243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29511663027305280884765981 11066873635239480331787243)
  ·
    refine ⟨16600310452859220497680865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11066873635239480331787243 16600310452859220497680865)
    ·
      refine ⟨12450232839644415373260649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16600310452859220497680865 12450232839644415373260649)
      ·
        refine ⟨9337674629733311529945487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12450232839644415373260649 9337674629733311529945487)
        ·
          refine ⟨14006511944599967294918231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9337674629733311529945487 14006511944599967294918231)
          ·
            refine ⟨21009767916899950942377347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14006511944599967294918231 21009767916899950942377347)
            ·
              refine ⟨31514651875349926413566021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21009767916899950942377347 31514651875349926413566021)
              ·
                refine ⟨5908997226628111202543629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31514651875349926413566021 5908997226628111202543629)
                ·
                  refine ⟨2215873959985541700953861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5908997226628111202543629 2215873959985541700953861)
                  ·
                    refine ⟨415476367497289068928849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2215873959985541700953861 415476367497289068928849)
                    ·
                      rfl

theorem cell22_1213706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 4, 3, 4].length) (baseStart_1213706 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1213706 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1213706 prefixEnd_1213706 := by exact prefixLift 1213706
  have htrace : WordTrace (prefixWord ++ tailWord_1213706) baseStart_1213706 baseEnd_1213706 := by
    simpa [prefixWord, tailWord_1213706, baseEnd_1213706] using wordTrace_append hprefix tailTrace_1213706
  have hstable : (prefixWord ++ tailWord_1213706).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1213706).length < 2 ^ (prefixWord ++ tailWord_1213706).sum := by decide
  have hdescent : baseEnd_1213706 < baseStart_1213706 := by decide
  rcases family_descends (prefixWord ++ tailWord_1213706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1213710 : List Nat := [4, 1, 1, 2, 1, 5, 2, 1, 5]
def baseStart_1213710 : Nat := 118140960795 + 1213710 * 2 ^ 59
def prefixEnd_1213710 : Nat := 4983230072969 + 3 ^ 40 * 1213710 * 2
def baseEnd_1213710 : Nat := 138492578926344797276279

theorem tailTrace_1213710 : CollatzResearch.WordTrace tailWord_1213710 prefixEnd_1213710 138492578926344797276279 := by
  unfold tailWord_1213710
  simp only [CollatzResearch.WordTrace]
  refine ⟨5533455054117928751286823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29511760288628953340196389 5533455054117928751286823)
  ·
    refine ⟨8300182581176893126930235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5533455054117928751286823 8300182581176893126930235)
    ·
      refine ⟨12450273871765339690395353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8300182581176893126930235 12450273871765339690395353)
      ·
        refine ⟨9337705403824004767796515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12450273871765339690395353 9337705403824004767796515)
        ·
          refine ⟨14006558105736007151694773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9337705403824004767796515 14006558105736007151694773)
          ·
            refine ⟨1313114822412750670471385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 14006558105736007151694773 1313114822412750670471385)
            ·
              refine ⟨984836116809563002853539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1313114822412750670471385 984836116809563002853539)
              ·
                refine ⟨1477254175214344504280309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 984836116809563002853539 1477254175214344504280309)
                ·
                  refine ⟨138492578926344797276279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1477254175214344504280309 138492578926344797276279)
                  ·
                    rfl

theorem cell22_1213710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 2, 1, 5].length) (baseStart_1213710 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1213710 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1213710 prefixEnd_1213710 := by exact prefixLift 1213710
  have htrace : WordTrace (prefixWord ++ tailWord_1213710) baseStart_1213710 baseEnd_1213710 := by
    simpa [prefixWord, tailWord_1213710, baseEnd_1213710] using wordTrace_append hprefix tailTrace_1213710
  have hstable : (prefixWord ++ tailWord_1213710).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1213710).length < 2 ^ (prefixWord ++ tailWord_1213710).sum := by decide
  have hdescent : baseEnd_1213710 < baseStart_1213710 := by decide
  rcases family_descends (prefixWord ++ tailWord_1213710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1213783 : List Nat := [1, 1, 3, 2, 3, 3, 3, 6]
def baseStart_1213783 : Nat := 118140960795 + 1213783 * 2 ^ 59
def prefixEnd_1213783 : Nat := 4983230072969 + 3 ^ 40 * 1213783 * 2
def baseEnd_1213783 : Nat := 46166969574542948305957

theorem tailTrace_1213783 : CollatzResearch.WordTrace tailWord_1213783 prefixEnd_1213783 46166969574542948305957 := by
  unfold tailWord_1213783
  simp only [CollatzResearch.WordTrace]
  refine ⟨44270302961678963477702003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29513535307785975651801335 44270302961678963477702003)
  ·
    refine ⟨66405454442518445216553005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44270302961678963477702003 66405454442518445216553005)
    ·
      refine ⟨24902045415944416956207377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66405454442518445216553005 24902045415944416956207377)
      ·
        refine ⟨18676534061958312717155533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24902045415944416956207377 18676534061958312717155533)
        ·
          refine ⟨7003700273234367268933325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18676534061958312717155533 7003700273234367268933325)
          ·
            refine ⟨2626387602462887725849997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7003700273234367268933325 2626387602462887725849997)
            ·
              refine ⟨984895350923582897193749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2626387602462887725849997 984895350923582897193749)
              ·
                refine ⟨46166969574542948305957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 984895350923582897193749 46166969574542948305957)
                ·
                  rfl

theorem cell22_1213783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 3, 6].length) (baseStart_1213783 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1213783 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1213783 prefixEnd_1213783 := by exact prefixLift 1213783
  have htrace : WordTrace (prefixWord ++ tailWord_1213783) baseStart_1213783 baseEnd_1213783 := by
    simpa [prefixWord, tailWord_1213783, baseEnd_1213783] using wordTrace_append hprefix tailTrace_1213783
  have hstable : (prefixWord ++ tailWord_1213783).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1213783).length < 2 ^ (prefixWord ++ tailWord_1213783).sum := by decide
  have hdescent : baseEnd_1213783 < baseStart_1213783 := by decide
  rcases family_descends (prefixWord ++ tailWord_1213783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1213815 : List Nat := [1, 1, 3, 1, 1, 2, 3, 6, 1, 3]
def baseStart_1213815 : Nat := 118140960795 + 1213815 * 2 ^ 59
def prefixEnd_1213815 : Nat := 4983230072969 + 3 ^ 40 * 1213815 * 2
def baseEnd_1213815 : Nat := 415513680424849117953515

theorem tailTrace_1213815 : CollatzResearch.WordTrace tailWord_1213815 prefixEnd_1213815 415513680424849117953515 := by
  unfold tailWord_1213815
  simp only [CollatzResearch.WordTrace]
  refine ⟨44271470097563032942866899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29514313398375355295244599 44271470097563032942866899)
  ·
    refine ⟨66407205146344549414300349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44271470097563032942866899 66407205146344549414300349)
    ·
      refine ⟨24902701929879206030362631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66407205146344549414300349 24902701929879206030362631)
      ·
        refine ⟨37354052894818809045543947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24902701929879206030362631 37354052894818809045543947)
        ·
          refine ⟨56031079342228213568315921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37354052894818809045543947 56031079342228213568315921)
          ·
            refine ⟨42023309506671160176236941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56031079342228213568315921 42023309506671160176236941)
            ·
              refine ⟨15758741065001685066088853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42023309506671160176236941 15758741065001685066088853)
              ·
                refine ⟨738690987421953987472915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 15758741065001685066088853 738690987421953987472915)
                ·
                  refine ⟨1108036481132930981209373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 738690987421953987472915 1108036481132930981209373)
                  ·
                    refine ⟨415513680424849117953515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1108036481132930981209373 415513680424849117953515)
                    ·
                      rfl

theorem cell22_1213815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 6, 1, 3].length) (baseStart_1213815 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1213815 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1213815 prefixEnd_1213815 := by exact prefixLift 1213815
  have htrace : WordTrace (prefixWord ++ tailWord_1213815) baseStart_1213815 baseEnd_1213815 := by
    simpa [prefixWord, tailWord_1213815, baseEnd_1213815] using wordTrace_append hprefix tailTrace_1213815
  have hstable : (prefixWord ++ tailWord_1213815).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1213815).length < 2 ^ (prefixWord ++ tailWord_1213815).sum := by decide
  have hdescent : baseEnd_1213815 < baseStart_1213815 := by decide
  rcases family_descends (prefixWord ++ tailWord_1213815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1213892 : List Nat := [2, 3, 3, 2, 1, 1, 3, 2, 1, 4]
def baseStart_1213892 : Nat := 118140960795 + 1213892 * 2 ^ 59
def prefixEnd_1213892 : Nat := 4983230072969 + 3 ^ 40 * 1213892 * 2
def baseEnd_1213892 : Nat := 415540039098446583778279

theorem tailTrace_1213892 : CollatzResearch.WordTrace tailWord_1213892 prefixEnd_1213892 415540039098446583778279 := by
  unfold tailWord_1213892
  simp only [CollatzResearch.WordTrace]
  refine ⟨22137139259142037546709965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29516185678856050062279953 22137139259142037546709965)
  ·
    refine ⟨8301427222178264080016237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22137139259142037546709965 8301427222178264080016237)
    ·
      refine ⟨3113035208316849030006089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8301427222178264080016237 3113035208316849030006089)
      ·
        refine ⟨2334776406237636772504567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3113035208316849030006089 2334776406237636772504567)
        ·
          refine ⟨3502164609356455158756851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2334776406237636772504567 3502164609356455158756851)
          ·
            refine ⟨5253246914034682738135277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3502164609356455158756851 5253246914034682738135277)
            ·
              refine ⟨1969967592763006026800729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5253246914034682738135277 1969967592763006026800729)
              ·
                refine ⟨1477475694572254520100547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1969967592763006026800729 1477475694572254520100547)
                ·
                  refine ⟨2216213541858381780150821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1477475694572254520100547 2216213541858381780150821)
                  ·
                    refine ⟨415540039098446583778279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2216213541858381780150821 415540039098446583778279)
                    ·
                      rfl

theorem cell22_1213892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 3, 2, 1, 4].length) (baseStart_1213892 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1213892 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1213892 prefixEnd_1213892 := by exact prefixLift 1213892
  have htrace : WordTrace (prefixWord ++ tailWord_1213892) baseStart_1213892 baseEnd_1213892 := by
    simpa [prefixWord, tailWord_1213892, baseEnd_1213892] using wordTrace_append hprefix tailTrace_1213892
  have hstable : (prefixWord ++ tailWord_1213892).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1213892).length < 2 ^ (prefixWord ++ tailWord_1213892).sum := by decide
  have hdescent : baseEnd_1213892 < baseStart_1213892 := by decide
  rcases family_descends (prefixWord ++ tailWord_1213892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1213903 : List Nat := [1, 1, 2, 1, 1, 4, 3, 3, 2, 4]
def baseStart_1213903 : Nat := 118140960795 + 1213903 * 2 ^ 59
def prefixEnd_1213903 : Nat := 4983230072969 + 3 ^ 40 * 1213903 * 2
def baseEnd_1213903 : Nat := 415543804623246221753245

theorem tailTrace_1213903 : CollatzResearch.WordTrace tailWord_1213903 prefixEnd_1213903 415543804623246221753245 := by
  unfold tailWord_1213903
  simp only [CollatzResearch.WordTrace]
  refine ⟨44274679721244223972070363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29516453147496149314713575 44274679721244223972070363)
  ·
    refine ⟨66412019581866335958105545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44274679721244223972070363 66412019581866335958105545)
    ·
      refine ⟨49809014686399751968579159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66412019581866335958105545 49809014686399751968579159)
      ·
        refine ⟨74713522029599627952868739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49809014686399751968579159 74713522029599627952868739)
        ·
          refine ⟨112070283044399441929303109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74713522029599627952868739 112070283044399441929303109)
          ·
            refine ⟨21013178070824895361744333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 112070283044399441929303109 21013178070824895361744333)
            ·
              refine ⟨7879941776559335760654125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21013178070824895361744333 7879941776559335760654125)
              ·
                refine ⟨2954978166209750910245297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7879941776559335760654125 2954978166209750910245297)
                ·
                  refine ⟨2216233624657313182683973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2954978166209750910245297 2216233624657313182683973)
                  ·
                    refine ⟨415543804623246221753245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2216233624657313182683973 415543804623246221753245)
                    ·
                      rfl

theorem cell22_1213903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 3, 2, 4].length) (baseStart_1213903 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1213903 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1213903 prefixEnd_1213903 := by exact prefixLift 1213903
  have htrace : WordTrace (prefixWord ++ tailWord_1213903) baseStart_1213903 baseEnd_1213903 := by
    simpa [prefixWord, tailWord_1213903, baseEnd_1213903] using wordTrace_append hprefix tailTrace_1213903
  have hstable : (prefixWord ++ tailWord_1213903).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1213903).length < 2 ^ (prefixWord ++ tailWord_1213903).sum := by decide
  have hdescent : baseEnd_1213903 < baseStart_1213903 := by decide
  rcases family_descends (prefixWord ++ tailWord_1213903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1213954 : List Nat := [3, 4, 1, 2, 1, 3, 1, 1, 2, 4]
def baseStart_1213954 : Nat := 118140960795 + 1213954 * 2 ^ 59
def prefixEnd_1213954 : Nat := 4983230072969 + 3 ^ 40 * 1213954 * 2
def baseEnd_1213954 : Nat := 415561262965499088728089

theorem tailTrace_1213954 : CollatzResearch.WordTrace tailWord_1213954 prefixEnd_1213954 415561262965499088728089 := by
  unfold tailWord_1213954
  simp only [CollatzResearch.WordTrace]
  refine ⟨11069134961014864920544229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29517693229372973121451277 11069134961014864920544229)
  ·
    refine ⟨2075462805190287172602043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11069134961014864920544229 2075462805190287172602043)
    ·
      refine ⟨3113194207785430758903065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2075462805190287172602043 3113194207785430758903065)
      ·
        refine ⟨2334895655839073069177299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3113194207785430758903065 2334895655839073069177299)
        ·
          refine ⟨3502343483758609603765949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2334895655839073069177299 3502343483758609603765949)
          ·
            refine ⟨1313378806409478601412231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3502343483758609603765949 1313378806409478601412231)
            ·
              refine ⟨1970068209614217902118347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1313378806409478601412231 1970068209614217902118347)
              ·
                refine ⟨2955102314421326853177521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1970068209614217902118347 2955102314421326853177521)
                ·
                  refine ⟨2216326735815995139883141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2955102314421326853177521 2216326735815995139883141)
                  ·
                    refine ⟨415561262965499088728089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2216326735815995139883141 415561262965499088728089)
                    ·
                      rfl

theorem cell22_1213954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 1, 1, 2, 4].length) (baseStart_1213954 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1213954 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1213954 prefixEnd_1213954 := by exact prefixLift 1213954
  have htrace : WordTrace (prefixWord ++ tailWord_1213954) baseStart_1213954 baseEnd_1213954 := by
    simpa [prefixWord, tailWord_1213954, baseEnd_1213954] using wordTrace_append hprefix tailTrace_1213954
  have hstable : (prefixWord ++ tailWord_1213954).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1213954).length < 2 ^ (prefixWord ++ tailWord_1213954).sum := by decide
  have hdescent : baseEnd_1213954 < baseStart_1213954 := by decide
  rcases family_descends (prefixWord ++ tailWord_1213954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1213958 : List Nat := [6, 2, 1, 1, 2, 1, 2, 3, 4]
def baseStart_1213958 : Nat := 118140960795 + 1213958 * 2 ^ 59
def prefixEnd_1213958 : Nat := 4983230072969 + 3 ^ 40 * 1213958 * 2
def baseEnd_1213958 : Nat := 138520877415748137209359

theorem tailTrace_1213958 : CollatzResearch.WordTrace tailWord_1213958 prefixEnd_1213958 138520877415748137209359 := by
  unfold tailWord_1213958
  simp only [CollatzResearch.WordTrace]
  refine ⟨1383646429251405261416329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 29517790490696645576881685 1383646429251405261416329)
  ·
    refine ⟨1037734821938553946062247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1383646429251405261416329 1037734821938553946062247)
    ·
      refine ⟨1556602232907830919093371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1037734821938553946062247 1556602232907830919093371)
      ·
        refine ⟨2334903349361746378640057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1556602232907830919093371 2334903349361746378640057)
        ·
          refine ⟨1751177512021309783980043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2334903349361746378640057 1751177512021309783980043)
          ·
            refine ⟨2626766268031964675970065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1751177512021309783980043 2626766268031964675970065)
            ·
              refine ⟨1970074701023973506977549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2626766268031964675970065 1970074701023973506977549)
              ·
                refine ⟨738778012883990065116581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1970074701023973506977549 738778012883990065116581)
                ·
                  refine ⟨138520877415748137209359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 738778012883990065116581 138520877415748137209359)
                  ·
                    rfl

theorem cell22_1213958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 2, 3, 4].length) (baseStart_1213958 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1213958 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1213958 prefixEnd_1213958 := by exact prefixLift 1213958
  have htrace : WordTrace (prefixWord ++ tailWord_1213958) baseStart_1213958 baseEnd_1213958 := by
    simpa [prefixWord, tailWord_1213958, baseEnd_1213958] using wordTrace_append hprefix tailTrace_1213958
  have hstable : (prefixWord ++ tailWord_1213958).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1213958).length < 2 ^ (prefixWord ++ tailWord_1213958).sum := by decide
  have hdescent : baseEnd_1213958 < baseStart_1213958 := by decide
  rcases family_descends (prefixWord ++ tailWord_1213958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1213984 : List Nat := [2, 1, 1, 6, 1, 1, 2, 4, 1, 3]
def baseStart_1213984 : Nat := 118140960795 + 1213984 * 2 ^ 59
def prefixEnd_1213984 : Nat := 4983230072969 + 3 ^ 40 * 1213984 * 2
def baseEnd_1213984 : Nat := 415571532578589010477997

theorem tailTrace_1213984 : CollatzResearch.WordTrace tailWord_1213984 prefixEnd_1213984 415571532578589010477997 := by
  unfold tailWord_1213984
  simp only [CollatzResearch.WordTrace]
  refine ⟨22138817016975387402884503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29518422689300516537179337 22138817016975387402884503)
  ·
    refine ⟨33208225525463081104326755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22138817016975387402884503 33208225525463081104326755)
    ·
      refine ⟨49812338288194621656490133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33208225525463081104326755 49812338288194621656490133)
      ·
        refine ⟨2334953357259122890147975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 49812338288194621656490133 2334953357259122890147975)
        ·
          refine ⟨3502430035888684335221963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2334953357259122890147975 3502430035888684335221963)
          ·
            refine ⟨5253645053833026502832945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3502430035888684335221963 5253645053833026502832945)
            ·
              refine ⟨3940233790374769877124709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5253645053833026502832945 3940233790374769877124709)
              ·
                refine ⟨738793835695269351960883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3940233790374769877124709 738793835695269351960883)
                ·
                  refine ⟨1108190753542904027941325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 738793835695269351960883 1108190753542904027941325)
                  ·
                    refine ⟨415571532578589010477997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1108190753542904027941325 415571532578589010477997)
                    ·
                      rfl

theorem cell22_1213984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 2, 4, 1, 3].length) (baseStart_1213984 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1213984 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1213984 prefixEnd_1213984 := by exact prefixLift 1213984
  have htrace : WordTrace (prefixWord ++ tailWord_1213984) baseStart_1213984 baseEnd_1213984 := by
    simpa [prefixWord, tailWord_1213984, baseEnd_1213984] using wordTrace_append hprefix tailTrace_1213984
  have hstable : (prefixWord ++ tailWord_1213984).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1213984).length < 2 ^ (prefixWord ++ tailWord_1213984).sum := by decide
  have hdescent : baseEnd_1213984 < baseStart_1213984 := by decide
  rcases family_descends (prefixWord ++ tailWord_1213984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1214061 : List Nat := [1, 5, 1, 1, 5, 1, 1, 2, 1, 4]
def baseStart_1214061 : Nat := 118140960795 + 1214061 * 2 ^ 59
def prefixEnd_1214061 : Nat := 4983230072969 + 3 ^ 40 * 1214061 * 2
def baseEnd_1214061 : Nat := 415597891252186476302761

theorem tailTrace_1214061 : CollatzResearch.WordTrace tailWord_1214061 prefixEnd_1214061 415597891252186476302761 := by
  unfold tailWord_1214061
  simp only [CollatzResearch.WordTrace]
  refine ⟨44280442454671816956322037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29520294969781211304214691 44280442454671816956322037)
  ·
    refine ⟨4151291480125482839655191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 44280442454671816956322037 4151291480125482839655191)
    ·
      refine ⟨6226937220188224259482787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4151291480125482839655191 6226937220188224259482787)
      ·
        refine ⟨9340405830282336389224181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6226937220188224259482787 9340405830282336389224181)
        ·
          refine ⟨875663046588969036489767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9340405830282336389224181 875663046588969036489767)
          ·
            refine ⟨1313494569883453554734651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 875663046588969036489767 1313494569883453554734651)
            ·
              refine ⟨1970241854825180332101977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1313494569883453554734651 1970241854825180332101977)
              ·
                refine ⟨1477681391118885249076483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1970241854825180332101977 1477681391118885249076483)
                ·
                  refine ⟨2216522086678327873614725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1477681391118885249076483 2216522086678327873614725)
                  ·
                    refine ⟨415597891252186476302761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2216522086678327873614725 415597891252186476302761)
                    ·
                      rfl

theorem cell22_1214061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 1, 2, 1, 4].length) (baseStart_1214061 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1214061 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1214061 prefixEnd_1214061 := by exact prefixLift 1214061
  have htrace : WordTrace (prefixWord ++ tailWord_1214061) baseStart_1214061 baseEnd_1214061 := by
    simpa [prefixWord, tailWord_1214061, baseEnd_1214061] using wordTrace_append hprefix tailTrace_1214061
  have hstable : (prefixWord ++ tailWord_1214061).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1214061).length < 2 ^ (prefixWord ++ tailWord_1214061).sum := by decide
  have hdescent : baseEnd_1214061 < baseStart_1214061 := by decide
  rcases family_descends (prefixWord ++ tailWord_1214061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1214115 : List Nat := [1, 1, 1, 4, 1, 1, 3, 5, 5]
def baseStart_1214115 : Nat := 118140960795 + 1214115 * 2 ^ 59
def prefixEnd_1214115 : Nat := 4983230072969 + 3 ^ 40 * 1214115 * 2
def baseEnd_1214115 : Nat := 138538792185249445150865

theorem tailTrace_1214115 : CollatzResearch.WordTrace tailWord_1214115 prefixEnd_1214115 138538792185249445150865 := by
  unfold tailWord_1214115
  simp only [CollatzResearch.WordTrace]
  refine ⟨44282411996476184178787799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29521607997650789452525199 44282411996476184178787799)
  ·
    refine ⟨66423617994714276268181699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44282411996476184178787799 66423617994714276268181699)
    ·
      refine ⟨99635426992071414402272549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66423617994714276268181699 99635426992071414402272549)
      ·
        refine ⟨18681642561013390200426103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 99635426992071414402272549 18681642561013390200426103)
        ·
          refine ⟨28022463841520085300639155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18681642561013390200426103 28022463841520085300639155)
          ·
            refine ⟨42033695762280127950958733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28022463841520085300639155 42033695762280127950958733)
            ·
              refine ⟨15762635910855047981609525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42033695762280127950958733 15762635910855047981609525)
              ·
                refine ⟨1477747116642660748275893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15762635910855047981609525 1477747116642660748275893)
                ·
                  refine ⟨138538792185249445150865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1477747116642660748275893 138538792185249445150865)
                  ·
                    rfl

theorem cell22_1214115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 5, 5].length) (baseStart_1214115 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1214115 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1214115 prefixEnd_1214115 := by exact prefixLift 1214115
  have htrace : WordTrace (prefixWord ++ tailWord_1214115) baseStart_1214115 baseEnd_1214115 := by
    simpa [prefixWord, tailWord_1214115, baseEnd_1214115] using wordTrace_append hprefix tailTrace_1214115
  have hstable : (prefixWord ++ tailWord_1214115).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1214115).length < 2 ^ (prefixWord ++ tailWord_1214115).sum := by decide
  have hdescent : baseEnd_1214115 < baseStart_1214115 := by decide
  rcases family_descends (prefixWord ++ tailWord_1214115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1214235 : List Nat := [1, 1, 1, 1, 1, 1, 4, 4, 2, 6]
def baseStart_1214235 : Nat := 118140960795 + 1214235 * 2 ^ 59
def prefixEnd_1214235 : Nat := 4983230072969 + 3 ^ 40 * 1214235 * 2
def baseEnd_1214235 : Nat := 415657455008108022452227

theorem tailTrace_1214235 : CollatzResearch.WordTrace tailWord_1214235 prefixEnd_1214235 415657455008108022452227 := by
  unfold tailWord_1214235
  simp only [CollatzResearch.WordTrace]
  refine ⟨44286788756041444673156159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29524525837360963115437439 44286788756041444673156159)
  ·
    refine ⟨66430183134062167009734239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44286788756041444673156159 66430183134062167009734239)
    ·
      refine ⟨99645274701093250514601359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66430183134062167009734239 99645274701093250514601359)
      ·
        refine ⟨149467912051639875771902039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99645274701093250514601359 149467912051639875771902039)
        ·
          refine ⟨224201868077459813657853059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149467912051639875771902039 224201868077459813657853059)
          ·
            refine ⟨336302802116189720486779589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 224201868077459813657853059 336302802116189720486779589)
            ·
              refine ⟨63056775396785572591271173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 336302802116189720486779589 63056775396785572591271173)
              ·
                refine ⟨11823145386897294860863345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 63056775396785572591271173 11823145386897294860863345)
                ·
                  refine ⟨8867359040172971145647509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11823145386897294860863345 8867359040172971145647509)
                  ·
                    refine ⟨415657455008108022452227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8867359040172971145647509 415657455008108022452227)
                    ·
                      rfl

theorem cell22_1214235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4, 2, 6].length) (baseStart_1214235 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1214235 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1214235 prefixEnd_1214235 := by exact prefixLift 1214235
  have htrace : WordTrace (prefixWord ++ tailWord_1214235) baseStart_1214235 baseEnd_1214235 := by
    simpa [prefixWord, tailWord_1214235, baseEnd_1214235] using wordTrace_append hprefix tailTrace_1214235
  have hstable : (prefixWord ++ tailWord_1214235).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1214235).length < 2 ^ (prefixWord ++ tailWord_1214235).sum := by decide
  have hdescent : baseEnd_1214235 < baseStart_1214235 := by decide
  rcases family_descends (prefixWord ++ tailWord_1214235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1214282 : List Nat := [3, 1, 2, 1, 1, 1, 5, 1, 2, 5]
def baseStart_1214282 : Nat := 118140960795 + 1214282 * 2 ^ 59
def prefixEnd_1214282 : Nat := 4983230072969 + 3 ^ 40 * 1214282 * 2
def baseEnd_1214282 : Nat := 415673544068615566527083

theorem tailTrace_1214282 : CollatzResearch.WordTrace tailWord_1214282 prefixEnd_1214282 415673544068615566527083 := by
  unfold tailWord_1214282
  simp only [CollatzResearch.WordTrace]
  refine ⟨11072125746717792925029275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29525668657914114466744733 11072125746717792925029275)
  ·
    refine ⟨16608188620076689387543913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11072125746717792925029275 16608188620076689387543913)
    ·
      refine ⟨12456141465057517040657935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16608188620076689387543913 12456141465057517040657935)
      ·
        refine ⟨18684212197586275560986903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12456141465057517040657935 18684212197586275560986903)
        ·
          refine ⟨28026318296379413341480355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18684212197586275560986903 28026318296379413341480355)
          ·
            refine ⟨42039477444569120012220533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28026318296379413341480355 42039477444569120012220533)
            ·
              refine ⟨3941201010428355001145675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 42039477444569120012220533 3941201010428355001145675)
              ·
                refine ⟨5911801515642532501718513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3941201010428355001145675 5911801515642532501718513)
                ·
                  refine ⟨4433851136731899376288885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5911801515642532501718513 4433851136731899376288885)
                  ·
                    refine ⟨415673544068615566527083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4433851136731899376288885 415673544068615566527083)
                    ·
                      rfl

theorem cell22_1214282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5, 1, 2, 5].length) (baseStart_1214282 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1214282 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1214282 prefixEnd_1214282 := by exact prefixLift 1214282
  have htrace : WordTrace (prefixWord ++ tailWord_1214282) baseStart_1214282 baseEnd_1214282 := by
    simpa [prefixWord, tailWord_1214282, baseEnd_1214282] using wordTrace_append hprefix tailTrace_1214282
  have hstable : (prefixWord ++ tailWord_1214282).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1214282).length < 2 ^ (prefixWord ++ tailWord_1214282).sum := by decide
  have hdescent : baseEnd_1214282 < baseStart_1214282 := by decide
  rcases family_descends (prefixWord ++ tailWord_1214282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1214297 : List Nat := [1, 2, 1, 2, 2, 3, 1, 3, 3, 4]
def baseStart_1214297 : Nat := 118140960795 + 1214297 * 2 ^ 59
def prefixEnd_1214297 : Nat := 4983230072969 + 3 ^ 40 * 1214297 * 2
def baseEnd_1214297 : Nat := 415678678875160527402037

theorem tailTrace_1214297 : CollatzResearch.WordTrace tailWord_1214297 prefixEnd_1214297 415678678875160527402037 := by
  unfold tailWord_1214297
  simp only [CollatzResearch.WordTrace]
  refine ⟨44289050081816829261913145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29526033387877886174608763 44289050081816829261913145)
  ·
    refine ⟨33216787561362621946434859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44289050081816829261913145 33216787561362621946434859)
    ·
      refine ⟨49825181342043932919652289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33216787561362621946434859 49825181342043932919652289)
      ·
        refine ⟨37368886006532949689739217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49825181342043932919652289 37368886006532949689739217)
        ·
          refine ⟨28026664504899712267304413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37368886006532949689739217 28026664504899712267304413)
          ·
            refine ⟨10509999189337392100239155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28026664504899712267304413 10509999189337392100239155)
            ·
              refine ⟨15764998784006088150358733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10509999189337392100239155 15764998784006088150358733)
              ·
                refine ⟨5911874544002283056384525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15764998784006088150358733 5911874544002283056384525)
                ·
                  refine ⟨2216952954000856146144197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5911874544002283056384525 2216952954000856146144197)
                  ·
                    refine ⟨415678678875160527402037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2216952954000856146144197 415678678875160527402037)
                    ·
                      rfl

theorem cell22_1214297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 3, 3, 4].length) (baseStart_1214297 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1214297 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1214297 prefixEnd_1214297 := by exact prefixLift 1214297
  have htrace : WordTrace (prefixWord ++ tailWord_1214297) baseStart_1214297 baseEnd_1214297 := by
    simpa [prefixWord, tailWord_1214297, baseEnd_1214297] using wordTrace_append hprefix tailTrace_1214297
  have hstable : (prefixWord ++ tailWord_1214297).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1214297).length < 2 ^ (prefixWord ++ tailWord_1214297).sum := by decide
  have hdescent : baseEnd_1214297 < baseStart_1214297 := by decide
  rcases family_descends (prefixWord ++ tailWord_1214297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1214312 : List Nat := [2, 1, 4, 2, 1, 1, 1, 2, 8]
def baseStart_1214312 : Nat := 118140960795 + 1214312 * 2 ^ 59
def prefixEnd_1214312 : Nat := 4983230072969 + 3 ^ 40 * 1214312 * 2
def baseEnd_1214312 : Nat := 138561271227235162758997

theorem tailTrace_1214312 : CollatzResearch.WordTrace tailWord_1214312 prefixEnd_1214312 138561271227235162758997 := by
  unfold tailWord_1214312
  simp only [CollatzResearch.WordTrace]
  refine ⟨22144798588381243411854595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29526398117841657882472793 22144798588381243411854595)
  ·
    refine ⟨33217197882571865117781893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22144798588381243411854595 33217197882571865117781893)
    ·
      refine ⟨6228224602982224709584105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33217197882571865117781893 6228224602982224709584105)
      ·
        refine ⟨4671168452236668532188079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6228224602982224709584105 4671168452236668532188079)
        ·
          refine ⟨7006752678355002798282119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4671168452236668532188079 7006752678355002798282119)
          ·
            refine ⟨10510129017532504197423179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7006752678355002798282119 10510129017532504197423179)
            ·
              refine ⟨15765193526298756296134769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10510129017532504197423179 15765193526298756296134769)
              ·
                refine ⟨11823895144724067222101077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15765193526298756296134769 11823895144724067222101077)
                ·
                  refine ⟨138561271227235162758997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 11823895144724067222101077 138561271227235162758997)
                  ·
                    rfl

theorem cell22_1214312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 2, 8].length) (baseStart_1214312 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1214312 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1214312 prefixEnd_1214312 := by exact prefixLift 1214312
  have htrace : WordTrace (prefixWord ++ tailWord_1214312) baseStart_1214312 baseEnd_1214312 := by
    simpa [prefixWord, tailWord_1214312, baseEnd_1214312] using wordTrace_append hprefix tailTrace_1214312
  have hstable : (prefixWord ++ tailWord_1214312).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1214312).length < 2 ^ (prefixWord ++ tailWord_1214312).sum := by decide
  have hdescent : baseEnd_1214312 < baseStart_1214312 := by decide
  rcases family_descends (prefixWord ++ tailWord_1214312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1214329 : List Nat := [1, 2, 1, 3, 2, 2, 1, 6, 4]
def baseStart_1214329 : Nat := 118140960795 + 1214329 * 2 ^ 59
def prefixEnd_1214329 : Nat := 4983230072969 + 3 ^ 40 * 1214329 * 2
def baseEnd_1214329 : Nat := 138563211043041036867313

theorem tailTrace_1214329 : CollatzResearch.WordTrace tailWord_1214329 prefixEnd_1214329 138563211043041036867313 := by
  unfold tailWord_1214329
  simp only [CollatzResearch.WordTrace]
  refine ⟨44290217217700898727078041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29526811478467265818052027 44290217217700898727078041)
  ·
    refine ⟨33217662913275674045308531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44290217217700898727078041 33217662913275674045308531)
    ·
      refine ⟨49826494369913511067962797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33217662913275674045308531 49826494369913511067962797)
      ·
        refine ⟨18684935388717566650486049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49826494369913511067962797 18684935388717566650486049)
        ·
          refine ⟨14013701541538174987864537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18684935388717566650486049 14013701541538174987864537)
          ·
            refine ⟨10510276156153631240898403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14013701541538174987864537 10510276156153631240898403)
            ·
              refine ⟨15765414234230446861347605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10510276156153631240898403 15765414234230446861347605)
              ·
                refine ⟨739003792229552196625669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 15765414234230446861347605 739003792229552196625669)
                ·
                  refine ⟨138563211043041036867313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 739003792229552196625669 138563211043041036867313)
                  ·
                    rfl

theorem cell22_1214329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 6, 4].length) (baseStart_1214329 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1214329 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1214329 prefixEnd_1214329 := by exact prefixLift 1214329
  have htrace : WordTrace (prefixWord ++ tailWord_1214329) baseStart_1214329 baseEnd_1214329 := by
    simpa [prefixWord, tailWord_1214329, baseEnd_1214329] using wordTrace_append hprefix tailTrace_1214329
  have hstable : (prefixWord ++ tailWord_1214329).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1214329).length < 2 ^ (prefixWord ++ tailWord_1214329).sum := by decide
  have hdescent : baseEnd_1214329 < baseStart_1214329 := by decide
  rcases family_descends (prefixWord ++ tailWord_1214329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1214357 : List Nat := [1, 3, 2, 1, 1, 3, 3, 8]
def baseStart_1214357 : Nat := 118140960795 + 1214357 * 2 ^ 59
def prefixEnd_1214357 : Nat := 4983230072969 + 3 ^ 40 * 1214357 * 2
def baseEnd_1214357 : Nat := 46188802011260041211317

theorem tailTrace_1214357 : CollatzResearch.WordTrace tailWord_1214357 prefixEnd_1214357 46188802011260041211317 := by
  unfold tailWord_1214357
  simp only [CollatzResearch.WordTrace]
  refine ⟨44291238461599459509097325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29527492307732973006064883 44291238461599459509097325)
  ·
    refine ⟨16609214423099797315911497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44291238461599459509097325 16609214423099797315911497)
    ·
      refine ⟨12456910817324847986933623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16609214423099797315911497 12456910817324847986933623)
      ·
        refine ⟨18685366225987271980400435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12456910817324847986933623 18685366225987271980400435)
        ·
          refine ⟨28028049338980907970600653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18685366225987271980400435 28028049338980907970600653)
          ·
            refine ⟨10510518502117840488975245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28028049338980907970600653 10510518502117840488975245)
            ·
              refine ⟨3941444438294190183365717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10510518502117840488975245 3941444438294190183365717)
              ·
                refine ⟨46188802011260041211317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3941444438294190183365717 46188802011260041211317)
                ·
                  rfl

theorem cell22_1214357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3, 8].length) (baseStart_1214357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1214357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1214357 prefixEnd_1214357 := by exact prefixLift 1214357
  have htrace : WordTrace (prefixWord ++ tailWord_1214357) baseStart_1214357 baseEnd_1214357 := by
    simpa [prefixWord, tailWord_1214357, baseEnd_1214357] using wordTrace_append hprefix tailTrace_1214357
  have hstable : (prefixWord ++ tailWord_1214357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1214357).length < 2 ^ (prefixWord ++ tailWord_1214357).sum := by decide
  have hdescent : baseEnd_1214357 < baseStart_1214357 := by decide
  rcases family_descends (prefixWord ++ tailWord_1214357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1214387 : List Nat := [1, 1, 1, 2, 3, 1, 4, 1, 2, 6]
def baseStart_1214387 : Nat := 118140960795 + 1214387 * 2 ^ 59
def prefixEnd_1214387 : Nat := 4983230072969 + 3 ^ 40 * 1214387 * 2
def baseEnd_1214387 : Nat := 415709487714430292651761

theorem tailTrace_1214387 : CollatzResearch.WordTrace tailWord_1214387 prefixEnd_1214387 415709487714430292651761 := by
  unfold tailWord_1214387
  simp only [CollatzResearch.WordTrace]
  refine ⟨44292332651490774632689415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29528221767660516421792943 44292332651490774632689415)
  ·
    refine ⟨66438498977236161949034123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44292332651490774632689415 66438498977236161949034123)
    ·
      refine ⟨99657748465854242923551185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66438498977236161949034123 99657748465854242923551185)
      ·
        refine ⟨74743311349390682192663389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99657748465854242923551185 74743311349390682192663389)
        ·
          refine ⟨28028741756021505822248771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74743311349390682192663389 28028741756021505822248771)
          ·
            refine ⟨42043112634032258733373157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28028741756021505822248771 42043112634032258733373157)
            ·
              refine ⟨7883083618881048512507467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42043112634032258733373157 7883083618881048512507467)
              ·
                refine ⟨11824625428321572768761201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7883083618881048512507467 11824625428321572768761201)
                ·
                  refine ⟨8868469071241179576570901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11824625428321572768761201 8868469071241179576570901)
                  ·
                    refine ⟨415709487714430292651761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8868469071241179576570901 415709487714430292651761)
                    ·
                      rfl

theorem cell22_1214387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 1, 2, 6].length) (baseStart_1214387 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1214387 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1214387 prefixEnd_1214387 := by exact prefixLift 1214387
  have htrace : WordTrace (prefixWord ++ tailWord_1214387) baseStart_1214387 baseEnd_1214387 := by
    simpa [prefixWord, tailWord_1214387, baseEnd_1214387] using wordTrace_append hprefix tailTrace_1214387
  have hstable : (prefixWord ++ tailWord_1214387).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1214387).length < 2 ^ (prefixWord ++ tailWord_1214387).sum := by decide
  have hdescent : baseEnd_1214387 < baseStart_1214387 := by decide
  rcases family_descends (prefixWord ++ tailWord_1214387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1214417 : List Nat := [1, 2, 2, 1, 2, 1, 2, 1, 3, 7]
def baseStart_1214417 : Nat := 118140960795 + 1214417 * 2 ^ 59
def prefixEnd_1214417 : Nat := 4983230072969 + 3 ^ 40 * 1214417 * 2
def baseEnd_1214417 : Nat := 415719757327520214401669

theorem tailTrace_1214417 : CollatzResearch.WordTrace tailWord_1214417 prefixEnd_1214417 415719757327520214401669 := by
  unfold tailWord_1214417
  simp only [CollatzResearch.WordTrace]
  refine ⟨44293426841382089756281505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29528951227588059837521003 44293426841382089756281505)
  ·
    refine ⟨33220070131036567317211129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44293426841382089756281505 33220070131036567317211129)
    ·
      refine ⟨24915052598277425487908347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33220070131036567317211129 24915052598277425487908347)
      ·
        refine ⟨37372578897416138231862521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24915052598277425487908347 37372578897416138231862521)
        ·
          refine ⟨28029434173062103673896891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37372578897416138231862521 28029434173062103673896891)
          ·
            refine ⟨42044151259593155510845337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28029434173062103673896891 42044151259593155510845337)
            ·
              refine ⟨31533113444694866633134003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42044151259593155510845337 31533113444694866633134003)
              ·
                refine ⟨47299670167042299949701005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31533113444694866633134003 47299670167042299949701005)
                ·
                  refine ⟨17737376312640862481137877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47299670167042299949701005 17737376312640862481137877)
                  ·
                    refine ⟨415719757327520214401669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17737376312640862481137877 415719757327520214401669)
                    ·
                      rfl

theorem cell22_1214417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 1, 3, 7].length) (baseStart_1214417 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1214417 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1214417 prefixEnd_1214417 := by exact prefixLift 1214417
  have htrace : WordTrace (prefixWord ++ tailWord_1214417) baseStart_1214417 baseEnd_1214417 := by
    simpa [prefixWord, tailWord_1214417, baseEnd_1214417] using wordTrace_append hprefix tailTrace_1214417
  have hstable : (prefixWord ++ tailWord_1214417).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1214417).length < 2 ^ (prefixWord ++ tailWord_1214417).sum := by decide
  have hdescent : baseEnd_1214417 < baseStart_1214417 := by decide
  rcases family_descends (prefixWord ++ tailWord_1214417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1214524 : List Nat := [2, 2, 2, 2, 2, 1, 1, 1, 2, 7]
def baseStart_1214524 : Nat := 118140960795 + 1214524 * 2 ^ 59
def prefixEnd_1214524 : Nat := 4983230072969 + 3 ^ 40 * 1214524 * 2
def baseEnd_1214524 : Nat := 415756385614207601976341

theorem tailTrace_1214524 : CollatzResearch.WordTrace tailWord_1214524 prefixEnd_1214524 415756385614207601976341 := by
  unfold tailWord_1214524
  simp only [CollatzResearch.WordTrace]
  refine ⟨22148664725997223515213313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29531552967996298020284417 22148664725997223515213313)
  ·
    refine ⟨16611498544497917636409985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22148664725997223515213313 16611498544497917636409985)
    ·
      refine ⟨12458623908373438227307489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16611498544497917636409985 12458623908373438227307489)
      ·
        refine ⟨9343967931280078670480617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12458623908373438227307489 9343967931280078670480617)
        ·
          refine ⟨7007975948460059002860463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9343967931280078670480617 7007975948460059002860463)
          ·
            refine ⟨10511963922690088504290695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7007975948460059002860463 10511963922690088504290695)
            ·
              refine ⟨15767945884035132756436043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10511963922690088504290695 15767945884035132756436043)
              ·
                refine ⟨23651918826052699134654065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15767945884035132756436043 23651918826052699134654065)
                ·
                  refine ⟨17738939119539524350990549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23651918826052699134654065 17738939119539524350990549)
                  ·
                    refine ⟨415756385614207601976341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17738939119539524350990549 415756385614207601976341)
                    ·
                      rfl

theorem cell22_1214524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 1, 2, 7].length) (baseStart_1214524 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1214524 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1214524 prefixEnd_1214524 := by exact prefixLift 1214524
  have htrace : WordTrace (prefixWord ++ tailWord_1214524) baseStart_1214524 baseEnd_1214524 := by
    simpa [prefixWord, tailWord_1214524, baseEnd_1214524] using wordTrace_append hprefix tailTrace_1214524
  have hstable : (prefixWord ++ tailWord_1214524).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1214524).length < 2 ^ (prefixWord ++ tailWord_1214524).sum := by decide
  have hdescent : baseEnd_1214524 < baseStart_1214524 := by decide
  rcases family_descends (prefixWord ++ tailWord_1214524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1214554 : List Nat := [3, 1, 1, 2, 1, 1, 3, 3, 7]
def baseStart_1214554 : Nat := 118140960795 + 1214554 * 2 ^ 59
def prefixEnd_1214554 : Nat := 4983230072969 + 3 ^ 40 * 1214554 * 2
def baseEnd_1214554 : Nat := 138588885075765841242083

theorem tailTrace_1214554 : CollatzResearch.WordTrace tailWord_1214554 prefixEnd_1214554 138588885075765841242083 := by
  unfold tailWord_1214554
  simp only [CollatzResearch.WordTrace]
  refine ⟨11074605910471440538504679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29532282427923841436012477 11074605910471440538504679)
  ·
    refine ⟨16611908865707160807757019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11074605910471440538504679 16611908865707160807757019)
    ·
      refine ⟨24917863298560741211635529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16611908865707160807757019 24917863298560741211635529)
      ·
        refine ⟨18688397473920555908726647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24917863298560741211635529 18688397473920555908726647)
        ·
          refine ⟨28032596210880833863089971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18688397473920555908726647 28032596210880833863089971)
          ·
            refine ⟨42048894316321250794634957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28032596210880833863089971 42048894316321250794634957)
            ·
              refine ⟨15768335368620469047988109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42048894316321250794634957 15768335368620469047988109)
              ·
                refine ⟨5913125763232675892995541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15768335368620469047988109 5913125763232675892995541)
                ·
                  refine ⟨138588885075765841242083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5913125763232675892995541 138588885075765841242083)
                  ·
                    rfl

theorem cell22_1214554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 3, 7].length) (baseStart_1214554 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1214554 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1214554 prefixEnd_1214554 := by exact prefixLift 1214554
  have htrace : WordTrace (prefixWord ++ tailWord_1214554) baseStart_1214554 baseEnd_1214554 := by
    simpa [prefixWord, tailWord_1214554, baseEnd_1214554] using wordTrace_append hprefix tailTrace_1214554
  have hstable : (prefixWord ++ tailWord_1214554).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1214554).length < 2 ^ (prefixWord ++ tailWord_1214554).sum := by decide
  have hdescent : baseEnd_1214554 < baseStart_1214554 := by decide
  rcases family_descends (prefixWord ++ tailWord_1214554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1214569 : List Nat := [1, 2, 1, 1, 1, 5, 2, 1, 1, 7]
def baseStart_1214569 : Nat := 118140960795 + 1214569 * 2 ^ 59
def prefixEnd_1214569 : Nat := 4983230072969 + 3 ^ 40 * 1214569 * 2
def baseEnd_1214569 : Nat := 415771790033842484601203

theorem tailTrace_1214569 : CollatzResearch.WordTrace tailWord_1214569 prefixEnd_1214569 415771790033842484601203 := by
  unfold tailWord_1214569
  simp only [CollatzResearch.WordTrace]
  refine ⟨44298970736831419715814761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29532647157887613143876507 44298970736831419715814761)
  ·
    refine ⟨33224228052623564786861071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44298970736831419715814761 33224228052623564786861071)
    ·
      refine ⟨49836342078935347180291607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33224228052623564786861071 49836342078935347180291607)
      ·
        refine ⟨74754513118403020770437411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49836342078935347180291607 74754513118403020770437411)
        ·
          refine ⟨112131769677604531155656117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74754513118403020770437411 112131769677604531155656117)
          ·
            refine ⟨10512353407275424795842761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 112131769677604531155656117 10512353407275424795842761)
            ·
              refine ⟨7884265055456568596882071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10512353407275424795842761 7884265055456568596882071)
              ·
                refine ⟨11826397583184852895323107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7884265055456568596882071 11826397583184852895323107)
                ·
                  refine ⟨17739596374777279342984661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11826397583184852895323107 17739596374777279342984661)
                  ·
                    refine ⟨415771790033842484601203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17739596374777279342984661 415771790033842484601203)
                    ·
                      rfl

theorem cell22_1214569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 1, 1, 7].length) (baseStart_1214569 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1214569 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1214569 prefixEnd_1214569 := by exact prefixLift 1214569
  have htrace : WordTrace (prefixWord ++ tailWord_1214569) baseStart_1214569 baseEnd_1214569 := by
    simpa [prefixWord, tailWord_1214569, baseEnd_1214569] using wordTrace_append hprefix tailTrace_1214569
  have hstable : (prefixWord ++ tailWord_1214569).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1214569).length < 2 ^ (prefixWord ++ tailWord_1214569).sum := by decide
  have hdescent : baseEnd_1214569 < baseStart_1214569 := by decide
  rcases family_descends (prefixWord ++ tailWord_1214569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1214652 : List Nat := [2, 2, 2, 3, 3, 2, 2, 1, 1, 4]
def baseStart_1214652 : Nat := 118140960795 + 1214652 * 2 ^ 59
def prefixEnd_1214652 : Nat := 4983230072969 + 3 ^ 40 * 1214652 * 2
def baseEnd_1214652 : Nat := 415800202630057934775949

theorem tailTrace_1214652 : CollatzResearch.WordTrace tailWord_1214652 prefixEnd_1214652 415800202630057934775949 := by
  unfold tailWord_1214652
  simp only [CollatzResearch.WordTrace]
  refine ⟨22150998997765362445543105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29534665330353816594057473 22150998997765362445543105)
  ·
    refine ⟨16613249248324021834157329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22150998997765362445543105 16613249248324021834157329)
    ·
      refine ⟨12459936936243016375617997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16613249248324021834157329 12459936936243016375617997)
      ·
        refine ⟨4672476351091131140856749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12459936936243016375617997 4672476351091131140856749)
        ·
          refine ⟨1752178631659174177821281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4672476351091131140856749 1752178631659174177821281)
          ·
            refine ⟨1314133973744380633365961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1752178631659174177821281 1314133973744380633365961)
            ·
              refine ⟨985600480308285475024471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1314133973744380633365961 985600480308285475024471)
              ·
                refine ⟨1478400720462428212536707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 985600480308285475024471 1478400720462428212536707)
                ·
                  refine ⟨2217601080693642318805061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1478400720462428212536707 2217601080693642318805061)
                  ·
                    refine ⟨415800202630057934775949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2217601080693642318805061 415800202630057934775949)
                    ·
                      rfl

theorem cell22_1214652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 2, 1, 1, 4].length) (baseStart_1214652 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1214652 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1214652 prefixEnd_1214652 := by exact prefixLift 1214652
  have htrace : WordTrace (prefixWord ++ tailWord_1214652) baseStart_1214652 baseEnd_1214652 := by
    simpa [prefixWord, tailWord_1214652, baseEnd_1214652] using wordTrace_append hprefix tailTrace_1214652
  have hstable : (prefixWord ++ tailWord_1214652).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1214652).length < 2 ^ (prefixWord ++ tailWord_1214652).sum := by decide
  have hdescent : baseEnd_1214652 < baseStart_1214652 := by decide
  rcases family_descends (prefixWord ++ tailWord_1214652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1214695 : List Nat := [1, 1, 5, 3, 1, 3, 2, 6]
def baseStart_1214695 : Nat := 118140960795 + 1214695 * 2 ^ 59
def prefixEnd_1214695 : Nat := 4983230072969 + 3 ^ 40 * 1214695 * 2
def baseEnd_1214695 : Nat := 46201658045424461772313

theorem tailTrace_1214695 : CollatzResearch.WordTrace tailWord_1214695 prefixEnd_1214695 46201658045424461772313 := by
  unfold tailWord_1214695
  simp only [CollatzResearch.WordTrace]
  refine ⟨44303566334374943234901539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29535710889583295489934359 44303566334374943234901539)
  ·
    refine ⟨66455349501562414852352309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44303566334374943234901539 66455349501562414852352309)
    ·
      refine ⟨6230189015771476392408029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 66455349501562414852352309 6230189015771476392408029)
      ·
        refine ⟨2336320880914303647153011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6230189015771476392408029 2336320880914303647153011)
        ·
          refine ⟨3504481321371455470729517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2336320880914303647153011 3504481321371455470729517)
          ·
            refine ⟨1314180495514295801523569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3504481321371455470729517 1314180495514295801523569)
            ·
              refine ⟨985635371635721851142677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1314180495514295801523569 985635371635721851142677)
              ·
                refine ⟨46201658045424461772313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 985635371635721851142677 46201658045424461772313)
                ·
                  rfl

theorem cell22_1214695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 2, 6].length) (baseStart_1214695 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1214695 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1214695 prefixEnd_1214695 := by exact prefixLift 1214695
  have htrace : WordTrace (prefixWord ++ tailWord_1214695) baseStart_1214695 baseEnd_1214695 := by
    simpa [prefixWord, tailWord_1214695, baseEnd_1214695] using wordTrace_append hprefix tailTrace_1214695
  have hstable : (prefixWord ++ tailWord_1214695).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1214695).length < 2 ^ (prefixWord ++ tailWord_1214695).sum := by decide
  have hdescent : baseEnd_1214695 < baseStart_1214695 := by decide
  rcases family_descends (prefixWord ++ tailWord_1214695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1214800 : List Nat := [2, 1, 1, 1, 1, 6, 2, 3, 2, 3]
def baseStart_1214800 : Nat := 118140960795 + 1214800 * 2 ^ 59
def prefixEnd_1214800 : Nat := 4983230072969 + 3 ^ 40 * 1214800 * 2
def baseEnd_1214800 : Nat := 415850866054634882075495

theorem tailTrace_1214800 : CollatzResearch.WordTrace tailWord_1214800 prefixEnd_1214800 415850866054634882075495 := by
  unfold tailWord_1214800
  simp only [CollatzResearch.WordTrace]
  refine ⟨22153697999497273083736927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29538263999329697444982569 22153697999497273083736927)
  ·
    refine ⟨33230546999245909625605391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22153697999497273083736927 33230546999245909625605391)
    ·
      refine ⟨49845820498868864438408087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33230546999245909625605391 49845820498868864438408087)
      ·
        refine ⟨74768730748303296657612131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49845820498868864438408087 74768730748303296657612131)
        ·
          refine ⟨112153096122454944986418197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74768730748303296657612131 112153096122454944986418197)
          ·
            refine ⟨5257176380740075546238353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 112153096122454944986418197 5257176380740075546238353)
            ·
              refine ⟨3942882285555056659678765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5257176380740075546238353 3942882285555056659678765)
              ·
                refine ⟨1478580857083146247379537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3942882285555056659678765 1478580857083146247379537)
                ·
                  refine ⟨1108935642812359685534653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1478580857083146247379537 1108935642812359685534653)
                  ·
                    refine ⟨415850866054634882075495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1108935642812359685534653 415850866054634882075495)
                    ·
                      rfl

theorem cell22_1214800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 2, 3, 2, 3].length) (baseStart_1214800 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1214800 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1214800 prefixEnd_1214800 := by exact prefixLift 1214800
  have htrace : WordTrace (prefixWord ++ tailWord_1214800) baseStart_1214800 baseEnd_1214800 := by
    simpa [prefixWord, tailWord_1214800, baseEnd_1214800] using wordTrace_append hprefix tailTrace_1214800
  have hstable : (prefixWord ++ tailWord_1214800).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1214800).length < 2 ^ (prefixWord ++ tailWord_1214800).sum := by decide
  have hdescent : baseEnd_1214800 < baseStart_1214800 := by decide
  rcases family_descends (prefixWord ++ tailWord_1214800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1214845 : List Nat := [1, 4, 1, 1, 2, 3, 1, 3, 3, 3]
def baseStart_1214845 : Nat := 118140960795 + 1214845 * 2 ^ 59
def prefixEnd_1214845 : Nat := 4983230072969 + 3 ^ 40 * 1214845 * 2
def baseEnd_1214845 : Nat := 415866270474269764700357

theorem tailTrace_1214845 : CollatzResearch.WordTrace tailWord_1214845 prefixEnd_1214845 415866270474269764700357 := by
  unfold tailWord_1214845
  simp only [CollatzResearch.WordTrace]
  refine ⟨44309037283831518852861989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29539358189221012568574659 44309037283831518852861989)
  ·
    refine ⟨8307944490718409784911623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44309037283831518852861989 8307944490718409784911623)
    ·
      refine ⟨12461916736077614677367435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8307944490718409784911623 12461916736077614677367435)
      ·
        refine ⟨18692875104116422016051153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12461916736077614677367435 18692875104116422016051153)
        ·
          refine ⟨14019656328087316512038365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18692875104116422016051153 14019656328087316512038365)
          ·
            refine ⟨5257371123032743692014387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14019656328087316512038365 5257371123032743692014387)
            ·
              refine ⟨7886056684549115538021581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5257371123032743692014387 7886056684549115538021581)
              ·
                refine ⟨2957271256705918326758093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7886056684549115538021581 2957271256705918326758093)
                ·
                  refine ⟨1108976721264719372534285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2957271256705918326758093 1108976721264719372534285)
                  ·
                    refine ⟨415866270474269764700357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1108976721264719372534285 415866270474269764700357)
                    ·
                      rfl

theorem cell22_1214845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 3, 3, 3].length) (baseStart_1214845 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1214845 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1214845 prefixEnd_1214845 := by exact prefixLift 1214845
  have htrace : WordTrace (prefixWord ++ tailWord_1214845) baseStart_1214845 baseEnd_1214845 := by
    simpa [prefixWord, tailWord_1214845, baseEnd_1214845] using wordTrace_append hprefix tailTrace_1214845
  have hstable : (prefixWord ++ tailWord_1214845).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1214845).length < 2 ^ (prefixWord ++ tailWord_1214845).sum := by decide
  have hdescent : baseEnd_1214845 < baseStart_1214845 := by decide
  rcases family_descends (prefixWord ++ tailWord_1214845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1214862 : List Nat := [4, 1, 1, 4, 1, 1, 2, 2, 3, 3]
def baseStart_1214862 : Nat := 118140960795 + 1214862 * 2 ^ 59
def prefixEnd_1214862 : Nat := 4983230072969 + 3 ^ 40 * 1214862 * 2
def baseEnd_1214862 : Nat := 415872089921687387025305

theorem tailTrace_1214862 : CollatzResearch.WordTrace tailWord_1214862 prefixEnd_1214862 415872089921687387025305 := by
  unfold tailWord_1214862
  simp only [CollatzResearch.WordTrace]
  refine ⟨5538707165596241344528855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29539771549846620504153893 5538707165596241344528855)
  ·
    refine ⟨8308060748394362016793283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5538707165596241344528855 8308060748394362016793283)
    ·
      refine ⟨12462091122591543025189925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8308060748394362016793283 12462091122591543025189925)
      ·
        refine ⟨2336642085485914317223111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12462091122591543025189925 2336642085485914317223111)
        ·
          refine ⟨3504963128228871475834667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2336642085485914317223111 3504963128228871475834667)
          ·
            refine ⟨5257444692343307213752001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3504963128228871475834667 5257444692343307213752001)
            ·
              refine ⟨3943083519257480410314001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5257444692343307213752001 3943083519257480410314001)
              ·
                refine ⟨2957312639443110307735501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3943083519257480410314001 2957312639443110307735501)
                ·
                  refine ⟨1108992239791166365400813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2957312639443110307735501 1108992239791166365400813)
                  ·
                    refine ⟨415872089921687387025305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1108992239791166365400813 415872089921687387025305)
                    ·
                      rfl

theorem cell22_1214862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 2, 2, 3, 3].length) (baseStart_1214862 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1214862 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1214862 prefixEnd_1214862 := by exact prefixLift 1214862
  have htrace : WordTrace (prefixWord ++ tailWord_1214862) baseStart_1214862 baseEnd_1214862 := by
    simpa [prefixWord, tailWord_1214862, baseEnd_1214862] using wordTrace_append hprefix tailTrace_1214862
  have hstable : (prefixWord ++ tailWord_1214862).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1214862).length < 2 ^ (prefixWord ++ tailWord_1214862).sum := by decide
  have hdescent : baseEnd_1214862 < baseStart_1214862 := by decide
  rcases family_descends (prefixWord ++ tailWord_1214862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1214870 : List Nat := [5, 3, 1, 2, 2, 1, 1, 3, 4]
def baseStart_1214870 : Nat := 118140960795 + 1214870 * 2 ^ 59
def prefixEnd_1214870 : Nat := 4983230072969 + 3 ^ 40 * 1214870 * 2
def baseEnd_1214870 : Nat := 138624942828392677608427

theorem tailTrace_1214870 : CollatzResearch.WordTrace tailWord_1214870 prefixEnd_1214870 138624942828392677608427 := by
  unfold tailWord_1214870
  simp only [CollatzResearch.WordTrace]
  refine ⟨2769371819296309257657629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 29539966072493965415014709 2769371819296309257657629)
  ·
    refine ⟨1038514432236115971621611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2769371819296309257657629 1038514432236115971621611)
    ·
      refine ⟨1557771648354173957432417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1038514432236115971621611 1557771648354173957432417)
      ·
        refine ⟨1168328736265630468074313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1557771648354173957432417 1168328736265630468074313)
        ·
          refine ⟨876246552199222851055735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1168328736265630468074313 876246552199222851055735)
          ·
            refine ⟨1314369828298834276583603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 876246552199222851055735 1314369828298834276583603)
            ·
              refine ⟨1971554742448251414875405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1314369828298834276583603 1971554742448251414875405)
              ·
                refine ⟨739333028418094280578277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1971554742448251414875405 739333028418094280578277)
                ·
                  refine ⟨138624942828392677608427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 739333028418094280578277 138624942828392677608427)
                  ·
                    rfl

theorem cell22_1214870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 1, 3, 4].length) (baseStart_1214870 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1214870 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1214870 prefixEnd_1214870 := by exact prefixLift 1214870
  have htrace : WordTrace (prefixWord ++ tailWord_1214870) baseStart_1214870 baseEnd_1214870 := by
    simpa [prefixWord, tailWord_1214870, baseEnd_1214870] using wordTrace_append hprefix tailTrace_1214870
  have hstable : (prefixWord ++ tailWord_1214870).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1214870).length < 2 ^ (prefixWord ++ tailWord_1214870).sum := by decide
  have hdescent : baseEnd_1214870 < baseStart_1214870 := by decide
  rcases family_descends (prefixWord ++ tailWord_1214870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1214952 : List Nat := [2, 1, 4, 1, 1, 3, 1, 4, 2, 3]
def baseStart_1214952 : Nat := 118140960795 + 1214952 * 2 ^ 59
def prefixEnd_1214952 : Nat := 4983230072969 + 3 ^ 40 * 1214952 * 2
def baseEnd_1214952 : Nat := 415902898760957152275029

theorem tailTrace_1214952 : CollatzResearch.WordTrace tailWord_1214952 prefixEnd_1214952 415902898760957152275029 := by
  unfold tailWord_1214952
  simp only [CollatzResearch.WordTrace]
  refine ⟨22156469947221938063503555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29541959929629250751338073 22156469947221938063503555)
  ·
    refine ⟨33234704920832907095255333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22156469947221938063503555 33234704920832907095255333)
    ·
      refine ⟨6231507172656170080360375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33234704920832907095255333 6231507172656170080360375)
      ·
        refine ⟨9347260758984255120540563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6231507172656170080360375 9347260758984255120540563)
        ·
          refine ⟨14020891138476382680810845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9347260758984255120540563 14020891138476382680810845)
          ·
            refine ⟨5257834176928643505304067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14020891138476382680810845 5257834176928643505304067)
            ·
              refine ⟨7886751265392965257956101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5257834176928643505304067 7886751265392965257956101)
              ·
                refine ⟨1478765862261180985866769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7886751265392965257956101 1478765862261180985866769)
                ·
                  refine ⟨1109074396695885739400077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1478765862261180985866769 1109074396695885739400077)
                  ·
                    refine ⟨415902898760957152275029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1109074396695885739400077 415902898760957152275029)
                    ·
                      rfl

theorem cell22_1214952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 4, 2, 3].length) (baseStart_1214952 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1214952 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1214952 prefixEnd_1214952 := by exact prefixLift 1214952
  have htrace : WordTrace (prefixWord ++ tailWord_1214952) baseStart_1214952 baseEnd_1214952 := by
    simpa [prefixWord, tailWord_1214952, baseEnd_1214952] using wordTrace_append hprefix tailTrace_1214952
  have hstable : (prefixWord ++ tailWord_1214952).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1214952).length < 2 ^ (prefixWord ++ tailWord_1214952).sum := by decide
  have hdescent : baseEnd_1214952 < baseStart_1214952 := by decide
  rcases family_descends (prefixWord ++ tailWord_1214952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1214954 : List Nat := [3, 1, 3, 1, 3, 1, 4, 2, 4]
def baseStart_1214954 : Nat := 118140960795 + 1214954 * 2 ^ 59
def prefixEnd_1214954 : Nat := 4983230072969 + 3 ^ 40 * 1214954 * 2
def baseEnd_1214954 : Nat := 138634527800609937908341

theorem tailTrace_1214954 : CollatzResearch.WordTrace tailWord_1214954 prefixEnd_1214954 138634527800609937908341 := by
  unfold tailWord_1214954
  simp only [CollatzResearch.WordTrace]
  refine ⟨11078253210109157617144979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29542008560291086979053277 11078253210109157617144979)
  ·
    refine ⟨16617379815163736425717469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11078253210109157617144979 16617379815163736425717469)
    ·
      refine ⟨6231517430686401159644051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16617379815163736425717469 6231517430686401159644051)
      ·
        refine ⟨9347276146029601739466077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6231517430686401159644051 9347276146029601739466077)
        ·
          refine ⟨3505228554761100652299779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9347276146029601739466077 3505228554761100652299779)
          ·
            refine ⟨5257842832141650978449669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3505228554761100652299779 5257842832141650978449669)
            ·
              refine ⟨985845531026559558459313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5257842832141650978449669 985845531026559558459313)
              ·
                refine ⟨739384148269919668844485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 985845531026559558459313 739384148269919668844485)
                ·
                  refine ⟨138634527800609937908341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 739384148269919668844485 138634527800609937908341)
                  ·
                    rfl

theorem cell22_1214954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 4, 2, 4].length) (baseStart_1214954 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1214954 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1214954 prefixEnd_1214954 := by exact prefixLift 1214954
  have htrace : WordTrace (prefixWord ++ tailWord_1214954) baseStart_1214954 baseEnd_1214954 := by
    simpa [prefixWord, tailWord_1214954, baseEnd_1214954] using wordTrace_append hprefix tailTrace_1214954
  have hstable : (prefixWord ++ tailWord_1214954).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1214954).length < 2 ^ (prefixWord ++ tailWord_1214954).sum := by decide
  have hdescent : baseEnd_1214954 < baseStart_1214954 := by decide
  rcases family_descends (prefixWord ++ tailWord_1214954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1215025 : List Nat := [1, 2, 2, 3, 1, 1, 4, 1, 2, 5]
def baseStart_1215025 : Nat := 118140960795 + 1215025 * 2 ^ 59
def prefixEnd_1215025 : Nat := 4983230072969 + 3 ^ 40 * 1215025 * 2
def baseEnd_1215025 : Nat := 415927888152809295199805

theorem tailTrace_1215025 : CollatzResearch.WordTrace tailWord_1215025 prefixEnd_1215025 415927888152809295199805 := by
  unfold tailWord_1215025
  simp only [CollatzResearch.WordTrace]
  refine ⟨44315602423179409594414529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29543734948786273062943019 44315602423179409594414529)
  ·
    refine ⟨33236701817384557195810897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44315602423179409594414529 33236701817384557195810897)
    ·
      refine ⟨24927526363038417896858173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33236701817384557195810897 24927526363038417896858173)
      ·
        refine ⟨9347822386139406711321815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24927526363038417896858173 9347822386139406711321815)
        ·
          refine ⟨14021733579209110066982723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9347822386139406711321815 14021733579209110066982723)
          ·
            refine ⟨21032600368813665100474085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14021733579209110066982723 21032600368813665100474085)
            ·
              refine ⟨3943612569152562206338891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21032600368813665100474085 3943612569152562206338891)
              ·
                refine ⟨5915418853728843309508337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3943612569152562206338891 5915418853728843309508337)
                ·
                  refine ⟨4436564140296632482131253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5915418853728843309508337 4436564140296632482131253)
                  ·
                    refine ⟨415927888152809295199805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4436564140296632482131253 415927888152809295199805)
                    ·
                      rfl

theorem cell22_1215025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4, 1, 2, 5].length) (baseStart_1215025 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1215025 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1215025 prefixEnd_1215025 := by exact prefixLift 1215025
  have htrace : WordTrace (prefixWord ++ tailWord_1215025) baseStart_1215025 baseEnd_1215025 := by
    simpa [prefixWord, tailWord_1215025, baseEnd_1215025] using wordTrace_append hprefix tailTrace_1215025
  have hstable : (prefixWord ++ tailWord_1215025).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1215025).length < 2 ^ (prefixWord ++ tailWord_1215025).sum := by decide
  have hdescent : baseEnd_1215025 < baseStart_1215025 := by decide
  rcases family_descends (prefixWord ++ tailWord_1215025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1215027 : List Nat := [1, 1, 1, 2, 4, 2, 5, 1, 5]
def baseStart_1215027 : Nat := 118140960795 + 1215027 * 2 ^ 59
def prefixEnd_1215027 : Nat := 4983230072969 + 3 ^ 40 * 1215027 * 2
def baseEnd_1215027 : Nat := 138642857597893985549933

theorem tailTrace_1215027 : CollatzResearch.WordTrace tailWord_1215027 prefixEnd_1215027 138642857597893985549933 := by
  unfold tailWord_1215027
  simp only [CollatzResearch.WordTrace]
  refine ⟨44315675369172163935987335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29543783579448109290658223 44315675369172163935987335)
  ·
    refine ⟨66473513053758245903981003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44315675369172163935987335 66473513053758245903981003)
    ·
      refine ⟨99710269580637368855971505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66473513053758245903981003 99710269580637368855971505)
      ·
        refine ⟨74782702185478026641978629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99710269580637368855971505 74782702185478026641978629)
        ·
          refine ⟨14021756659777129995370993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 74782702185478026641978629 14021756659777129995370993)
          ·
            refine ⟨10516317494832847496528245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14021756659777129995370993 10516317494832847496528245)
            ·
              refine ⟨985904765140579452799523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10516317494832847496528245 985904765140579452799523)
              ·
                refine ⟨1478857147710869179199285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 985904765140579452799523 1478857147710869179199285)
                ·
                  refine ⟨138642857597893985549933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1478857147710869179199285 138642857597893985549933)
                  ·
                    rfl

theorem cell22_1215027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 5, 1, 5].length) (baseStart_1215027 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1215027 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1215027 prefixEnd_1215027 := by exact prefixLift 1215027
  have htrace : WordTrace (prefixWord ++ tailWord_1215027) baseStart_1215027 baseEnd_1215027 := by
    simpa [prefixWord, tailWord_1215027, baseEnd_1215027] using wordTrace_append hprefix tailTrace_1215027
  have hstable : (prefixWord ++ tailWord_1215027).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1215027).length < 2 ^ (prefixWord ++ tailWord_1215027).sum := by decide
  have hdescent : baseEnd_1215027 < baseStart_1215027 := by decide
  rcases family_descends (prefixWord ++ tailWord_1215027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1215040 : List Nat := [2, 1, 1, 2, 2, 2, 2, 3, 3, 4]
def baseStart_1215040 : Nat := 118140960795 + 1215040 * 2 ^ 59
def prefixEnd_1215040 : Nat := 4983230072969 + 3 ^ 40 * 1215040 * 2
def baseEnd_1215040 : Nat := 415933022959354256074759

theorem tailTrace_1215040 : CollatzResearch.WordTrace tailWord_1215040 prefixEnd_1215040 415933022959354256074759 := by
  unfold tailWord_1215040
  simp only [CollatzResearch.WordTrace]
  refine ⟨22158074759062533578105287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29544099678750044770807049 22158074759062533578105287)
  ·
    refine ⟨33237112138593800367157931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22158074759062533578105287 33237112138593800367157931)
    ·
      refine ⟨49855668207890700550736897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33237112138593800367157931 49855668207890700550736897)
      ·
        refine ⟨37391751155918025413052673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49855668207890700550736897 37391751155918025413052673)
        ·
          refine ⟨28043813366938519059789505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37391751155918025413052673 28043813366938519059789505)
          ·
            refine ⟨21032860025203889294842129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28043813366938519059789505 21032860025203889294842129)
            ·
              refine ⟨15774645018902916971131597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21032860025203889294842129 15774645018902916971131597)
              ·
                refine ⟨5915491882088593864174349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15774645018902916971131597 5915491882088593864174349)
                ·
                  refine ⟨2218309455783222699065381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5915491882088593864174349 2218309455783222699065381)
                  ·
                    refine ⟨415933022959354256074759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2218309455783222699065381 415933022959354256074759)
                    ·
                      rfl

theorem cell22_1215040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 3, 3, 4].length) (baseStart_1215040 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1215040 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1215040 prefixEnd_1215040 := by exact prefixLift 1215040
  have htrace : WordTrace (prefixWord ++ tailWord_1215040) baseStart_1215040 baseEnd_1215040 := by
    simpa [prefixWord, tailWord_1215040, baseEnd_1215040] using wordTrace_append hprefix tailTrace_1215040
  have hstable : (prefixWord ++ tailWord_1215040).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1215040).length < 2 ^ (prefixWord ++ tailWord_1215040).sum := by decide
  have hdescent : baseEnd_1215040 < baseStart_1215040 := by decide
  rcases family_descends (prefixWord ++ tailWord_1215040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1215057 : List Nat := [1, 2, 2, 1, 3, 3, 2, 3, 1, 4]
def baseStart_1215057 : Nat := 118140960795 + 1215057 * 2 ^ 59
def prefixEnd_1215057 : Nat := 4983230072969 + 3 ^ 40 * 1215057 * 2
def baseEnd_1215057 : Nat := 415938842406771878399707

theorem tailTrace_1215057 : CollatzResearch.WordTrace tailWord_1215057 prefixEnd_1215057 415938842406771878399707 := by
  unfold tailWord_1215057
  simp only [CollatzResearch.WordTrace]
  refine ⟨44316769559063479059579425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29544513039375652706386283 44316769559063479059579425)
  ·
    refine ⟨33237577169297609294684569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44316769559063479059579425 33237577169297609294684569)
    ·
      refine ⟨24928182876973206971013427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33237577169297609294684569 24928182876973206971013427)
      ·
        refine ⟨37392274315459810456520141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24928182876973206971013427 37392274315459810456520141)
        ·
          refine ⟨14022102868297428921195053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37392274315459810456520141 14022102868297428921195053)
          ·
            refine ⟨5258288575611535845448145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14022102868297428921195053 5258288575611535845448145)
            ·
              refine ⟨3943716431708651884086109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5258288575611535845448145 3943716431708651884086109)
              ·
                refine ⟨1478893661890744456532291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3943716431708651884086109 1478893661890744456532291)
                ·
                  refine ⟨2218340492836116684798437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1478893661890744456532291 2218340492836116684798437)
                  ·
                    refine ⟨415938842406771878399707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2218340492836116684798437 415938842406771878399707)
                    ·
                      rfl

theorem cell22_1215057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 2, 3, 1, 4].length) (baseStart_1215057 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1215057 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1215057 prefixEnd_1215057 := by exact prefixLift 1215057
  have htrace : WordTrace (prefixWord ++ tailWord_1215057) baseStart_1215057 baseEnd_1215057 := by
    simpa [prefixWord, tailWord_1215057, baseEnd_1215057] using wordTrace_append hprefix tailTrace_1215057
  have hstable : (prefixWord ++ tailWord_1215057).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1215057).length < 2 ^ (prefixWord ++ tailWord_1215057).sum := by decide
  have hdescent : baseEnd_1215057 < baseStart_1215057 := by decide
  rcases family_descends (prefixWord ++ tailWord_1215057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1215072 : List Nat := [2, 1, 1, 3, 2, 1, 2, 6, 4]
def baseStart_1215072 : Nat := 118140960795 + 1215072 * 2 ^ 59
def prefixEnd_1215072 : Nat := 4983230072969 + 3 ^ 40 * 1215072 * 2
def baseEnd_1215072 : Nat := 138647992404438946424887

theorem tailTrace_1215072 : CollatzResearch.WordTrace tailWord_1215072 prefixEnd_1215072 138647992404438946424887 := by
  unfold tailWord_1215072
  simp only [CollatzResearch.WordTrace]
  refine ⟨22158658327004568310687735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29544877769339424414250313 22158658327004568310687735)
  ·
    refine ⟨33237987490506852466031603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22158658327004568310687735 33237987490506852466031603)
    ·
      refine ⟨49856981235760278699047405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33237987490506852466031603 49856981235760278699047405)
      ·
        refine ⟨18696367963410104512142777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49856981235760278699047405 18696367963410104512142777)
        ·
          refine ⟨14022275972557578384107083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18696367963410104512142777 14022275972557578384107083)
          ·
            refine ⟨21033413958836367576160625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14022275972557578384107083 21033413958836367576160625)
            ·
              refine ⟨15775060469127275682120469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21033413958836367576160625 15775060469127275682120469)
              ·
                refine ⟨739455959490341047599397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 15775060469127275682120469 739455959490341047599397)
                ·
                  refine ⟨138647992404438946424887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 739455959490341047599397 138647992404438946424887)
                  ·
                    rfl

theorem cell22_1215072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 6, 4].length) (baseStart_1215072 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1215072 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1215072 prefixEnd_1215072 := by exact prefixLift 1215072
  have htrace : WordTrace (prefixWord ++ tailWord_1215072) baseStart_1215072 baseEnd_1215072 := by
    simpa [prefixWord, tailWord_1215072, baseEnd_1215072] using wordTrace_append hprefix tailTrace_1215072
  have hstable : (prefixWord ++ tailWord_1215072).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1215072).length < 2 ^ (prefixWord ++ tailWord_1215072).sum := by decide
  have hdescent : baseEnd_1215072 < baseStart_1215072 := by decide
  rcases family_descends (prefixWord ++ tailWord_1215072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1215100 : List Nat := [2, 2, 2, 1, 1, 2, 4, 8]
def baseStart_1215100 : Nat := 118140960795 + 1215100 * 2 ^ 59
def prefixEnd_1215100 : Nat := 4983230072969 + 3 ^ 40 * 1215100 * 2
def baseEnd_1215100 : Nat := 46217062465059344397175

theorem tailTrace_1215100 : CollatzResearch.WordTrace tailWord_1215100 prefixEnd_1215100 46217062465059344397175 := by
  unfold tailWord_1215100
  simp only [CollatzResearch.WordTrace]
  refine ⟨22159168948953848701697377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29545558598605131602263169 22159168948953848701697377)
  ·
    refine ⟨16619376711715386526273033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22159168948953848701697377 16619376711715386526273033)
    ·
      refine ⟨12464532533786539894704775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16619376711715386526273033 12464532533786539894704775)
      ·
        refine ⟨18696798800679809842057163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12464532533786539894704775 18696798800679809842057163)
        ·
          refine ⟨28045198201019714763085745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18696798800679809842057163 28045198201019714763085745)
          ·
            refine ⟨21033898650764786072314309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28045198201019714763085745 21033898650764786072314309)
            ·
              refine ⟨3943855997018397388558933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21033898650764786072314309 3943855997018397388558933)
              ·
                refine ⟨46217062465059344397175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3943855997018397388558933 46217062465059344397175)
                ·
                  rfl

theorem cell22_1215100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4, 8].length) (baseStart_1215100 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1215100 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1215100 prefixEnd_1215100 := by exact prefixLift 1215100
  have htrace : WordTrace (prefixWord ++ tailWord_1215100) baseStart_1215100 baseEnd_1215100 := by
    simpa [prefixWord, tailWord_1215100, baseEnd_1215100] using wordTrace_append hprefix tailTrace_1215100
  have hstable : (prefixWord ++ tailWord_1215100).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1215100).length < 2 ^ (prefixWord ++ tailWord_1215100).sum := by decide
  have hdescent : baseEnd_1215100 < baseStart_1215100 := by decide
  rcases family_descends (prefixWord ++ tailWord_1215100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1215149 : List Nat := [1, 5, 2, 1, 1, 2, 1, 1, 5, 3]
def baseStart_1215149 : Nat := 118140960795 + 1215149 * 2 ^ 59
def prefixEnd_1215149 : Nat := 4983230072969 + 3 ^ 40 * 1215149 * 2
def baseEnd_1215149 : Nat := 415970335886914305099425

theorem tailTrace_1215149 : CollatzResearch.WordTrace tailWord_1215149 prefixEnd_1215149 415970335886914305099425 := by
  unfold tailWord_1215149
  simp only [CollatzResearch.WordTrace]
  refine ⟨44320125074730178771928501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29546750049820119181285667 44320125074730178771928501)
  ·
    refine ⟨4155011725755954259868297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 44320125074730178771928501 4155011725755954259868297)
    ·
      refine ⟨3116258794316965694901223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4155011725755954259868297 3116258794316965694901223)
      ·
        refine ⟨4674388191475448542351835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3116258794316965694901223 4674388191475448542351835)
        ·
          refine ⟨7011582287213172813527753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4674388191475448542351835 7011582287213172813527753)
          ·
            refine ⟨5258686715409879610145815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7011582287213172813527753 5258686715409879610145815)
            ·
              refine ⟨7888030073114819415218723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5258686715409879610145815 7888030073114819415218723)
              ·
                refine ⟨11832045109672229122828085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7888030073114819415218723 11832045109672229122828085)
                ·
                  refine ⟨1109254229031771480265133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 11832045109672229122828085 1109254229031771480265133)
                  ·
                    refine ⟨415970335886914305099425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1109254229031771480265133 415970335886914305099425)
                    ·
                      rfl

theorem cell22_1215149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 1, 5, 3].length) (baseStart_1215149 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1215149 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1215149 prefixEnd_1215149 := by exact prefixLift 1215149
  have htrace : WordTrace (prefixWord ++ tailWord_1215149) baseStart_1215149 baseEnd_1215149 := by
    simpa [prefixWord, tailWord_1215149, baseEnd_1215149] using wordTrace_append hprefix tailTrace_1215149
  have hstable : (prefixWord ++ tailWord_1215149).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1215149).length < 2 ^ (prefixWord ++ tailWord_1215149).sum := by decide
  have hdescent : baseEnd_1215149 < baseStart_1215149 := by decide
  rcases family_descends (prefixWord ++ tailWord_1215149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1215153 : List Nat := [1, 2, 2, 6, 2, 1, 1, 1, 2, 4]
def baseStart_1215153 : Nat := 118140960795 + 1215153 * 2 ^ 59
def prefixEnd_1215153 : Nat := 4983230072969 + 3 ^ 40 * 1215153 * 2
def baseEnd_1215153 : Nat := 415971705168659627999413

theorem tailTrace_1215153 : CollatzResearch.WordTrace tailWord_1215153 prefixEnd_1215153 415971705168659627999413 := by
  unfold tailWord_1215153
  simp only [CollatzResearch.WordTrace]
  refine ⟨44320270966715687455074113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29546847311143791636716075 44320270966715687455074113)
  ·
    refine ⟨33240203225036765591305585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44320270966715687455074113 33240203225036765591305585)
    ·
      refine ⟨24930152418777574193479189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33240203225036765591305585 24930152418777574193479189)
      ·
        refine ⟨1168600894630198790319337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 24930152418777574193479189 1168600894630198790319337)
        ·
          refine ⟨876450670972649092739503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1168600894630198790319337 876450670972649092739503)
          ·
            refine ⟨1314676006458973639109255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 876450670972649092739503 1314676006458973639109255)
            ·
              refine ⟨1972014009688460458663883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1314676006458973639109255 1972014009688460458663883)
              ·
                refine ⟨2958021014532690687995825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1972014009688460458663883 2958021014532690687995825)
                ·
                  refine ⟨2218515760899518015996869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2958021014532690687995825 2218515760899518015996869)
                  ·
                    refine ⟨415971705168659627999413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2218515760899518015996869 415971705168659627999413)
                    ·
                      rfl

theorem cell22_1215153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 1, 1, 2, 4].length) (baseStart_1215153 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1215153 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1215153 prefixEnd_1215153 := by exact prefixLift 1215153
  have htrace : WordTrace (prefixWord ++ tailWord_1215153) baseStart_1215153 baseEnd_1215153 := by
    simpa [prefixWord, tailWord_1215153, baseEnd_1215153] using wordTrace_append hprefix tailTrace_1215153
  have hstable : (prefixWord ++ tailWord_1215153).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1215153).length < 2 ^ (prefixWord ++ tailWord_1215153).sum := by decide
  have hdescent : baseEnd_1215153 < baseStart_1215153 := by decide
  rcases family_descends (prefixWord ++ tailWord_1215153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1215286 : List Nat := [5, 1, 2, 2, 3, 9]
def baseStart_1215286 : Nat := 118140960795 + 1215286 * 2 ^ 59
def prefixEnd_1215286 : Nat := 4983230072969 + 3 ^ 40 * 1215286 * 2
def baseEnd_1215286 : Nat := 5136015231934464375605

theorem tailTrace_1215286 : CollatzResearch.WordTrace tailWord_1215286 prefixEnd_1215286 5136015231934464375605 := by
  unfold tailWord_1215286
  simp only [CollatzResearch.WordTrace]
  refine ⟨2770320117202115698104107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 29550081250155900779777141 2770320117202115698104107)
  ·
    refine ⟨4155480175803173547156161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2770320117202115698104107 4155480175803173547156161)
    ·
      refine ⟨3116610131852380160367121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4155480175803173547156161 3116610131852380160367121)
      ·
        refine ⟨2337457598889285120275341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3116610131852380160367121 2337457598889285120275341)
        ·
          refine ⟨876546599583481920103253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2337457598889285120275341 876546599583481920103253)
          ·
            refine ⟨5136015231934464375605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 876546599583481920103253 5136015231934464375605)
            ·
              rfl

theorem cell22_1215286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 9].length) (baseStart_1215286 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1215286 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1215286 prefixEnd_1215286 := by exact prefixLift 1215286
  have htrace : WordTrace (prefixWord ++ tailWord_1215286) baseStart_1215286 baseEnd_1215286 := by
    simpa [prefixWord, tailWord_1215286, baseEnd_1215286] using wordTrace_append hprefix tailTrace_1215286
  have hstable : (prefixWord ++ tailWord_1215286).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1215286).length < 2 ^ (prefixWord ++ tailWord_1215286).sum := by decide
  have hdescent : baseEnd_1215286 < baseStart_1215286 := by decide
  rcases family_descends (prefixWord ++ tailWord_1215286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1215312 : List Nat := [2, 1, 1, 1, 1, 4, 3, 1, 1, 7]
def baseStart_1215312 : Nat := 118140960795 + 1215312 * 2 ^ 59
def prefixEnd_1215312 : Nat := 4983230072969 + 3 ^ 40 * 1215312 * 2
def baseEnd_1215312 : Nat := 416026134118036213273925

theorem tailTrace_1215312 : CollatzResearch.WordTrace tailWord_1215312 prefixEnd_1215312 416026134118036213273925 := by
  unfold tailWord_1215312
  simp only [CollatzResearch.WordTrace]
  refine ⟨22163035086569828805056095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29550713448759771740074793 22163035086569828805056095)
  ·
    refine ⟨33244552629854743207584143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22163035086569828805056095 33244552629854743207584143)
    ·
      refine ⟨49866828944782114811376215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33244552629854743207584143 49866828944782114811376215)
      ·
        refine ⟨74800243417173172217064323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49866828944782114811376215 74800243417173172217064323)
        ·
          refine ⟨112200365125759758325596485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74800243417173172217064323 112200365125759758325596485)
          ·
            refine ⟨21037568461079954686049341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 112200365125759758325596485 21037568461079954686049341)
            ·
              refine ⟨7889088172904983007268503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21037568461079954686049341 7889088172904983007268503)
              ·
                refine ⟨11833632259357474510902755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7889088172904983007268503 11833632259357474510902755)
                ·
                  refine ⟨17750448389036211766354133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11833632259357474510902755 17750448389036211766354133)
                  ·
                    refine ⟨416026134118036213273925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17750448389036211766354133 416026134118036213273925)
                    ·
                      rfl

theorem cell22_1215312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 1, 1, 7].length) (baseStart_1215312 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1215312 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1215312 prefixEnd_1215312 := by exact prefixLift 1215312
  have htrace : WordTrace (prefixWord ++ tailWord_1215312) baseStart_1215312 baseEnd_1215312 := by
    simpa [prefixWord, tailWord_1215312, baseEnd_1215312] using wordTrace_append hprefix tailTrace_1215312
  have hstable : (prefixWord ++ tailWord_1215312).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1215312).length < 2 ^ (prefixWord ++ tailWord_1215312).sum := by decide
  have hdescent : baseEnd_1215312 < baseStart_1215312 := by decide
  rcases family_descends (prefixWord ++ tailWord_1215312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1215314 : List Nat := [3, 2, 2, 1, 1, 2, 1, 5, 5]
def baseStart_1215314 : Nat := 118140960795 + 1215314 * 2 ^ 59
def prefixEnd_1215314 : Nat := 4983230072969 + 3 ^ 40 * 1215314 * 2
def baseEnd_1215314 : Nat := 138675606252969624907973

theorem tailTrace_1215314 : CollatzResearch.WordTrace tailWord_1215314 prefixEnd_1215314 138675606252969624907973 := by
  unfold tailWord_1215314
  simp only [CollatzResearch.WordTrace]
  refine ⟨11081535779783102987921249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29550762079421607967789997 11081535779783102987921249)
  ·
    refine ⟨8311151834837327240940937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11081535779783102987921249 8311151834837327240940937)
    ·
      refine ⟨6233363876127995430705703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8311151834837327240940937 6233363876127995430705703)
      ·
        refine ⟨9350045814191993146058555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6233363876127995430705703 9350045814191993146058555)
        ·
          refine ⟨14025068721287989719087833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9350045814191993146058555 14025068721287989719087833)
          ·
            refine ⟨10518801540965992289315875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14025068721287989719087833 10518801540965992289315875)
            ·
              refine ⟨15778202311448988433973813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10518801540965992289315875 15778202311448988433973813)
              ·
                refine ⟨1479206466698342665685045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15778202311448988433973813 1479206466698342665685045)
                ·
                  refine ⟨138675606252969624907973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1479206466698342665685045 138675606252969624907973)
                  ·
                    rfl

theorem cell22_1215314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 5, 5].length) (baseStart_1215314 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1215314 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1215314 prefixEnd_1215314 := by exact prefixLift 1215314
  have htrace : WordTrace (prefixWord ++ tailWord_1215314) baseStart_1215314 baseEnd_1215314 := by
    simpa [prefixWord, tailWord_1215314, baseEnd_1215314] using wordTrace_append hprefix tailTrace_1215314
  have hstable : (prefixWord ++ tailWord_1215314).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1215314).length < 2 ^ (prefixWord ++ tailWord_1215314).sum := by decide
  have hdescent : baseEnd_1215314 < baseStart_1215314 := by decide
  rcases family_descends (prefixWord ++ tailWord_1215314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1215389 : List Nat := [1, 4, 2, 1, 2, 1, 1, 3, 1, 6]
def baseStart_1215389 : Nat := 118140960795 + 1215389 * 2 ^ 59
def prefixEnd_1215389 : Nat := 4983230072969 + 3 ^ 40 * 1215389 * 2
def baseEnd_1215389 : Nat := 416052492791633679098689

theorem tailTrace_1215389 : CollatzResearch.WordTrace tailWord_1215389 prefixEnd_1215389 416052492791633679098689 := by
  unfold tailWord_1215389
  simp only [CollatzResearch.WordTrace]
  refine ⟨44328878593860699760665221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29552585729240466507110147 44328878593860699760665221)
  ·
    refine ⟨8311664736348881205124729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44328878593860699760665221 8311664736348881205124729)
    ·
      refine ⟨6233748552261660903843547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8311664736348881205124729 6233748552261660903843547)
      ·
        refine ⟨9350622828392491355765321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6233748552261660903843547 9350622828392491355765321)
        ·
          refine ⟨7012967121294368516823991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9350622828392491355765321 7012967121294368516823991)
          ·
            refine ⟨10519450681941552775235987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7012967121294368516823991 10519450681941552775235987)
            ·
              refine ⟨15779176022912329162853981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10519450681941552775235987 15779176022912329162853981)
              ·
                refine ⟨5917191008592123436070243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15779176022912329162853981 5917191008592123436070243)
                ·
                  refine ⟨8875786512888185154105365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5917191008592123436070243 8875786512888185154105365)
                  ·
                    refine ⟨416052492791633679098689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8875786512888185154105365 416052492791633679098689)
                    ·
                      rfl

theorem cell22_1215389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 3, 1, 6].length) (baseStart_1215389 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1215389 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1215389 prefixEnd_1215389 := by exact prefixLift 1215389
  have htrace : WordTrace (prefixWord ++ tailWord_1215389) baseStart_1215389 baseEnd_1215389 := by
    simpa [prefixWord, tailWord_1215389, baseEnd_1215389] using wordTrace_append hprefix tailTrace_1215389
  have hstable : (prefixWord ++ tailWord_1215389).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1215389).length < 2 ^ (prefixWord ++ tailWord_1215389).sum := by decide
  have hdescent : baseEnd_1215389 < baseStart_1215389 := by decide
  rcases family_descends (prefixWord ++ tailWord_1215389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1215391 : List Nat := [1, 1, 2, 5, 2, 1, 1, 2, 4, 3]
def baseStart_1215391 : Nat := 118140960795 + 1215391 * 2 ^ 59
def prefixEnd_1215391 : Nat := 4983230072969 + 3 ^ 40 * 1215391 * 2
def baseEnd_1215391 : Nat := 416053177432506340548683

theorem tailTrace_1215391 : CollatzResearch.WordTrace tailWord_1215391 prefixEnd_1215391 416053177432506340548683 := by
  unfold tailWord_1215391
  simp only [CollatzResearch.WordTrace]
  refine ⟨44328951539853454102238027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29552634359902302734825351 44328951539853454102238027)
  ·
    refine ⟨66493427309780181153357041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44328951539853454102238027 66493427309780181153357041)
    ·
      refine ⟨49870070482335135865017781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66493427309780181153357041 49870070482335135865017781)
      ·
        refine ⟨4675319107718918987345417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 49870070482335135865017781 4675319107718918987345417)
        ·
          refine ⟨3506489330789189240509063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4675319107718918987345417 3506489330789189240509063)
          ·
            refine ⟨5259733996183783860763595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3506489330789189240509063 5259733996183783860763595)
            ·
              refine ⟨7889600994275675791145393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5259733996183783860763595 7889600994275675791145393)
              ·
                refine ⟨5917200745706756843359045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7889600994275675791145393 5917200745706756843359045)
                ·
                  refine ⟨1109475139820016908129821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5917200745706756843359045 1109475139820016908129821)
                  ·
                    refine ⟨416053177432506340548683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1109475139820016908129821 416053177432506340548683)
                    ·
                      rfl

theorem cell22_1215391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 2, 4, 3].length) (baseStart_1215391 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1215391 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1215391 prefixEnd_1215391 := by exact prefixLift 1215391
  have htrace : WordTrace (prefixWord ++ tailWord_1215391) baseStart_1215391 baseEnd_1215391 := by
    simpa [prefixWord, tailWord_1215391, baseEnd_1215391] using wordTrace_append hprefix tailTrace_1215391
  have hstable : (prefixWord ++ tailWord_1215391).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1215391).length < 2 ^ (prefixWord ++ tailWord_1215391).sum := by decide
  have hdescent : baseEnd_1215391 < baseStart_1215391 := by decide
  rcases family_descends (prefixWord ++ tailWord_1215391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1215393 : List Nat := [1, 2, 3, 4, 1, 1, 3, 3, 4]
def baseStart_1215393 : Nat := 118140960795 + 1215393 * 2 ^ 59
def prefixEnd_1215393 : Nat := 4983230072969 + 3 ^ 40 * 1215393 * 2
def baseEnd_1215393 : Nat := 138684620691126333999559

theorem tailTrace_1215393 : CollatzResearch.WordTrace tailWord_1215393 prefixEnd_1215393 138684620691126333999559 := by
  unfold tailWord_1215393
  simp only [CollatzResearch.WordTrace]
  refine ⟨44329024485846208443810833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29552682990564138962540555 44329024485846208443810833)
  ·
    refine ⟨33246768364384656332858125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44329024485846208443810833 33246768364384656332858125)
    ·
      refine ⟨12467538136644246124821797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33246768364384656332858125 12467538136644246124821797)
      ·
        refine ⟨2337663400620796148404087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12467538136644246124821797 2337663400620796148404087)
        ·
          refine ⟨3506495100931194222606131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2337663400620796148404087 3506495100931194222606131)
          ·
            refine ⟨5259742651396791333909197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3506495100931194222606131 5259742651396791333909197)
            ·
              refine ⟨1972403494273796750215949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5259742651396791333909197 1972403494273796750215949)
              ·
                refine ⟨739651310352673781330981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1972403494273796750215949 739651310352673781330981)
                ·
                  refine ⟨138684620691126333999559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 739651310352673781330981 138684620691126333999559)
                  ·
                    rfl

theorem cell22_1215393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 3, 3, 4].length) (baseStart_1215393 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1215393 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1215393 prefixEnd_1215393 := by exact prefixLift 1215393
  have htrace : WordTrace (prefixWord ++ tailWord_1215393) baseStart_1215393 baseEnd_1215393 := by
    simpa [prefixWord, tailWord_1215393, baseEnd_1215393] using wordTrace_append hprefix tailTrace_1215393
  have hstable : (prefixWord ++ tailWord_1215393).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1215393).length < 2 ^ (prefixWord ++ tailWord_1215393).sum := by decide
  have hdescent : baseEnd_1215393 < baseStart_1215393 := by decide
  rcases family_descends (prefixWord ++ tailWord_1215393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1215421 : List Nat := [1, 4, 1, 2, 4, 1, 2, 7]
def baseStart_1215421 : Nat := 118140960795 + 1215421 * 2 ^ 59
def prefixEnd_1215421 : Nat := 4983230072969 + 3 ^ 40 * 1215421 * 2
def baseEnd_1215421 : Nat := 46229271893955140255399

theorem tailTrace_1215421 : CollatzResearch.WordTrace tailWord_1215421 prefixEnd_1215421 46229271893955140255399 := by
  unfold tailWord_1215421
  simp only [CollatzResearch.WordTrace]
  refine ⟨44330045729744769225830117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29553363819829846150553411 44330045729744769225830117)
  ·
    refine ⟨8311883574327144229843147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44330045729744769225830117 8311883574327144229843147)
    ·
      refine ⟨12467825361490716344764721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8311883574327144229843147 12467825361490716344764721)
      ·
        refine ⟨9350869021118037258573541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12467825361490716344764721 9350869021118037258573541)
        ·
          refine ⟨1753287941459631985982539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9350869021118037258573541 1753287941459631985982539)
          ·
            refine ⟨2629931912189447978973809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1753287941459631985982539 2629931912189447978973809)
            ·
              refine ⟨1972448934142085984230357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2629931912189447978973809 1972448934142085984230357)
              ·
                refine ⟨46229271893955140255399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1972448934142085984230357 46229271893955140255399)
                ·
                  rfl

theorem cell22_1215421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 2, 7].length) (baseStart_1215421 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1215421 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1215421 prefixEnd_1215421 := by exact prefixLift 1215421
  have htrace : WordTrace (prefixWord ++ tailWord_1215421) baseStart_1215421 baseEnd_1215421 := by
    simpa [prefixWord, tailWord_1215421, baseEnd_1215421] using wordTrace_append hprefix tailTrace_1215421
  have hstable : (prefixWord ++ tailWord_1215421).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1215421).length < 2 ^ (prefixWord ++ tailWord_1215421).sum := by decide
  have hdescent : baseEnd_1215421 < baseStart_1215421 := by decide
  rcases family_descends (prefixWord ++ tailWord_1215421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1215436 : List Nat := [2, 2, 1, 4, 1, 1, 2, 1, 5, 3]
def baseStart_1215436 : Nat := 118140960795 + 1215436 * 2 ^ 59
def prefixEnd_1215436 : Nat := 4983230072969 + 3 ^ 40 * 1215436 * 2
def baseEnd_1215436 : Nat := 416068581852141223173545

theorem tailTrace_1215436 : CollatzResearch.WordTrace tailWord_1215436 prefixEnd_1215436 416068581852141223173545 := by
  unfold tailWord_1215436
  simp only [CollatzResearch.WordTrace]
  refine ⟨22165296412345213393813081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29553728549793617858417441 22165296412345213393813081)
  ·
    refine ⟨16623972309258910045359811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22165296412345213393813081 16623972309258910045359811)
    ·
      refine ⟨24935958463888365068039717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16623972309258910045359811 24935958463888365068039717)
      ·
        refine ⟨4675492211979068450257447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24935958463888365068039717 4675492211979068450257447)
        ·
          refine ⟨7013238317968602675386171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4675492211979068450257447 7013238317968602675386171)
          ·
            refine ⟨10519857476952904013079257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7013238317968602675386171 10519857476952904013079257)
            ·
              refine ⟨7889893107714678009809443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10519857476952904013079257 7889893107714678009809443)
              ·
                refine ⟨11834839661572017014714165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7889893107714678009809443 11834839661572017014714165)
                ·
                  refine ⟨1109516218272376595129453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 11834839661572017014714165 1109516218272376595129453)
                  ·
                    refine ⟨416068581852141223173545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1109516218272376595129453 416068581852141223173545)
                    ·
                      rfl

theorem cell22_1215436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 1, 5, 3].length) (baseStart_1215436 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1215436 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1215436 prefixEnd_1215436 := by exact prefixLift 1215436
  have htrace : WordTrace (prefixWord ++ tailWord_1215436) baseStart_1215436 baseEnd_1215436 := by
    simpa [prefixWord, tailWord_1215436, baseEnd_1215436] using wordTrace_append hprefix tailTrace_1215436
  have hstable : (prefixWord ++ tailWord_1215436).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1215436).length < 2 ^ (prefixWord ++ tailWord_1215436).sum := by decide
  have hdescent : baseEnd_1215436 < baseStart_1215436 := by decide
  rcases family_descends (prefixWord ++ tailWord_1215436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1215466 : List Nat := [3, 1, 3, 1, 2, 2, 1, 4, 5]
def baseStart_1215466 : Nat := 118140960795 + 1215466 * 2 ^ 59
def prefixEnd_1215466 : Nat := 4983230072969 + 3 ^ 40 * 1215466 * 2
def baseEnd_1215466 : Nat := 138692950488410381641151

theorem tailTrace_1215466 : CollatzResearch.WordTrace tailWord_1215466 prefixEnd_1215466 138692950488410381641151 := by
  unfold tailWord_1215466
  simp only [CollatzResearch.WordTrace]
  refine ⟨11082921753645435477804563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29554458009721161274145501 11082921753645435477804563)
  ·
    refine ⟨16624382630468153216706845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11082921753645435477804563 16624382630468153216706845)
    ·
      refine ⟨6234143486425557456265067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16624382630468153216706845 6234143486425557456265067)
      ·
        refine ⟨9351215229638336184397601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6234143486425557456265067 9351215229638336184397601)
        ·
          refine ⟨7013411422228752138298201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9351215229638336184397601 7013411422228752138298201)
          ·
            refine ⟨5260058566671564103723651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7013411422228752138298201 5260058566671564103723651)
            ·
              refine ⟨7890087850007346155585477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5260058566671564103723651 7890087850007346155585477)
              ·
                refine ⟨1479391471876377404172277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7890087850007346155585477 1479391471876377404172277)
                ·
                  refine ⟨138692950488410381641151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1479391471876377404172277 138692950488410381641151)
                  ·
                    rfl

theorem cell22_1215466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 4, 5].length) (baseStart_1215466 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1215466 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1215466 prefixEnd_1215466 := by exact prefixLift 1215466
  have htrace : WordTrace (prefixWord ++ tailWord_1215466) baseStart_1215466 baseEnd_1215466 := by
    simpa [prefixWord, tailWord_1215466, baseEnd_1215466] using wordTrace_append hprefix tailTrace_1215466
  have hstable : (prefixWord ++ tailWord_1215466).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1215466).length < 2 ^ (prefixWord ++ tailWord_1215466).sum := by decide
  have hdescent : baseEnd_1215466 < baseStart_1215466 := by decide
  rcases family_descends (prefixWord ++ tailWord_1215466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1215496 : List Nat := [2, 1, 3, 2, 1, 3, 2, 1, 3, 4]
def baseStart_1215496 : Nat := 118140960795 + 1215496 * 2 ^ 59
def prefixEnd_1215496 : Nat := 4983230072969 + 3 ^ 40 * 1215496 * 2
def baseEnd_1215496 : Nat := 416089121078321066673361

theorem tailTrace_1215496 : CollatzResearch.WordTrace tailWord_1215496 prefixEnd_1215496 416089121078321066673361 := by
  unfold tailWord_1215496
  simp only [CollatzResearch.WordTrace]
  refine ⟨22166390602236528517405171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29555187469648704689873561 22166390602236528517405171)
  ·
    refine ⟨33249585903354792776107757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22166390602236528517405171 33249585903354792776107757)
    ·
      refine ⟨12468594713758047291040409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33249585903354792776107757 12468594713758047291040409)
      ·
        refine ⟨9351446035318535468280307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12468594713758047291040409 9351446035318535468280307)
        ·
          refine ⟨14027169052977803202420461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9351446035318535468280307 14027169052977803202420461)
          ·
            refine ⟨5260188394866676200907673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14027169052977803202420461 5260188394866676200907673)
            ·
              refine ⟨3945141296150007150680755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5260188394866676200907673 3945141296150007150680755)
              ·
                refine ⟨5917711944225010726021133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3945141296150007150680755 5917711944225010726021133)
                ·
                  refine ⟨2219141979084379022257925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5917711944225010726021133 2219141979084379022257925)
                  ·
                    refine ⟨416089121078321066673361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2219141979084379022257925 416089121078321066673361)
                    ·
                      rfl

theorem cell22_1215496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2, 1, 3, 4].length) (baseStart_1215496 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1215496 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1215496 prefixEnd_1215496 := by exact prefixLift 1215496
  have htrace : WordTrace (prefixWord ++ tailWord_1215496) baseStart_1215496 baseEnd_1215496 := by
    simpa [prefixWord, tailWord_1215496, baseEnd_1215496] using wordTrace_append hprefix tailTrace_1215496
  have hstable : (prefixWord ++ tailWord_1215496).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1215496).length < 2 ^ (prefixWord ++ tailWord_1215496).sum := by decide
  have hdescent : baseEnd_1215496 < baseStart_1215496 := by decide
  rcases family_descends (prefixWord ++ tailWord_1215496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1215513 : List Nat := [1, 2, 1, 2, 1, 1, 8, 1, 1, 4]
def baseStart_1215513 : Nat := 118140960795 + 1215513 * 2 ^ 59
def prefixEnd_1215513 : Nat := 4983230072969 + 3 ^ 40 * 1215513 * 2
def baseEnd_1215513 : Nat := 416094940525738688998309

theorem tailTrace_1215513 : CollatzResearch.WordTrace tailWord_1215513 prefixEnd_1215513 416094940525738688998309 := by
  unfold tailWord_1215513
  simp only [CollatzResearch.WordTrace]
  refine ⟨44333401245411468938179193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29555600830274312625452795 44333401245411468938179193)
  ·
    refine ⟨33250050934058601703634395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44333401245411468938179193 33250050934058601703634395)
    ·
      refine ⟨49875076401087902555451593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33250050934058601703634395 49875076401087902555451593)
      ·
        refine ⟨37406307300815926916588695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49875076401087902555451593 37406307300815926916588695)
        ·
          refine ⟨56109460951223890374883043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37406307300815926916588695 56109460951223890374883043)
          ·
            refine ⟨84164191426835835562324565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56109460951223890374883043 84164191426835835562324565)
            ·
              refine ⟨986299118283232447995991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 84164191426835835562324565 986299118283232447995991)
              ·
                refine ⟨1479448677424848671993987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 986299118283232447995991 1479448677424848671993987)
                ·
                  refine ⟨2219173016137273007990981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1479448677424848671993987 2219173016137273007990981)
                  ·
                    refine ⟨416094940525738688998309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2219173016137273007990981 416094940525738688998309)
                    ·
                      rfl

theorem cell22_1215513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 8, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 8, 1, 1, 4].length) (baseStart_1215513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1215513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1215513 prefixEnd_1215513 := by exact prefixLift 1215513
  have htrace : WordTrace (prefixWord ++ tailWord_1215513) baseStart_1215513 baseEnd_1215513 := by
    simpa [prefixWord, tailWord_1215513, baseEnd_1215513] using wordTrace_append hprefix tailTrace_1215513
  have hstable : (prefixWord ++ tailWord_1215513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1215513).length < 2 ^ (prefixWord ++ tailWord_1215513).sum := by decide
  have hdescent : baseEnd_1215513 < baseStart_1215513 := by decide
  rcases family_descends (prefixWord ++ tailWord_1215513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1215539 : List Nat := [1, 1, 1, 2, 4, 1, 1, 11]
def baseStart_1215539 : Nat := 118140960795 + 1215539 * 2 ^ 59
def prefixEnd_1215539 : Nat := 4983230072969 + 3 ^ 40 * 1215539 * 2
def baseEnd_1215539 : Nat := 46233760095231476427581

theorem tailTrace_1215539 : CollatzResearch.WordTrace tailWord_1215539 prefixEnd_1215539 46233760095231476427581 := by
  unfold tailWord_1215539
  simp only [CollatzResearch.WordTrace]
  refine ⟨44334349543317275378625671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29556233028878183585750447 44334349543317275378625671)
  ·
    refine ⟨66501524314975913067938507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44334349543317275378625671 66501524314975913067938507)
    ·
      refine ⟨99752286472463869601907761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66501524314975913067938507 99752286472463869601907761)
      ·
        refine ⟨74814214854347902201430821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99752286472463869601907761 74814214854347902201430821)
        ·
          refine ⟨14027665285190231662768279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 74814214854347902201430821 14027665285190231662768279)
          ·
            refine ⟨21041497927785347494152419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14027665285190231662768279 21041497927785347494152419)
            ·
              refine ⟨31562246891678021241228629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21041497927785347494152419 31562246891678021241228629)
              ·
                refine ⟨46233760095231476427581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 31562246891678021241228629 46233760095231476427581)
                ·
                  rfl

theorem cell22_1215539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 11].length) (baseStart_1215539 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1215539 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1215539 prefixEnd_1215539 := by exact prefixLift 1215539
  have htrace : WordTrace (prefixWord ++ tailWord_1215539) baseStart_1215539 baseEnd_1215539 := by
    simpa [prefixWord, tailWord_1215539, baseEnd_1215539] using wordTrace_append hprefix tailTrace_1215539
  have hstable : (prefixWord ++ tailWord_1215539).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1215539).length < 2 ^ (prefixWord ++ tailWord_1215539).sum := by decide
  have hdescent : baseEnd_1215539 < baseStart_1215539 := by decide
  rcases family_descends (prefixWord ++ tailWord_1215539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1215571 : List Nat := [1, 1, 1, 2, 1, 1, 2, 3, 7, 3]
def baseStart_1215571 : Nat := 118140960795 + 1215571 * 2 ^ 59
def prefixEnd_1215571 : Nat := 4983230072969 + 3 ^ 40 * 1215571 * 2
def baseEnd_1215571 : Nat := 416114795111045871048131

theorem tailTrace_1215571 : CollatzResearch.WordTrace tailWord_1215571 prefixEnd_1215571 416114795111045871048131 := by
  unfold tailWord_1215571
  simp only [CollatzResearch.WordTrace]
  refine ⟨44335516679201344843790567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29557011119467563229193711 44335516679201344843790567)
  ·
    refine ⟨66503275018802017265685851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44335516679201344843790567 66503275018802017265685851)
    ·
      refine ⟨99754912528203025898528777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66503275018802017265685851 99754912528203025898528777)
      ·
        refine ⟨74816184396152269423896583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99754912528203025898528777 74816184396152269423896583)
        ·
          refine ⟨112224276594228404135844875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74816184396152269423896583 112224276594228404135844875)
          ·
            refine ⟨168336414891342606203767313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112224276594228404135844875 168336414891342606203767313)
            ·
              refine ⟨126252311168506954652825485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 168336414891342606203767313 126252311168506954652825485)
              ·
                refine ⟨47344616688190107994809557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 126252311168506954652825485 47344616688190107994809557)
                ·
                  refine ⟨1109639453629455656128349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 47344616688190107994809557 1109639453629455656128349)
                  ·
                    refine ⟨416114795111045871048131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1109639453629455656128349 416114795111045871048131)
                    ·
                      rfl

theorem cell22_1215571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 3, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 3, 7, 3].length) (baseStart_1215571 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1215571 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1215571 prefixEnd_1215571 := by exact prefixLift 1215571
  have htrace : WordTrace (prefixWord ++ tailWord_1215571) baseStart_1215571 baseEnd_1215571 := by
    simpa [prefixWord, tailWord_1215571, baseEnd_1215571] using wordTrace_append hprefix tailTrace_1215571
  have hstable : (prefixWord ++ tailWord_1215571).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1215571).length < 2 ^ (prefixWord ++ tailWord_1215571).sum := by decide
  have hdescent : baseEnd_1215571 < baseStart_1215571 := by decide
  rcases family_descends (prefixWord ++ tailWord_1215571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1215639 : List Nat := [1, 1, 3, 3, 3, 3, 2, 2, 1, 3]
def baseStart_1215639 : Nat := 118140960795 + 1215639 * 2 ^ 59
def prefixEnd_1215639 : Nat := 4983230072969 + 3 ^ 40 * 1215639 * 2
def baseEnd_1215639 : Nat := 416138072900716360347923

theorem tailTrace_1215639 : CollatzResearch.WordTrace tailWord_1215639 prefixEnd_1215639 416138072900716360347923 := by
  unfold tailWord_1215639
  simp only [CollatzResearch.WordTrace]
  refine ⟨44337996842954992457265971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29558664561969994971510647 44337996842954992457265971)
  ·
    refine ⟨66506995264432488685898957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44337996842954992457265971 66506995264432488685898957)
    ·
      refine ⟨24940123224162183257212109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66506995264432488685898957 24940123224162183257212109)
      ·
        refine ⟨9352546209060818721454541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24940123224162183257212109 9352546209060818721454541)
        ·
          refine ⟨3507204828397807020545453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9352546209060818721454541 3507204828397807020545453)
          ·
            refine ⟨1315201810649177632704545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3507204828397807020545453 1315201810649177632704545)
            ·
              refine ⟨986401357986883224528409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1315201810649177632704545 986401357986883224528409)
              ·
                refine ⟨739801018490162418396307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 986401357986883224528409 739801018490162418396307)
                ·
                  refine ⟨1109701527735243627594461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 739801018490162418396307 1109701527735243627594461)
                  ·
                    refine ⟨416138072900716360347923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1109701527735243627594461 416138072900716360347923)
                    ·
                      rfl

theorem cell22_1215639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 2, 2, 1, 3].length) (baseStart_1215639 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1215639 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1215639 prefixEnd_1215639 := by exact prefixLift 1215639
  have htrace : WordTrace (prefixWord ++ tailWord_1215639) baseStart_1215639 baseEnd_1215639 := by
    simpa [prefixWord, tailWord_1215639, baseEnd_1215639] using wordTrace_append hprefix tailTrace_1215639
  have hstable : (prefixWord ++ tailWord_1215639).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1215639).length < 2 ^ (prefixWord ++ tailWord_1215639).sum := by decide
  have hdescent : baseEnd_1215639 < baseStart_1215639 := by decide
  rcases family_descends (prefixWord ++ tailWord_1215639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1215650 : List Nat := [3, 3, 1, 3, 2, 1, 1, 1, 2, 5]
def baseStart_1215650 : Nat := 118140960795 + 1215650 * 2 ^ 59
def prefixEnd_1215650 : Nat := 4983230072969 + 3 ^ 40 * 1215650 * 2
def baseEnd_1215650 : Nat := 416141838425515998322889

theorem tailTrace_1215650 : CollatzResearch.WordTrace tailWord_1215650 prefixEnd_1215650 416141838425515998322889 := by
  unfold tailWord_1215650
  simp only [CollatzResearch.WordTrace]
  refine ⟨11084599511478785333979101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29558932030610094223944269 11084599511478785333979101)
  ·
    refine ⟨4156724816804544500242163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11084599511478785333979101 4156724816804544500242163)
    ·
      refine ⟨6235087225206816750363245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4156724816804544500242163 6235087225206816750363245)
      ·
        refine ⟨2338157709452556281386217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6235087225206816750363245 2338157709452556281386217)
        ·
          refine ⟨1753618282089417211039663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2338157709452556281386217 1753618282089417211039663)
          ·
            refine ⟨2630427423134125816559495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1753618282089417211039663 2630427423134125816559495)
            ·
              refine ⟨3945641134701188724839243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2630427423134125816559495 3945641134701188724839243)
              ·
                refine ⟨5918461702051783087258865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3945641134701188724839243 5918461702051783087258865)
                ·
                  refine ⟨4438846276538837315444149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5918461702051783087258865 4438846276538837315444149)
                  ·
                    refine ⟨416141838425515998322889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4438846276538837315444149 416141838425515998322889)
                    ·
                      rfl

theorem cell22_1215650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 1, 1, 2, 5].length) (baseStart_1215650 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1215650 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1215650 prefixEnd_1215650 := by exact prefixLift 1215650
  have htrace : WordTrace (prefixWord ++ tailWord_1215650) baseStart_1215650 baseEnd_1215650 := by
    simpa [prefixWord, tailWord_1215650, baseEnd_1215650] using wordTrace_append hprefix tailTrace_1215650
  have hstable : (prefixWord ++ tailWord_1215650).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1215650).length < 2 ^ (prefixWord ++ tailWord_1215650).sum := by decide
  have hdescent : baseEnd_1215650 < baseStart_1215650 := by decide
  rcases family_descends (prefixWord ++ tailWord_1215650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1215686 : List Nat := [6, 1, 2, 2, 1, 2, 1, 2, 5]
def baseStart_1215686 : Nat := 118140960795 + 1215686 * 2 ^ 59
def prefixEnd_1215686 : Nat := 4983230072969 + 3 ^ 40 * 1215686 * 2
def baseEnd_1215686 : Nat := 138718053987074634807593

theorem tailTrace_1215686 : CollatzResearch.WordTrace tailWord_1215686 prefixEnd_1215686 138718053987074634807593 := by
  unfold tailWord_1215686
  simp only [CollatzResearch.WordTrace]
  refine ⟨1385615971055772483882091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 29559807382523146322817941 1385615971055772483882091)
  ·
    refine ⟨2078423956583658725823137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1385615971055772483882091 2078423956583658725823137)
    ·
      refine ⟨1558817967437744044367353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2078423956583658725823137 1558817967437744044367353)
      ·
        refine ⟨1169113475578308033275515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1558817967437744044367353 1169113475578308033275515)
        ·
          refine ⟨1753670213367462049913273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1169113475578308033275515 1753670213367462049913273)
          ·
            refine ⟨1315252660025596537434955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1753670213367462049913273 1315252660025596537434955)
            ·
              refine ⟨1972878990038394806152433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1315252660025596537434955 1972878990038394806152433)
              ·
                refine ⟨1479659242528796104614325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1972878990038394806152433 1479659242528796104614325)
                ·
                  refine ⟨138718053987074634807593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1479659242528796104614325 138718053987074634807593)
                  ·
                    rfl

theorem cell22_1215686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 1, 2, 5].length) (baseStart_1215686 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1215686 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1215686 prefixEnd_1215686 := by exact prefixLift 1215686
  have htrace : WordTrace (prefixWord ++ tailWord_1215686) baseStart_1215686 baseEnd_1215686 := by
    simpa [prefixWord, tailWord_1215686, baseEnd_1215686] using wordTrace_append hprefix tailTrace_1215686
  have hstable : (prefixWord ++ tailWord_1215686).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1215686).length < 2 ^ (prefixWord ++ tailWord_1215686).sum := by decide
  have hdescent : baseEnd_1215686 < baseStart_1215686 := by decide
  rcases family_descends (prefixWord ++ tailWord_1215686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1215712 : List Nat := [2, 1, 1, 3, 1, 5, 3, 1, 2, 3]
def baseStart_1215712 : Nat := 118140960795 + 1215712 * 2 ^ 59
def prefixEnd_1215712 : Nat := 4983230072969 + 3 ^ 40 * 1215712 * 2
def baseEnd_1215712 : Nat := 416163062292568503272699

theorem tailTrace_1215712 : CollatzResearch.WordTrace tailWord_1215712 prefixEnd_1215712 416163062292568503272699 := by
  unfold tailWord_1215712
  simp only [CollatzResearch.WordTrace]
  refine ⟨22170329685845262962336695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29560439581127017283115593 22170329685845262962336695)
  ·
    refine ⟨33255494528767894443505043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22170329685845262962336695 33255494528767894443505043)
    ·
      refine ⟨49883241793151841665257565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33255494528767894443505043 49883241793151841665257565)
      ·
        refine ⟨18706215672431940624471587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49883241793151841665257565 18706215672431940624471587)
        ·
          refine ⟨28059323508647910936707381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18706215672431940624471587 28059323508647910936707381)
          ·
            refine ⟨2630561578935741650316317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 28059323508647910936707381 2630561578935741650316317)
            ·
              refine ⟨986460592100903118868619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2630561578935741650316317 986460592100903118868619)
              ·
                refine ⟨1479690888151354678302929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 986460592100903118868619 1479690888151354678302929)
                ·
                  refine ⟨1109768166113516008727197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1479690888151354678302929 1109768166113516008727197)
                  ·
                    refine ⟨416163062292568503272699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1109768166113516008727197 416163062292568503272699)
                    ·
                      rfl

theorem cell22_1215712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 3, 1, 2, 3].length) (baseStart_1215712 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1215712 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1215712 prefixEnd_1215712 := by exact prefixLift 1215712
  have htrace : WordTrace (prefixWord ++ tailWord_1215712) baseStart_1215712 baseEnd_1215712 := by
    simpa [prefixWord, tailWord_1215712, baseEnd_1215712] using wordTrace_append hprefix tailTrace_1215712
  have hstable : (prefixWord ++ tailWord_1215712).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1215712).length < 2 ^ (prefixWord ++ tailWord_1215712).sum := by decide
  have hdescent : baseEnd_1215712 < baseStart_1215712 := by decide
  rcases family_descends (prefixWord ++ tailWord_1215712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1215725 : List Nat := [1, 5, 1, 2, 2, 1, 4, 6]
def baseStart_1215725 : Nat := 118140960795 + 1215725 * 2 ^ 59
def prefixEnd_1215725 : Nat := 4983230072969 + 3 ^ 40 * 1215725 * 2
def baseEnd_1215725 : Nat := 46240834717582311410851

theorem tailTrace_1215725 : CollatzResearch.WordTrace tailWord_1215725 prefixEnd_1215725 46240834717582311410851 := by
  unfold tailWord_1215725
  simp only [CollatzResearch.WordTrace]
  refine ⟨44341133520643429144896629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29560755680428952763264419 44341133520643429144896629)
  ·
    refine ⟨4156981267560321482334059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 44341133520643429144896629 4156981267560321482334059)
    ·
      refine ⟨6235471901340482223501089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4156981267560321482334059 6235471901340482223501089)
      ·
        refine ⟨4676603926005361667625817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6235471901340482223501089 4676603926005361667625817)
        ·
          refine ⟨3507452944504021250719363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4676603926005361667625817 3507452944504021250719363)
          ·
            refine ⟨5261179416756031876079045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3507452944504021250719363 5261179416756031876079045)
            ·
              refine ⟨986471140641755976764821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5261179416756031876079045 986471140641755976764821)
              ·
                refine ⟨46240834717582311410851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 986471140641755976764821 46240834717582311410851)
                ·
                  rfl

theorem cell22_1215725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 4, 6].length) (baseStart_1215725 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1215725 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1215725 prefixEnd_1215725 := by exact prefixLift 1215725
  have htrace : WordTrace (prefixWord ++ tailWord_1215725) baseStart_1215725 baseEnd_1215725 := by
    simpa [prefixWord, tailWord_1215725, baseEnd_1215725] using wordTrace_append hprefix tailTrace_1215725
  have hstable : (prefixWord ++ tailWord_1215725).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1215725).length < 2 ^ (prefixWord ++ tailWord_1215725).sum := by decide
  have hdescent : baseEnd_1215725 < baseStart_1215725 := by decide
  rcases family_descends (prefixWord ++ tailWord_1215725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1215753 : List Nat := [1, 2, 1, 1, 3, 3, 2, 4, 5]
def baseStart_1215753 : Nat := 118140960795 + 1215753 * 2 ^ 59
def prefixEnd_1215753 : Nat := 4983230072969 + 3 ^ 40 * 1215753 * 2
def baseEnd_1215753 : Nat := 138725699143486020999191

theorem tailTrace_1215753 : CollatzResearch.WordTrace tailWord_1215753 prefixEnd_1215753 138725699143486020999191 := by
  unfold tailWord_1215753
  simp only [CollatzResearch.WordTrace]
  refine ⟨44342154764541989926915913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29561436509694659951277275 44342154764541989926915913)
  ·
    refine ⟨33256616073406492445186935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44342154764541989926915913 33256616073406492445186935)
    ·
      refine ⟨49884924110109738667780403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33256616073406492445186935 49884924110109738667780403)
      ·
        refine ⟨74827386165164608001670605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49884924110109738667780403 74827386165164608001670605)
        ·
          refine ⟨28060269811936728000626477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74827386165164608001670605 28060269811936728000626477)
          ·
            refine ⟨10522601179476273000234929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28060269811936728000626477 10522601179476273000234929)
            ·
              refine ⟨7891950884607204750176197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10522601179476273000234929 7891950884607204750176197)
              ·
                refine ⟨1479740790863850890658037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7891950884607204750176197 1479740790863850890658037)
                ·
                  refine ⟨138725699143486020999191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1479740790863850890658037 138725699143486020999191)
                  ·
                    rfl

theorem cell22_1215753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 4, 5].length) (baseStart_1215753 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1215753 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1215753 prefixEnd_1215753 := by exact prefixLift 1215753
  have htrace : WordTrace (prefixWord ++ tailWord_1215753) baseStart_1215753 baseEnd_1215753 := by
    simpa [prefixWord, tailWord_1215753, baseEnd_1215753] using wordTrace_append hprefix tailTrace_1215753
  have hstable : (prefixWord ++ tailWord_1215753).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1215753).length < 2 ^ (prefixWord ++ tailWord_1215753).sum := by decide
  have hdescent : baseEnd_1215753 < baseStart_1215753 := by decide
  rcases family_descends (prefixWord ++ tailWord_1215753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1215770 : List Nat := [3, 1, 1, 3, 3, 2, 1, 3, 5]
def baseStart_1215770 : Nat := 118140960795 + 1215770 * 2 ^ 59
def prefixEnd_1215770 : Nat := 4983230072969 + 3 ^ 40 * 1215770 * 2
def baseEnd_1215770 : Nat := 138727638959291895107507

theorem tailTrace_1215770 : CollatzResearch.WordTrace tailWord_1215770 prefixEnd_1215770 138727638959291895107507 := by
  unfold tailWord_1215770
  simp only [CollatzResearch.WordTrace]
  refine ⟨11085693701370100457571191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29561849870320267886856509 11085693701370100457571191)
  ·
    refine ⟨16628540552055150686356787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11085693701370100457571191 16628540552055150686356787)
    ·
      refine ⟨24942810828082726029535181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16628540552055150686356787 24942810828082726029535181)
      ·
        refine ⟨9353554060531022261075693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24942810828082726029535181 9353554060531022261075693)
        ·
          refine ⟨3507582772699133347903385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9353554060531022261075693 3507582772699133347903385)
          ·
            refine ⟨2630687079524350010927539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3507582772699133347903385 2630687079524350010927539)
            ·
              refine ⟨3946030619286525016391309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2630687079524350010927539 3946030619286525016391309)
              ·
                refine ⟨1479761482232446881146741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3946030619286525016391309 1479761482232446881146741)
                ·
                  refine ⟨138727638959291895107507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1479761482232446881146741 138727638959291895107507)
                  ·
                    rfl

theorem cell22_1215770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 1, 3, 5].length) (baseStart_1215770 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1215770 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1215770 prefixEnd_1215770 := by exact prefixLift 1215770
  have htrace : WordTrace (prefixWord ++ tailWord_1215770) baseStart_1215770 baseEnd_1215770 := by
    simpa [prefixWord, tailWord_1215770, baseEnd_1215770] using wordTrace_append hprefix tailTrace_1215770
  have hstable : (prefixWord ++ tailWord_1215770).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1215770).length < 2 ^ (prefixWord ++ tailWord_1215770).sum := by decide
  have hdescent : baseEnd_1215770 < baseStart_1215770 := by decide
  rcases family_descends (prefixWord ++ tailWord_1215770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1215950 : List Nat := [4, 1, 1, 1, 2, 1, 2, 4, 6]
def baseStart_1215950 : Nat := 118140960795 + 1215950 * 2 ^ 59
def prefixEnd_1215950 : Nat := 4983230072969 + 3 ^ 40 * 1215950 * 2
def baseEnd_1215950 : Nat := 138748178185471738607323

theorem tailTrace_1215950 : CollatzResearch.WordTrace tailWord_1215950 prefixEnd_1215950 138748178185471738607323 := by
  unfold tailWord_1215950
  simp only [CollatzResearch.WordTrace]
  refine ⟨5543667493103536571479663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29566226629885528381224869 5543667493103536571479663)
  ·
    refine ⟨8315501239655304857219495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5543667493103536571479663 8315501239655304857219495)
    ·
      refine ⟨12473251859482957285829243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8315501239655304857219495 12473251859482957285829243)
      ·
        refine ⟨18709877789224435928743865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12473251859482957285829243 18709877789224435928743865)
        ·
          refine ⟨14032408341918326946557899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18709877789224435928743865 14032408341918326946557899)
          ·
            refine ⟨21048612512877490419836849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14032408341918326946557899 21048612512877490419836849)
            ·
              refine ⟨15786459384658117814877637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21048612512877490419836849 15786459384658117814877637)
              ·
                refine ⟨2959961134623397090289557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15786459384658117814877637 2959961134623397090289557)
                ·
                  refine ⟨138748178185471738607323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2959961134623397090289557 138748178185471738607323)
                  ·
                    rfl

theorem cell22_1215950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 4, 6].length) (baseStart_1215950 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1215950 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1215950 prefixEnd_1215950 := by exact prefixLift 1215950
  have htrace : WordTrace (prefixWord ++ tailWord_1215950) baseStart_1215950 baseEnd_1215950 := by
    simpa [prefixWord, tailWord_1215950, baseEnd_1215950] using wordTrace_append hprefix tailTrace_1215950
  have hstable : (prefixWord ++ tailWord_1215950).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1215950).length < 2 ^ (prefixWord ++ tailWord_1215950).sum := by decide
  have hdescent : baseEnd_1215950 < baseStart_1215950 := by decide
  rcases family_descends (prefixWord ++ tailWord_1215950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1215967 : List Nat := [1, 1, 2, 3, 3, 1, 2, 5, 4]
def baseStart_1215967 : Nat := 118140960795 + 1215967 * 2 ^ 59
def prefixEnd_1215967 : Nat := 4983230072969 + 3 ^ 40 * 1215967 * 2
def baseEnd_1215967 : Nat := 138750118001277612715639

theorem tailTrace_1215967 : CollatzResearch.WordTrace tailWord_1215967 prefixEnd_1215967 138750118001277612715639 := by
  unfold tailWord_1215967
  simp only [CollatzResearch.WordTrace]
  refine ⟨44349959985766704475206155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29566639990511136316804103 44349959985766704475206155)
  ·
    refine ⟨66524939978650056712809233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44349959985766704475206155 66524939978650056712809233)
    ·
      refine ⟨49893704983987542534606925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66524939978650056712809233 49893704983987542534606925)
      ·
        refine ⟨18710139368995328450477597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49893704983987542534606925 18710139368995328450477597)
        ·
          refine ⟨7016302263373248168929099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18710139368995328450477597 7016302263373248168929099)
          ·
            refine ⟨10524453395059872253393649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7016302263373248168929099 10524453395059872253393649)
            ·
              refine ⟨7893340046294904190045237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10524453395059872253393649 7893340046294904190045237)
              ·
                refine ⟨740000629340147267816741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7893340046294904190045237 740000629340147267816741)
                ·
                  refine ⟨138750118001277612715639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 740000629340147267816741 138750118001277612715639)
                  ·
                    rfl

theorem cell22_1215967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 5, 4].length) (baseStart_1215967 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1215967 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1215967 prefixEnd_1215967 := by exact prefixLift 1215967
  have htrace : WordTrace (prefixWord ++ tailWord_1215967) baseStart_1215967 baseEnd_1215967 := by
    simpa [prefixWord, tailWord_1215967, baseEnd_1215967] using wordTrace_append hprefix tailTrace_1215967
  have hstable : (prefixWord ++ tailWord_1215967).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1215967).length < 2 ^ (prefixWord ++ tailWord_1215967).sum := by decide
  have hdescent : baseEnd_1215967 < baseStart_1215967 := by decide
  rcases family_descends (prefixWord ++ tailWord_1215967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1215969 : List Nat := [1, 2, 3, 1, 2, 4, 3, 1, 1, 4]
def baseStart_1215969 : Nat := 118140960795 + 1215969 * 2 ^ 59
def prefixEnd_1215969 : Nat := 4983230072969 + 3 ^ 40 * 1215969 * 2
def baseEnd_1215969 : Nat := 416251038644705499596911

theorem tailTrace_1215969 : CollatzResearch.WordTrace tailWord_1215969 prefixEnd_1215969 416251038644705499596911 := by
  unfold tailWord_1215969
  simp only [CollatzResearch.WordTrace]
  refine ⟨44350032931759458816778961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29566688621172972544519307 44350032931759458816778961)
  ·
    refine ⟨33262524698819594112584221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44350032931759458816778961 33262524698819594112584221)
    ·
      refine ⟨12473446762057347792219083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33262524698819594112584221 12473446762057347792219083)
      ·
        refine ⟨18710170143086021688328625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12473446762057347792219083 18710170143086021688328625)
        ·
          refine ⟨14032627607314516266246469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18710170143086021688328625 14032627607314516266246469)
          ·
            refine ⟨2631117676371471799921213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14032627607314516266246469 2631117676371471799921213)
            ·
              refine ⟨986669128639301924970455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2631117676371471799921213 986669128639301924970455)
              ·
                refine ⟨1480003692958952887455683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 986669128639301924970455 1480003692958952887455683)
                ·
                  refine ⟨2220005539438429331183525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1480003692958952887455683 2220005539438429331183525)
                  ·
                    refine ⟨416251038644705499596911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2220005539438429331183525 416251038644705499596911)
                    ·
                      rfl

theorem cell22_1215969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 3, 1, 1, 4].length) (baseStart_1215969 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1215969 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1215969 prefixEnd_1215969 := by exact prefixLift 1215969
  have htrace : WordTrace (prefixWord ++ tailWord_1215969) baseStart_1215969 baseEnd_1215969 := by
    simpa [prefixWord, tailWord_1215969, baseEnd_1215969] using wordTrace_append hprefix tailTrace_1215969
  have hstable : (prefixWord ++ tailWord_1215969).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1215969).length < 2 ^ (prefixWord ++ tailWord_1215969).sum := by decide
  have hdescent : baseEnd_1215969 < baseStart_1215969 := by decide
  rcases family_descends (prefixWord ++ tailWord_1215969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1215980 : List Nat := [2, 2, 1, 1, 2, 1, 2, 3, 4, 4]
def baseStart_1215980 : Nat := 118140960795 + 1215980 * 2 ^ 59
def prefixEnd_1215980 : Nat := 4983230072969 + 3 ^ 40 * 1215980 * 2
def baseEnd_1215980 : Nat := 416254804169505137571877

theorem tailTrace_1215980 : CollatzResearch.WordTrace tailWord_1215980 prefixEnd_1215980 416254804169505137571877 := by
  unfold tailWord_1215980
  simp only [CollatzResearch.WordTrace]
  refine ⟨22175217067359803847714697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29566956089813071796952929 22175217067359803847714697)
  ·
    refine ⟨16631412800519852885786023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22175217067359803847714697 16631412800519852885786023)
    ·
      refine ⟨24947119200779779328679035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16631412800519852885786023 24947119200779779328679035)
      ·
        refine ⟨37420678801169668993018553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24947119200779779328679035 37420678801169668993018553)
        ·
          refine ⟨28065509100877251744763915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37420678801169668993018553 28065509100877251744763915)
          ·
            refine ⟨42098263651315877617145873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28065509100877251744763915 42098263651315877617145873)
            ·
              refine ⟨31573697738486908212859405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42098263651315877617145873 31573697738486908212859405)
              ·
                refine ⟨11840136651932590579822277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31573697738486908212859405 11840136651932590579822277)
                ·
                  refine ⟨2220025622237360733716677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11840136651932590579822277 2220025622237360733716677)
                  ·
                    refine ⟨416254804169505137571877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2220025622237360733716677 416254804169505137571877)
                    ·
                      rfl

theorem cell22_1215980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 4].length) (baseStart_1215980 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1215980 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1215980 prefixEnd_1215980 := by exact prefixLift 1215980
  have htrace : WordTrace (prefixWord ++ tailWord_1215980) baseStart_1215980 baseEnd_1215980 := by
    simpa [prefixWord, tailWord_1215980, baseEnd_1215980] using wordTrace_append hprefix tailTrace_1215980
  have hstable : (prefixWord ++ tailWord_1215980).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1215980).length < 2 ^ (prefixWord ++ tailWord_1215980).sum := by decide
  have hdescent : baseEnd_1215980 < baseStart_1215980 := by decide
  rcases family_descends (prefixWord ++ tailWord_1215980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1215984 : List Nat := [2, 1, 1, 1, 3, 4, 4, 2, 4]
def baseStart_1215984 : Nat := 118140960795 + 1215984 * 2 ^ 59
def prefixEnd_1215984 : Nat := 4983230072969 + 3 ^ 40 * 1215984 * 2
def baseEnd_1215984 : Nat := 138752057817083486823955

theorem tailTrace_1215984 : CollatzResearch.WordTrace tailWord_1215984 prefixEnd_1215984 138752057817083486823955 := by
  unfold tailWord_1215984
  simp only [CollatzResearch.WordTrace]
  refine ⟨22175290013352558189287503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29567053351136744252383337 22175290013352558189287503)
  ·
    refine ⟨33262935020028837283931255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22175290013352558189287503 33262935020028837283931255)
    ·
      refine ⟨49894402530043255925896883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33262935020028837283931255 49894402530043255925896883)
      ·
        refine ⟨74841603795064883888845325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49894402530043255925896883 74841603795064883888845325)
        ·
          refine ⟨28065601423149331458316997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74841603795064883888845325 28065601423149331458316997)
          ·
            refine ⟨5262300266840499648434437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28065601423149331458316997 5262300266840499648434437)
            ·
              refine ⟨986681300032593684081457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5262300266840499648434437 986681300032593684081457)
              ·
                refine ⟨740010975024445263061093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 986681300032593684081457 740010975024445263061093)
                ·
                  refine ⟨138752057817083486823955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 740010975024445263061093 138752057817083486823955)
                  ·
                    rfl

theorem cell22_1215984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 4, 2, 4].length) (baseStart_1215984 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1215984 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1215984 prefixEnd_1215984 := by exact prefixLift 1215984
  have htrace : WordTrace (prefixWord ++ tailWord_1215984) baseStart_1215984 baseEnd_1215984 := by
    simpa [prefixWord, tailWord_1215984, baseEnd_1215984] using wordTrace_append hprefix tailTrace_1215984
  have hstable : (prefixWord ++ tailWord_1215984).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1215984).length < 2 ^ (prefixWord ++ tailWord_1215984).sum := by decide
  have hdescent : baseEnd_1215984 < baseStart_1215984 := by decide
  rcases family_descends (prefixWord ++ tailWord_1215984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1216020 : List Nat := [2, 4, 3, 1, 3, 1, 2, 1, 1, 4]
def baseStart_1216020 : Nat := 118140960795 + 1216020 * 2 ^ 59
def prefixEnd_1216020 : Nat := 4983230072969 + 3 ^ 40 * 1216020 * 2
def baseEnd_1216020 : Nat := 416268496986958366571755

theorem tailTrace_1216020 : CollatzResearch.WordTrace tailWord_1216020 prefixEnd_1216020 416268496986958366571755 := by
  unfold tailWord_1216020
  simp only [CollatzResearch.WordTrace]
  refine ⟨22175946527287347263442757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29567928703049796351257009 22175946527287347263442757)
  ·
    refine ⟨4157989973866377611895517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22175946527287347263442757 4157989973866377611895517)
    ·
      refine ⟨1559246240199891604460819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4157989973866377611895517 1559246240199891604460819)
      ·
        refine ⟨2338869360299837406691229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1559246240199891604460819 2338869360299837406691229)
        ·
          refine ⟨877076010112439027509211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2338869360299837406691229 877076010112439027509211)
          ·
            refine ⟨1315614015168658541263817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 877076010112439027509211 1315614015168658541263817)
            ·
              refine ⟨986710511376493905947863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1315614015168658541263817 986710511376493905947863)
              ·
                refine ⟨1480065767064740858921795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 986710511376493905947863 1480065767064740858921795)
                ·
                  refine ⟨2220098650597111288382693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1480065767064740858921795 2220098650597111288382693)
                  ·
                    refine ⟨416268496986958366571755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2220098650597111288382693 416268496986958366571755)
                    ·
                      rfl

theorem cell22_1216020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 2, 1, 1, 4].length) (baseStart_1216020 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1216020 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1216020 prefixEnd_1216020 := by exact prefixLift 1216020
  have htrace : WordTrace (prefixWord ++ tailWord_1216020) baseStart_1216020 baseEnd_1216020 := by
    simpa [prefixWord, tailWord_1216020, baseEnd_1216020] using wordTrace_append hprefix tailTrace_1216020
  have hstable : (prefixWord ++ tailWord_1216020).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1216020).length < 2 ^ (prefixWord ++ tailWord_1216020).sum := by decide
  have hdescent : baseEnd_1216020 < baseStart_1216020 := by decide
  rcases family_descends (prefixWord ++ tailWord_1216020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1216151 : List Nat := [1, 1, 3, 3, 2, 3, 2, 2, 2, 3]
def baseStart_1216151 : Nat := 118140960795 + 1216151 * 2 ^ 59
def prefixEnd_1216151 : Nat := 4983230072969 + 3 ^ 40 * 1216151 * 2
def baseEnd_1216151 : Nat := 416313340964117691546353

theorem tailTrace_1216151 : CollatzResearch.WordTrace tailWord_1216151 prefixEnd_1216151 416313340964117691546353 := by
  unfold tailWord_1216151
  simp only [CollatzResearch.WordTrace]
  refine ⟨44356671017100103899904307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29571114011400069266602871 44356671017100103899904307)
  ·
    refine ⟨66535006525650155849856461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44356671017100103899904307 66535006525650155849856461)
    ·
      refine ⟨24950627447118808443696173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66535006525650155849856461 24950627447118808443696173)
      ·
        refine ⟨9356485292669553166386065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24950627447118808443696173 9356485292669553166386065)
        ·
          refine ⟨7017363969502164874789549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9356485292669553166386065 7017363969502164874789549)
          ·
            refine ⟨2631511488563311828046081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7017363969502164874789549 2631511488563311828046081)
            ·
              refine ⟨1973633616422483871034561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2631511488563311828046081 1973633616422483871034561)
              ·
                refine ⟨1480225212316862903275921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1973633616422483871034561 1480225212316862903275921)
                ·
                  refine ⟨1110168909237647177456941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1480225212316862903275921 1110168909237647177456941)
                  ·
                    refine ⟨416313340964117691546353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1110168909237647177456941 416313340964117691546353)
                    ·
                      rfl

theorem cell22_1216151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 2, 2, 2, 3].length) (baseStart_1216151 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1216151 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1216151 prefixEnd_1216151 := by exact prefixLift 1216151
  have htrace : WordTrace (prefixWord ++ tailWord_1216151) baseStart_1216151 baseEnd_1216151 := by
    simpa [prefixWord, tailWord_1216151, baseEnd_1216151] using wordTrace_append hprefix tailTrace_1216151
  have hstable : (prefixWord ++ tailWord_1216151).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1216151).length < 2 ^ (prefixWord ++ tailWord_1216151).sum := by decide
  have hdescent : baseEnd_1216151 < baseStart_1216151 := by decide
  rcases family_descends (prefixWord ++ tailWord_1216151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1216164 : List Nat := [2, 3, 1, 2, 2, 4, 1, 7]
def baseStart_1216164 : Nat := 118140960795 + 1216164 * 2 ^ 59
def prefixEnd_1216164 : Nat := 4983230072969 + 3 ^ 40 * 1216164 * 2
def baseEnd_1216164 : Nat := 46257532347754443441257

theorem tailTrace_1216164 : CollatzResearch.WordTrace tailWord_1216164 prefixEnd_1216164 46257532347754443441257 := by
  unfold tailWord_1216164
  simp only [CollatzResearch.WordTrace]
  refine ⟨22178572583026503560063773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29571430110702004746751697 22178572583026503560063773)
  ·
    refine ⟨8316964718634938835023915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22178572583026503560063773 8316964718634938835023915)
    ·
      refine ⟨12475447077952408252535873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8316964718634938835023915 12475447077952408252535873)
      ·
        refine ⟨9356585308464306189401905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12475447077952408252535873 9356585308464306189401905)
        ·
          refine ⟨7017438981348229642051429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9356585308464306189401905 7017438981348229642051429)
          ·
            refine ⟨1315769809002793057884643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7017438981348229642051429 1315769809002793057884643)
            ·
              refine ⟨1973654713504189586826965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1315769809002793057884643 1973654713504189586826965)
              ·
                refine ⟨46257532347754443441257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1973654713504189586826965 46257532347754443441257)
                ·
                  rfl

theorem cell22_1216164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 1, 7].length) (baseStart_1216164 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1216164 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1216164 prefixEnd_1216164 := by exact prefixLift 1216164
  have htrace : WordTrace (prefixWord ++ tailWord_1216164) baseStart_1216164 baseEnd_1216164 := by
    simpa [prefixWord, tailWord_1216164, baseEnd_1216164] using wordTrace_append hprefix tailTrace_1216164
  have hstable : (prefixWord ++ tailWord_1216164).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1216164).length < 2 ^ (prefixWord ++ tailWord_1216164).sum := by decide
  have hdescent : baseEnd_1216164 < baseStart_1216164 := by decide
  rcases family_descends (prefixWord ++ tailWord_1216164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1216179 : List Nat := [1, 1, 1, 2, 3, 3, 3, 2, 3, 3]
def baseStart_1216179 : Nat := 118140960795 + 1216179 * 2 ^ 59
def prefixEnd_1216179 : Nat := 4983230072969 + 3 ^ 40 * 1216179 * 2
def baseEnd_1216179 : Nat := 416322925936334951846267

theorem tailTrace_1216179 : CollatzResearch.WordTrace tailWord_1216179 prefixEnd_1216179 416322925936334951846267 := by
  unfold tailWord_1216179
  simp only [CollatzResearch.WordTrace]
  refine ⟨44357692260998664681923591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29571794840665776454615727 44357692260998664681923591)
  ·
    refine ⟨66536538391497997022885387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44357692260998664681923591 66536538391497997022885387)
    ·
      refine ⟨99804807587246995534328081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66536538391497997022885387 99804807587246995534328081)
      ·
        refine ⟨74853605690435246650746061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99804807587246995534328081 74853605690435246650746061)
        ·
          refine ⟨28070102133913217494029773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74853605690435246650746061 28070102133913217494029773)
          ·
            refine ⟨10526288300217456560261165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28070102133913217494029773 10526288300217456560261165)
            ·
              refine ⟨3947358112581546210097937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10526288300217456560261165 3947358112581546210097937)
              ·
                refine ⟨2960518584436159657573453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3947358112581546210097937 2960518584436159657573453)
                ·
                  refine ⟨1110194469163559871590045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2960518584436159657573453 1110194469163559871590045)
                  ·
                    refine ⟨416322925936334951846267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1110194469163559871590045 416322925936334951846267)
                    ·
                      rfl

theorem cell22_1216179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3, 2, 3, 3].length) (baseStart_1216179 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1216179 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1216179 prefixEnd_1216179 := by exact prefixLift 1216179
  have htrace : WordTrace (prefixWord ++ tailWord_1216179) baseStart_1216179 baseEnd_1216179 := by
    simpa [prefixWord, tailWord_1216179, baseEnd_1216179] using wordTrace_append hprefix tailTrace_1216179
  have hstable : (prefixWord ++ tailWord_1216179).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1216179).length < 2 ^ (prefixWord ++ tailWord_1216179).sum := by decide
  have hdescent : baseEnd_1216179 < baseStart_1216179 := by decide
  rcases family_descends (prefixWord ++ tailWord_1216179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1216181 : List Nat := [1, 3, 3, 3, 2, 1, 3, 6]
def baseStart_1216181 : Nat := 118140960795 + 1216181 * 2 ^ 59
def prefixEnd_1216181 : Nat := 4983230072969 + 3 ^ 40 * 1216181 * 2
def baseEnd_1216181 : Nat := 46258178953023068144029

theorem tailTrace_1216181 : CollatzResearch.WordTrace tailWord_1216181 prefixEnd_1216181 46258178953023068144029 := by
  unfold tailWord_1216181
  simp only [CollatzResearch.WordTrace]
  refine ⟨44357765206991419023496397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29571843471327612682330931 44357765206991419023496397)
  ·
    refine ⟨16634161952621782133811149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44357765206991419023496397 16634161952621782133811149)
    ·
      refine ⟨6237810732233168300179181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16634161952621782133811149 6237810732233168300179181)
      ·
        refine ⟨2339179024587438112567193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6237810732233168300179181 2339179024587438112567193)
        ·
          refine ⟨1754384268440578584425395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2339179024587438112567193 1754384268440578584425395)
          ·
            refine ⟨2631576402660867876638093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1754384268440578584425395 2631576402660867876638093)
            ·
              refine ⟨986841150997825453739285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2631576402660867876638093 986841150997825453739285)
              ·
                refine ⟨46258178953023068144029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 986841150997825453739285 46258178953023068144029)
                ·
                  rfl

theorem cell22_1216181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 3, 6].length) (baseStart_1216181 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1216181 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1216181 prefixEnd_1216181 := by exact prefixLift 1216181
  have htrace : WordTrace (prefixWord ++ tailWord_1216181) baseStart_1216181 baseEnd_1216181 := by
    simpa [prefixWord, tailWord_1216181, baseEnd_1216181] using wordTrace_append hprefix tailTrace_1216181
  have hstable : (prefixWord ++ tailWord_1216181).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1216181).length < 2 ^ (prefixWord ++ tailWord_1216181).sum := by decide
  have hdescent : baseEnd_1216181 < baseStart_1216181 := by decide
  rcases family_descends (prefixWord ++ tailWord_1216181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1216192 : List Nat := [2, 1, 1, 2, 4, 1, 2, 2, 7]
def baseStart_1216192 : Nat := 118140960795 + 1216192 * 2 ^ 59
def prefixEnd_1216192 : Nat := 4983230072969 + 3 ^ 40 * 1216192 * 2
def baseEnd_1216192 : Nat := 138775792034002417090409

theorem tailTrace_1216192 : CollatzResearch.WordTrace tailWord_1216192 prefixEnd_1216192 138775792034002417090409 := by
  unfold tailWord_1216192
  simp only [CollatzResearch.WordTrace]
  refine ⟨22179083204975783951073415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29572110939967711934764553 22179083204975783951073415)
  ·
    refine ⟨33268624807463675926610123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22179083204975783951073415 33268624807463675926610123)
    ·
      refine ⟨49902937211195513889915185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33268624807463675926610123 49902937211195513889915185)
      ·
        refine ⟨37427202908396635417436389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49902937211195513889915185 37427202908396635417436389)
        ·
          refine ⟨7017600545324369140769323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37427202908396635417436389 7017600545324369140769323)
          ·
            refine ⟨10526400817986553711153985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7017600545324369140769323 10526400817986553711153985)
            ·
              refine ⟨7894800613489915283365489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10526400817986553711153985 7894800613489915283365489)
              ·
                refine ⟨5921100460117436462524117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7894800613489915283365489 5921100460117436462524117)
                ·
                  refine ⟨138775792034002417090409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5921100460117436462524117 138775792034002417090409)
                  ·
                    rfl

theorem cell22_1216192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 2, 7].length) (baseStart_1216192 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1216192 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1216192 prefixEnd_1216192 := by exact prefixLift 1216192
  have htrace : WordTrace (prefixWord ++ tailWord_1216192) baseStart_1216192 baseEnd_1216192 := by
    simpa [prefixWord, tailWord_1216192, baseEnd_1216192] using wordTrace_append hprefix tailTrace_1216192
  have hstable : (prefixWord ++ tailWord_1216192).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1216192).length < 2 ^ (prefixWord ++ tailWord_1216192).sum := by decide
  have hdescent : baseEnd_1216192 < baseStart_1216192 := by decide
  rcases family_descends (prefixWord ++ tailWord_1216192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1216209 : List Nat := [1, 2, 2, 1, 2, 4, 3, 2, 5]
def baseStart_1216209 : Nat := 118140960795 + 1216209 * 2 ^ 59
def prefixEnd_1216209 : Nat := 4983230072969 + 3 ^ 40 * 1216209 * 2
def baseEnd_1216209 : Nat := 138777731849808291198725

theorem tailTrace_1216209 : CollatzResearch.WordTrace tailWord_1216209 prefixEnd_1216209 138777731849808291198725 := by
  unfold tailWord_1216209
  simp only [CollatzResearch.WordTrace]
  refine ⟨44358786450889979805515681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29572524300593319870343787 44358786450889979805515681)
  ·
    refine ⟨33269089838167484854136761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44358786450889979805515681 33269089838167484854136761)
    ·
      refine ⟨24951817378625613640602571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33269089838167484854136761 24951817378625613640602571)
      ·
        refine ⟨37427726067938420460903857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24951817378625613640602571 37427726067938420460903857)
        ·
          refine ⟨28070794550953815345677893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37427726067938420460903857 28070794550953815345677893)
          ·
            refine ⟨5263273978303840377314605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28070794550953815345677893 5263273978303840377314605)
            ·
              refine ⟨1973727741863940141492977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5263273978303840377314605 1973727741863940141492977)
              ·
                refine ⟨1480295806397955106119733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1973727741863940141492977 1480295806397955106119733)
                ·
                  refine ⟨138777731849808291198725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1480295806397955106119733 138777731849808291198725)
                  ·
                    rfl

theorem cell22_1216209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 3, 2, 5].length) (baseStart_1216209 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1216209 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1216209 prefixEnd_1216209 := by exact prefixLift 1216209
  have htrace : WordTrace (prefixWord ++ tailWord_1216209) baseStart_1216209 baseEnd_1216209 := by
    simpa [prefixWord, tailWord_1216209, baseEnd_1216209] using wordTrace_append hprefix tailTrace_1216209
  have hstable : (prefixWord ++ tailWord_1216209).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1216209).length < 2 ^ (prefixWord ++ tailWord_1216209).sum := by decide
  have hdescent : baseEnd_1216209 < baseStart_1216209 := by decide
  rcases family_descends (prefixWord ++ tailWord_1216209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1216284 : List Nat := [2, 2, 3, 1, 1, 2, 1, 2, 4, 4]
def baseStart_1216284 : Nat := 118140960795 + 1216284 * 2 ^ 59
def prefixEnd_1216284 : Nat := 4983230072969 + 3 ^ 40 * 1216284 * 2
def baseEnd_1216284 : Nat := 416358869582149677970945

theorem tailTrace_1216284 : CollatzResearch.WordTrace tailWord_1216284 prefixEnd_1216284 416358869582149677970945 := by
  unfold tailWord_1216284
  simp only [CollatzResearch.WordTrace]
  refine ⟨22180760962809133807247953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29574347950412178409663937 22180760962809133807247953)
  ·
    refine ⟨16635570722106850355435965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22180760962809133807247953 16635570722106850355435965)
    ·
      refine ⟨6238339020790068883288487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16635570722106850355435965 6238339020790068883288487)
      ·
        refine ⟨9357508531185103324932731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6238339020790068883288487 9357508531185103324932731)
        ·
          refine ⟨14036262796777654987399097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9357508531185103324932731 14036262796777654987399097)
          ·
            refine ⟨10527197097583241240549323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14036262796777654987399097 10527197097583241240549323)
            ·
              refine ⟨15790795646374861860823985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10527197097583241240549323 15790795646374861860823985)
              ·
                refine ⟨11843096734781146395617989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15790795646374861860823985 11843096734781146395617989)
                ·
                  refine ⟨2220580637771464949178373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11843096734781146395617989 2220580637771464949178373)
                  ·
                    refine ⟨416358869582149677970945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2220580637771464949178373 416358869582149677970945)
                    ·
                      rfl

theorem cell22_1216284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 2, 4, 4].length) (baseStart_1216284 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1216284 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1216284 prefixEnd_1216284 := by exact prefixLift 1216284
  have htrace : WordTrace (prefixWord ++ tailWord_1216284) baseStart_1216284 baseEnd_1216284 := by
    simpa [prefixWord, tailWord_1216284, baseEnd_1216284] using wordTrace_append hprefix tailTrace_1216284
  have hstable : (prefixWord ++ tailWord_1216284).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1216284).length < 2 ^ (prefixWord ++ tailWord_1216284).sum := by decide
  have hdescent : baseEnd_1216284 < baseStart_1216284 := by decide
  rcases family_descends (prefixWord ++ tailWord_1216284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1216333 : List Nat := [1, 6, 1, 2, 1, 3, 1, 7]
def baseStart_1216333 : Nat := 118140960795 + 1216333 * 2 ^ 59
def prefixEnd_1216333 : Nat := 4983230072969 + 3 ^ 40 * 1216333 * 2
def baseEnd_1216333 : Nat := 46263960364836653721755

theorem tailTrace_1216333 : CollatzResearch.WordTrace tailWord_1216333 prefixEnd_1216333 46263960364836653721755 := by
  unfold tailWord_1216333
  simp only [CollatzResearch.WordTrace]
  refine ⟨44363309102440748983029653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29575539401627165988686435 44363309102440748983029653)
  ·
    refine ⟨2079530114176910108579515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 44363309102440748983029653 2079530114176910108579515)
    ·
      refine ⟨3119295171265365162869273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2079530114176910108579515 3119295171265365162869273)
      ·
        refine ⟨2339471378449023872151955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3119295171265365162869273 2339471378449023872151955)
        ·
          refine ⟨3509207067673535808227933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2339471378449023872151955 3509207067673535808227933)
          ·
            refine ⟨1315952650377575928085475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3509207067673535808227933 1315952650377575928085475)
            ·
              refine ⟨1973928975566363892128213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1315952650377575928085475 1973928975566363892128213)
              ·
                refine ⟨46263960364836653721755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1973928975566363892128213 46263960364836653721755)
                ·
                  rfl

theorem cell22_1216333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 1, 7].length) (baseStart_1216333 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1216333 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1216333 prefixEnd_1216333 := by exact prefixLift 1216333
  have htrace : WordTrace (prefixWord ++ tailWord_1216333) baseStart_1216333 baseEnd_1216333 := by
    simpa [prefixWord, tailWord_1216333, baseEnd_1216333] using wordTrace_append hprefix tailTrace_1216333
  have hstable : (prefixWord ++ tailWord_1216333).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1216333).length < 2 ^ (prefixWord ++ tailWord_1216333).sum := by decide
  have hdescent : baseEnd_1216333 < baseStart_1216333 := by decide
  rcases family_descends (prefixWord ++ tailWord_1216333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1216359 : List Nat := [1, 1, 5, 1, 2, 1, 1, 2, 1, 7]
def baseStart_1216359 : Nat := 118140960795 + 1216359 * 2 ^ 59
def prefixEnd_1216359 : Nat := 4983230072969 + 3 ^ 40 * 1216359 * 2
def baseEnd_1216359 : Nat := 416384543614874482345715

theorem tailTrace_1216359 : CollatzResearch.WordTrace tailWord_1216359 prefixEnd_1216359 416384543614874482345715 := by
  unfold tailWord_1216359
  simp only [CollatzResearch.WordTrace]
  refine ⟨44364257400346555423476131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29576171600231036948984087 44364257400346555423476131)
  ·
    refine ⟨66546386100519833135214197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44364257400346555423476131 66546386100519833135214197)
    ·
      refine ⟨6238723696923734356426331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 66546386100519833135214197 6238723696923734356426331)
      ·
        refine ⟨9358085545385601534639497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6238723696923734356426331 9358085545385601534639497)
        ·
          refine ⟨7018564159039201150979623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9358085545385601534639497 7018564159039201150979623)
          ·
            refine ⟨10527846238558801726469435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7018564159039201150979623 10527846238558801726469435)
            ·
              refine ⟨15791769357838202589704153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10527846238558801726469435 15791769357838202589704153)
              ·
                refine ⟨11843827018378651942278115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15791769357838202589704153 11843827018378651942278115)
                ·
                  refine ⟨17765740527567977913417173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11843827018378651942278115 17765740527567977913417173)
                  ·
                    refine ⟨416384543614874482345715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17765740527567977913417173 416384543614874482345715)
                    ·
                      rfl

theorem cell22_1216359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 2, 1, 7].length) (baseStart_1216359 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1216359 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1216359 prefixEnd_1216359 := by exact prefixLift 1216359
  have htrace : WordTrace (prefixWord ++ tailWord_1216359) baseStart_1216359 baseEnd_1216359 := by
    simpa [prefixWord, tailWord_1216359, baseEnd_1216359] using wordTrace_append hprefix tailTrace_1216359
  have hstable : (prefixWord ++ tailWord_1216359).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1216359).length < 2 ^ (prefixWord ++ tailWord_1216359).sum := by decide
  have hdescent : baseEnd_1216359 < baseStart_1216359 := by decide
  rcases family_descends (prefixWord ++ tailWord_1216359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1216382 : List Nat := [4, 2, 3, 1, 1, 1, 2, 4, 1, 3]
def baseStart_1216382 : Nat := 118140960795 + 1216382 * 2 ^ 59
def prefixEnd_1216382 : Nat := 4983230072969 + 3 ^ 40 * 1216382 * 2
def baseEnd_1216382 : Nat := 416392416984910089020645

theorem tailTrace_1216382 : CollatzResearch.WordTrace tailWord_1216382 prefixEnd_1216382 416392416984910089020645 := by
  unfold tailWord_1216382
  simp only [CollatzResearch.WordTrace]
  refine ⟨5545637034907903793945425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29576730852842153567708933 5545637034907903793945425)
  ·
    refine ⟨4159227776180927845459069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5545637034907903793945425 4159227776180927845459069)
    ·
      refine ⟨1559710416067847942047151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4159227776180927845459069 1559710416067847942047151)
      ·
        refine ⟨2339565624101771913070727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1559710416067847942047151 2339565624101771913070727)
        ·
          refine ⟨3509348436152657869606091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2339565624101771913070727 3509348436152657869606091)
          ·
            refine ⟨5264022654228986804409137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3509348436152657869606091 5264022654228986804409137)
            ·
              refine ⟨3948016990671740103306853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5264022654228986804409137 3948016990671740103306853)
              ·
                refine ⟨740253185750951269370035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3948016990671740103306853 740253185750951269370035)
                ·
                  refine ⟨1110379778626426904055053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 740253185750951269370035 1110379778626426904055053)
                  ·
                    refine ⟨416392416984910089020645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1110379778626426904055053 416392416984910089020645)
                    ·
                      rfl

theorem cell22_1216382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 2, 4, 1, 3].length) (baseStart_1216382 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1216382 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1216382 prefixEnd_1216382 := by exact prefixLift 1216382
  have htrace : WordTrace (prefixWord ++ tailWord_1216382) baseStart_1216382 baseEnd_1216382 := by
    simpa [prefixWord, tailWord_1216382, baseEnd_1216382] using wordTrace_append hprefix tailTrace_1216382
  have hstable : (prefixWord ++ tailWord_1216382).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1216382).length < 2 ^ (prefixWord ++ tailWord_1216382).sum := by decide
  have hdescent : baseEnd_1216382 < baseStart_1216382 := by decide
  rcases family_descends (prefixWord ++ tailWord_1216382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1216496 : List Nat := [2, 1, 1, 1, 3, 2, 3, 4, 5]
def baseStart_1216496 : Nat := 118140960795 + 1216496 * 2 ^ 59
def prefixEnd_1216496 : Nat := 4983230072969 + 3 ^ 40 * 1216496 * 2
def baseEnd_1216496 : Nat := 138810480504883930556765

theorem tailTrace_1216496 : CollatzResearch.WordTrace tailWord_1216496 prefixEnd_1216496 138810480504883930556765 := by
  unfold tailWord_1216496
  simp only [CollatzResearch.WordTrace]
  refine ⟨22184627100425113910606671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29579502800566818547475561 22184627100425113910606671)
  ·
    refine ⟨33276940650637670865910007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22184627100425113910606671 33276940650637670865910007)
    ·
      refine ⟨49915410975956506298865011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33276940650637670865910007 49915410975956506298865011)
      ·
        refine ⟨74873116463934759448297517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49915410975956506298865011 74873116463934759448297517)
        ·
          refine ⟨28077418673975534793111569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74873116463934759448297517 28077418673975534793111569)
          ·
            refine ⟨21058064005481651094833677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28077418673975534793111569 21058064005481651094833677)
            ·
              refine ⟨7896774002055619160562629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21058064005481651094833677 7896774002055619160562629)
              ·
                refine ⟨1480645125385428592605493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7896774002055619160562629 1480645125385428592605493)
                ·
                  refine ⟨138810480504883930556765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1480645125385428592605493 138810480504883930556765)
                  ·
                    rfl

theorem cell22_1216496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 4, 5].length) (baseStart_1216496 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1216496 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1216496 prefixEnd_1216496 := by exact prefixLift 1216496
  have htrace : WordTrace (prefixWord ++ tailWord_1216496) baseStart_1216496 baseEnd_1216496 := by
    simpa [prefixWord, tailWord_1216496, baseEnd_1216496] using wordTrace_append hprefix tailTrace_1216496
  have hstable : (prefixWord ++ tailWord_1216496).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1216496).length < 2 ^ (prefixWord ++ tailWord_1216496).sum := by decide
  have hdescent : baseEnd_1216496 < baseStart_1216496 := by decide
  rcases family_descends (prefixWord ++ tailWord_1216496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1216543 : List Nat := [1, 1, 2, 4, 1, 2, 3, 3, 1, 4]
def baseStart_1216543 : Nat := 118140960795 + 1216543 * 2 ^ 59
def prefixEnd_1216543 : Nat := 4983230072969 + 3 ^ 40 * 1216543 * 2
def baseEnd_1216543 : Nat := 416447530575159335745151

theorem tailTrace_1216543 : CollatzResearch.WordTrace tailWord_1216543 prefixEnd_1216543 416447530575159335745151 := by
  unfold tailWord_1216543
  simp only [CollatzResearch.WordTrace]
  refine ⟨44370968431679954848174283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29580645621119969898782855 44370968431679954848174283)
  ·
    refine ⟨66556452647519932272261425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44370968431679954848174283 66556452647519932272261425)
    ·
      refine ⟨49917339485639949204196069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66556452647519932272261425 49917339485639949204196069)
      ·
        refine ⟨9359501153557490475786763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49917339485639949204196069 9359501153557490475786763)
        ·
          refine ⟨14039251730336235713680145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9359501153557490475786763 14039251730336235713680145)
          ·
            refine ⟨10529438797752176785260109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14039251730336235713680145 10529438797752176785260109)
            ·
              refine ⟨3948539549157066294472541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10529438797752176785260109 3948539549157066294472541)
              ·
                refine ⟨1480702330933899860427203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3948539549157066294472541 1480702330933899860427203)
                ·
                  refine ⟨2221053496400849790640805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1480702330933899860427203 2221053496400849790640805)
                  ·
                    refine ⟨416447530575159335745151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2221053496400849790640805 416447530575159335745151)
                    ·
                      rfl

theorem cell22_1216543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3, 3, 1, 4].length) (baseStart_1216543 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1216543 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1216543 prefixEnd_1216543 := by exact prefixLift 1216543
  have htrace : WordTrace (prefixWord ++ tailWord_1216543) baseStart_1216543 baseEnd_1216543 := by
    simpa [prefixWord, tailWord_1216543, baseEnd_1216543] using wordTrace_append hprefix tailTrace_1216543
  have hstable : (prefixWord ++ tailWord_1216543).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1216543).length < 2 ^ (prefixWord ++ tailWord_1216543).sum := by decide
  have hdescent : baseEnd_1216543 < baseStart_1216543 := by decide
  rcases family_descends (prefixWord ++ tailWord_1216543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
