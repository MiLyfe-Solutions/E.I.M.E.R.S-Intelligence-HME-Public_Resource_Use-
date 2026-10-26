import V185TrunkScan23Chunk1017

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6027011 : List Nat := [1, 1, 1, 3, 2, 2, 3, 1, 5, 2, 2]
def baseStart_6027011 : Nat := 118140960795 + 6027011 * 2 ^ 59
def prefixEnd_6027011 : Nat := 4983230072969 + 3 ^ 40 * 6027011 * 2
def baseEnd_6027011 : Nat := 3094753552935224025444787

theorem tailTrace_6027011 : CollatzResearch.WordTrace tailWord_6027011 prefixEnd_6027011 3094753552935224025444787 := by
  unfold tailWord_6027011
  simp only [CollatzResearch.WordTrace]
  refine ⟨219823150368175953374640887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146548766912117302249760591 219823150368175953374640887)
  ·
    refine ⟨329734725552263930061961331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219823150368175953374640887 329734725552263930061961331)
    ·
      refine ⟨494602088328395895092941997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 329734725552263930061961331 494602088328395895092941997)
      ·
        refine ⟨185475783123148460659853249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 494602088328395895092941997 185475783123148460659853249)
        ·
          refine ⟨139106837342361345494889937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 185475783123148460659853249 139106837342361345494889937)
          ·
            refine ⟨104330128006771009121167453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 139106837342361345494889937 104330128006771009121167453)
            ·
              refine ⟨39123798002539128420437795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 104330128006771009121167453 39123798002539128420437795)
              ·
                refine ⟨58685697003808692630656693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39123798002539128420437795 58685697003808692630656693)
                ·
                  refine ⟨5501784094107064934124065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 58685697003808692630656693 5501784094107064934124065)
                  ·
                    refine ⟨4126338070580298700593049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5501784094107064934124065 4126338070580298700593049)
                    ·
                      refine ⟨3094753552935224025444787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4126338070580298700593049 3094753552935224025444787)
                      ·
                        rfl

theorem cell23_6027011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 1, 5, 2, 2].length) (baseStart_6027011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6027011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6027011 prefixEnd_6027011 := by exact prefixLift 6027011
  have htrace : WordTrace (prefixWord ++ tailWord_6027011) baseStart_6027011 baseEnd_6027011 := by
    simpa [prefixWord, tailWord_6027011, baseEnd_6027011] using wordTrace_append hprefix tailTrace_6027011
  have hstable : (prefixWord ++ tailWord_6027011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6027011).length < 2 ^ (prefixWord ++ tailWord_6027011).sum := by decide
  have hdescent : baseEnd_6027011 < baseStart_6027011 := by decide
  rcases family_descends (prefixWord ++ tailWord_6027011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6027015 : List Nat := [1, 1, 4, 4, 2, 2, 1, 1, 2, 3, 2]
def baseStart_6027015 : Nat := 118140960795 + 6027015 * 2 ^ 59
def prefixEnd_6027015 : Nat := 4983230072969 + 3 ^ 40 * 6027015 * 2
def baseEnd_6027015 : Nat := 3094755606857842009794769

theorem tailTrace_6027015 : CollatzResearch.WordTrace tailWord_6027015 prefixEnd_6027015 3094755606857842009794769 := by
  unfold tailWord_6027015
  simp only [CollatzResearch.WordTrace]
  refine ⟨219823296260161462057786499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146548864173440974705190999 219823296260161462057786499)
  ·
    refine ⟨329734944390242193086679749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219823296260161462057786499 329734944390242193086679749)
    ·
      refine ⟨61825302073170411203752453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 329734944390242193086679749 61825302073170411203752453)
      ·
        refine ⟨11592244138719452100703585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61825302073170411203752453 11592244138719452100703585)
        ·
          refine ⟨8694183104039589075527689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11592244138719452100703585 8694183104039589075527689)
          ·
            refine ⟨6520637328029691806645767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8694183104039589075527689 6520637328029691806645767)
            ·
              refine ⟨9780955992044537709968651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6520637328029691806645767 9780955992044537709968651)
              ·
                refine ⟨14671433988066806564952977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9780955992044537709968651 14671433988066806564952977)
                ·
                  refine ⟨11003575491050104923714733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14671433988066806564952977 11003575491050104923714733)
                  ·
                    refine ⟨4126340809143789346393025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11003575491050104923714733 4126340809143789346393025)
                    ·
                      refine ⟨3094755606857842009794769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4126340809143789346393025 3094755606857842009794769)
                      ·
                        rfl

theorem cell23_6027015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 1, 1, 2, 3, 2].length) (baseStart_6027015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6027015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6027015 prefixEnd_6027015 := by exact prefixLift 6027015
  have htrace : WordTrace (prefixWord ++ tailWord_6027015) baseStart_6027015 baseEnd_6027015 := by
    simpa [prefixWord, tailWord_6027015, baseEnd_6027015] using wordTrace_append hprefix tailTrace_6027015
  have hstable : (prefixWord ++ tailWord_6027015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6027015).length < 2 ^ (prefixWord ++ tailWord_6027015).sum := by decide
  have hdescent : baseEnd_6027015 < baseStart_6027015 := by decide
  rcases family_descends (prefixWord ++ tailWord_6027015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6027045 : List Nat := [1, 3, 1, 2, 3, 2, 2, 4, 1, 2, 2]
def baseStart_6027045 : Nat := 118140960795 + 6027045 * 2 ^ 59
def prefixEnd_6027045 : Nat := 4983230072969 + 3 ^ 40 * 6027045 * 2
def baseEnd_6027045 : Nat := 3094771011277476892419631

theorem tailTrace_6027045 : CollatzResearch.WordTrace tailWord_6027045 prefixEnd_6027045 3094771011277476892419631 := by
  unfold tailWord_6027045
  simp only [CollatzResearch.WordTrace]
  refine ⟨219824390450052777181378589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146549593633368518120919059 219824390450052777181378589)
  ·
    refine ⟨82434146418769791443016971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 219824390450052777181378589 82434146418769791443016971)
    ·
      refine ⟨123651219628154687164525457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82434146418769791443016971 123651219628154687164525457)
      ·
        refine ⟨92738414721116015373394093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123651219628154687164525457 92738414721116015373394093)
        ·
          refine ⟨34776905520418505765022785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92738414721116015373394093 34776905520418505765022785)
          ·
            refine ⟨26082679140313879323767089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34776905520418505765022785 26082679140313879323767089)
            ·
              refine ⟨19562009355235409492825317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26082679140313879323767089 19562009355235409492825317)
              ·
                refine ⟨3667876754106639279904747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19562009355235409492825317 3667876754106639279904747)
                ·
                  refine ⟨5501815131159958919857121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3667876754106639279904747 5501815131159958919857121)
                  ·
                    refine ⟨4126361348369969189892841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5501815131159958919857121 4126361348369969189892841)
                    ·
                      refine ⟨3094771011277476892419631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4126361348369969189892841 3094771011277476892419631)
                      ·
                        rfl

theorem cell23_6027045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 2, 4, 1, 2, 2].length) (baseStart_6027045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6027045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6027045 prefixEnd_6027045 := by exact prefixLift 6027045
  have htrace : WordTrace (prefixWord ++ tailWord_6027045) baseStart_6027045 baseEnd_6027045 := by
    simpa [prefixWord, tailWord_6027045, baseEnd_6027045] using wordTrace_append hprefix tailTrace_6027045
  have hstable : (prefixWord ++ tailWord_6027045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6027045).length < 2 ^ (prefixWord ++ tailWord_6027045).sum := by decide
  have hdescent : baseEnd_6027045 < baseStart_6027045 := by decide
  rcases family_descends (prefixWord ++ tailWord_6027045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6027065 : List Nat := [1, 2, 1, 7, 1, 1, 2, 2, 1, 2, 3]
def baseStart_6027065 : Nat := 118140960795 + 6027065 * 2 ^ 59
def prefixEnd_6027065 : Nat := 4983230072969 + 3 ^ 40 * 6027065 * 2
def baseEnd_6027065 : Nat := 3094781280890566814169539

theorem tailTrace_6027065 : CollatzResearch.WordTrace tailWord_6027065 prefixEnd_6027065 3094781280890566814169539 := by
  unfold tailWord_6027065
  simp only [CollatzResearch.WordTrace]
  refine ⟨219825119909980320597106649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146550079939986880398071099 219825119909980320597106649)
  ·
    refine ⟨164868839932485240447829987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219825119909980320597106649 164868839932485240447829987)
    ·
      refine ⟨247303259898727860671744981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164868839932485240447829987 247303259898727860671744981)
      ·
        refine ⟨5796170153876434234494023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 247303259898727860671744981 5796170153876434234494023)
        ·
          refine ⟨8694255230814651351741035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5796170153876434234494023 8694255230814651351741035)
          ·
            refine ⟨13041382846221977027611553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8694255230814651351741035 13041382846221977027611553)
            ·
              refine ⟨9781037134666482770708665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13041382846221977027611553 9781037134666482770708665)
              ·
                refine ⟨7335777850999862078031499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9781037134666482770708665 7335777850999862078031499)
                ·
                  refine ⟨11003666776499793117047249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7335777850999862078031499 11003666776499793117047249)
                  ·
                    refine ⟨8252750082374844837785437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11003666776499793117047249 8252750082374844837785437)
                    ·
                      refine ⟨3094781280890566814169539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8252750082374844837785437 3094781280890566814169539)
                      ·
                        rfl

theorem cell23_6027065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 2, 2, 1, 2, 3].length) (baseStart_6027065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6027065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6027065 prefixEnd_6027065 := by exact prefixLift 6027065
  have htrace : WordTrace (prefixWord ++ tailWord_6027065) baseStart_6027065 baseEnd_6027065 := by
    simpa [prefixWord, tailWord_6027065, baseEnd_6027065] using wordTrace_append hprefix tailTrace_6027065
  have hstable : (prefixWord ++ tailWord_6027065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6027065).length < 2 ^ (prefixWord ++ tailWord_6027065).sum := by decide
  have hdescent : baseEnd_6027065 < baseStart_6027065 := by decide
  rcases family_descends (prefixWord ++ tailWord_6027065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6027141 : List Nat := [1, 3, 1, 1, 3, 2, 2, 5, 5]
def baseStart_6027141 : Nat := 118140960795 + 6027141 * 2 ^ 59
def prefixEnd_6027141 : Nat := 4983230072969 + 3 ^ 40 * 6027141 * 2
def baseEnd_6027141 : Nat := 343868922824478724091021

theorem tailTrace_6027141 : CollatzResearch.WordTrace tailWord_6027141 prefixEnd_6027141 343868922824478724091021 := by
  unfold tailWord_6027141
  simp only [CollatzResearch.WordTrace]
  refine ⟨219827891857704985576873277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146551927905136657051248851 219827891857704985576873277)
  ·
    refine ⟨82435459446639369591327479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 219827891857704985576873277 82435459446639369591327479)
    ·
      refine ⟨123653189169959054386991219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82435459446639369591327479 123653189169959054386991219)
      ·
        refine ⟨185479783754938581580486829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123653189169959054386991219 185479783754938581580486829)
        ·
          refine ⟨69554918908101968092682561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 185479783754938581580486829 69554918908101968092682561)
          ·
            refine ⟨52166189181076476069511921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69554918908101968092682561 52166189181076476069511921)
            ·
              refine ⟨39124641885807357052133941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52166189181076476069511921 39124641885807357052133941)
              ·
                refine ⟨3667935176794439723637557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39124641885807357052133941 3667935176794439723637557)
                ·
                  refine ⟨343868922824478724091021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3667935176794439723637557 343868922824478724091021)
                  ·
                    rfl

theorem cell23_6027141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 5, 5].length) (baseStart_6027141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6027141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6027141 prefixEnd_6027141 := by exact prefixLift 6027141
  have htrace : WordTrace (prefixWord ++ tailWord_6027141) baseStart_6027141 baseEnd_6027141 := by
    simpa [prefixWord, tailWord_6027141, baseEnd_6027141] using wordTrace_append hprefix tailTrace_6027141
  have hstable : (prefixWord ++ tailWord_6027141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6027141).length < 2 ^ (prefixWord ++ tailWord_6027141).sum := by decide
  have hdescent : baseEnd_6027141 < baseStart_6027141 := by decide
  rcases family_descends (prefixWord ++ tailWord_6027141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6027161 : List Nat := [1, 2, 1, 2, 1, 3, 3, 1, 2, 5, 2]
def baseStart_6027161 : Nat := 118140960795 + 6027161 * 2 ^ 59
def prefixEnd_6027161 : Nat := 4983230072969 + 3 ^ 40 * 6027161 * 2
def baseEnd_6027161 : Nat := 3094830575033398438569097

theorem tailTrace_6027161 : CollatzResearch.WordTrace tailWord_6027161 prefixEnd_6027161 3094830575033398438569097 := by
  unfold tailWord_6027161
  simp only [CollatzResearch.WordTrace]
  refine ⟨219828621317632528992601337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146552414211755019328400891 219828621317632528992601337)
  ·
    refine ⟨164871465988224396744451003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219828621317632528992601337 164871465988224396744451003)
    ·
      refine ⟨247307198982336595116676505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164871465988224396744451003 247307198982336595116676505)
      ·
        refine ⟨185480399236752446337507379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 247307198982336595116676505 185480399236752446337507379)
        ·
          refine ⟨278220598855128669506261069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185480399236752446337507379 278220598855128669506261069)
          ·
            refine ⟨104332724570673251064847901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 278220598855128669506261069 104332724570673251064847901)
            ·
              refine ⟨39124771714002469149317963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 104332724570673251064847901 39124771714002469149317963)
              ·
                refine ⟨58687157571003703723976945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39124771714002469149317963 58687157571003703723976945)
                ·
                  refine ⟨44015368178252777792982709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58687157571003703723976945 44015368178252777792982709)
                  ·
                    refine ⟨4126440766711197918092129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 44015368178252777792982709 4126440766711197918092129)
                    ·
                      refine ⟨3094830575033398438569097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4126440766711197918092129 3094830575033398438569097)
                      ·
                        rfl

theorem cell23_6027161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 1, 2, 5, 2].length) (baseStart_6027161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6027161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6027161 prefixEnd_6027161 := by exact prefixLift 6027161
  have htrace : WordTrace (prefixWord ++ tailWord_6027161) baseStart_6027161 baseEnd_6027161 := by
    simpa [prefixWord, tailWord_6027161, baseEnd_6027161] using wordTrace_append hprefix tailTrace_6027161
  have hstable : (prefixWord ++ tailWord_6027161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6027161).length < 2 ^ (prefixWord ++ tailWord_6027161).sum := by decide
  have hdescent : baseEnd_6027161 < baseStart_6027161 := by decide
  rcases family_descends (prefixWord ++ tailWord_6027161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6027191 : List Nat := [1, 1, 3, 1, 3, 1, 1, 1, 3, 6, 2]
def baseStart_6027191 : Nat := 118140960795 + 6027191 * 2 ^ 59
def prefixEnd_6027191 : Nat := 4983230072969 + 3 ^ 40 * 6027191 * 2
def baseEnd_6027191 : Nat := 3094845979453033321193959

theorem tailTrace_6027191 : CollatzResearch.WordTrace tailWord_6027191 prefixEnd_6027191 3094845979453033321193959 := by
  unfold tailWord_6027191
  simp only [CollatzResearch.WordTrace]
  refine ⟨219829715507523844116193427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146553143671682562744128951 219829715507523844116193427)
  ·
    refine ⟨329744573261285766174290141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219829715507523844116193427 329744573261285766174290141)
    ·
      refine ⟨123654214972982162315358803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 329744573261285766174290141 123654214972982162315358803)
      ·
        refine ⟨185481322459473243473038205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123654214972982162315358803 185481322459473243473038205)
        ·
          refine ⟨69555495922302466302389327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 185481322459473243473038205 69555495922302466302389327)
          ·
            refine ⟨104333243883453699453583991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69555495922302466302389327 104333243883453699453583991)
            ·
              refine ⟨156499865825180549180375987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104333243883453699453583991 156499865825180549180375987)
              ·
                refine ⟨234749798737770823770563981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 156499865825180549180375987 234749798737770823770563981)
                ·
                  refine ⟨88031174526664058913961493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 234749798737770823770563981 88031174526664058913961493)
                  ·
                    refine ⟨4126461305937377761591945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 88031174526664058913961493 4126461305937377761591945)
                    ·
                      refine ⟨3094845979453033321193959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4126461305937377761591945 3094845979453033321193959)
                      ·
                        rfl

theorem cell23_6027191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 1, 3, 6, 2].length) (baseStart_6027191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6027191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6027191 prefixEnd_6027191 := by exact prefixLift 6027191
  have htrace : WordTrace (prefixWord ++ tailWord_6027191) baseStart_6027191 baseEnd_6027191 := by
    simpa [prefixWord, tailWord_6027191, baseEnd_6027191] using wordTrace_append hprefix tailTrace_6027191
  have hstable : (prefixWord ++ tailWord_6027191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6027191).length < 2 ^ (prefixWord ++ tailWord_6027191).sum := by decide
  have hdescent : baseEnd_6027191 < baseStart_6027191 := by decide
  rcases family_descends (prefixWord ++ tailWord_6027191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6027194 : List Nat := [3, 1, 1, 1, 2, 1, 2, 2, 2, 3, 5]
def baseStart_6027194 : Nat := 118140960795 + 6027194 * 2 ^ 59
def prefixEnd_6027194 : Nat := 4983230072969 + 3 ^ 40 * 6027194 * 2
def baseEnd_6027194 : Nat := 3094847519894996809456445

theorem tailTrace_6027194 : CollatzResearch.WordTrace tailWord_6027194 prefixEnd_6027194 3094847519894996809456445 := by
  unfold tailWord_6027194
  simp only [CollatzResearch.WordTrace]
  refine ⟨54957456231628243907138159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146553216617675317085701757 54957456231628243907138159)
  ·
    refine ⟨82436184347442365860707239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54957456231628243907138159 82436184347442365860707239)
    ·
      refine ⟨123654276521163548791060859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82436184347442365860707239 123654276521163548791060859)
      ·
        refine ⟨185481414781745323186591289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123654276521163548791060859 185481414781745323186591289)
        ·
          refine ⟨139111061086308992389943467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 185481414781745323186591289 139111061086308992389943467)
          ·
            refine ⟨208666591629463488584915201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139111061086308992389943467 208666591629463488584915201)
            ·
              refine ⟨156499943722097616438686401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 208666591629463488584915201 156499943722097616438686401)
              ·
                refine ⟨117374957791573212329014801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 156499943722097616438686401 117374957791573212329014801)
                ·
                  refine ⟨88031218343679909246761101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 117374957791573212329014801 88031218343679909246761101)
                  ·
                    refine ⟨33011706878879965967535413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 88031218343679909246761101 33011706878879965967535413)
                    ·
                      refine ⟨3094847519894996809456445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33011706878879965967535413 3094847519894996809456445)
                      ·
                        rfl

theorem cell23_6027194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 2, 2, 3, 5].length) (baseStart_6027194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6027194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6027194 prefixEnd_6027194 := by exact prefixLift 6027194
  have htrace : WordTrace (prefixWord ++ tailWord_6027194) baseStart_6027194 baseEnd_6027194 := by
    simpa [prefixWord, tailWord_6027194, baseEnd_6027194] using wordTrace_append hprefix tailTrace_6027194
  have hstable : (prefixWord ++ tailWord_6027194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6027194).length < 2 ^ (prefixWord ++ tailWord_6027194).sum := by decide
  have hdescent : baseEnd_6027194 < baseStart_6027194 := by decide
  rcases family_descends (prefixWord ++ tailWord_6027194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6027208 : List Nat := [2, 1, 3, 1, 4, 1, 1, 2, 2, 4, 2]
def baseStart_6027208 : Nat := 118140960795 + 6027208 * 2 ^ 59
def prefixEnd_6027208 : Nat := 4983230072969 + 3 ^ 40 * 6027208 * 2
def baseEnd_6027208 : Nat := 3094854708624159754681381

theorem tailTrace_6027208 : CollatzResearch.WordTrace tailWord_6027208 prefixEnd_6027208 3094854708624159754681381 := by
  unfold tailWord_6027208
  simp only [CollatzResearch.WordTrace]
  refine ⟨109915167774231128009781139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146553557032308170679708185 109915167774231128009781139)
  ·
    refine ⟨164872751661346692014671709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109915167774231128009781139 164872751661346692014671709)
    ·
      refine ⟨61827281873005009505501891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 164872751661346692014671709 61827281873005009505501891)
      ·
        refine ⟨92740922809507514258252837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61827281873005009505501891 92740922809507514258252837)
        ·
          refine ⟨17388923026782658923422407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 92740922809507514258252837 17388923026782658923422407)
          ·
            refine ⟨26083384540173988385133611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17388923026782658923422407 26083384540173988385133611)
            ·
              refine ⟨39125076810260982577700417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26083384540173988385133611 39125076810260982577700417)
              ·
                refine ⟨29343807607695736933275313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39125076810260982577700417 29343807607695736933275313)
                ·
                  refine ⟨22007855705771802699956485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29343807607695736933275313 22007855705771802699956485)
                  ·
                    refine ⟨4126472944832213006241841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22007855705771802699956485 4126472944832213006241841)
                    ·
                      refine ⟨3094854708624159754681381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4126472944832213006241841 3094854708624159754681381)
                      ·
                        rfl

theorem cell23_6027208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 2, 2, 4, 2].length) (baseStart_6027208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6027208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6027208 prefixEnd_6027208 := by exact prefixLift 6027208
  have htrace : WordTrace (prefixWord ++ tailWord_6027208) baseStart_6027208 baseEnd_6027208 := by
    simpa [prefixWord, tailWord_6027208, baseEnd_6027208] using wordTrace_append hprefix tailTrace_6027208
  have hstable : (prefixWord ++ tailWord_6027208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6027208).length < 2 ^ (prefixWord ++ tailWord_6027208).sum := by decide
  have hdescent : baseEnd_6027208 < baseStart_6027208 := by decide
  rcases family_descends (prefixWord ++ tailWord_6027208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6027211 : List Nat := [1, 1, 1, 1, 3, 4, 2, 1, 4, 2, 3]
def baseStart_6027211 : Nat := 118140960795 + 6027211 * 2 ^ 59
def prefixEnd_6027211 : Nat := 4983230072969 + 3 ^ 40 * 6027211 * 2
def baseEnd_6027211 : Nat := 3094856249066123242943867

theorem tailTrace_6027211 : CollatzResearch.WordTrace tailWord_6027211 prefixEnd_6027211 3094856249066123242943867 := by
  unfold tailWord_6027211
  simp only [CollatzResearch.WordTrace]
  refine ⟨219830444967451387531921487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146553629978300925021280991 219830444967451387531921487)
  ·
    refine ⟨329745667451177081297882231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219830444967451387531921487 329745667451177081297882231)
    ·
      refine ⟨494618501176765621946823347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 329745667451177081297882231 494618501176765621946823347)
      ·
        refine ⟨741927751765148432920235021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 494618501176765621946823347 741927751765148432920235021)
        ·
          refine ⟨278222906911930662345088133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 741927751765148432920235021 278222906911930662345088133)
          ·
            refine ⟨52166795045986999189704025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 278222906911930662345088133 52166795045986999189704025)
            ·
              refine ⟨39125096284490249392278019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52166795045986999189704025 39125096284490249392278019)
              ·
                refine ⟨58687644426735374088417029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39125096284490249392278019 58687644426735374088417029)
                ·
                  refine ⟨11003933330012882641578193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 58687644426735374088417029 11003933330012882641578193)
                  ·
                    refine ⟨8252949997509661981183645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11003933330012882641578193 8252949997509661981183645)
                    ·
                      refine ⟨3094856249066123242943867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8252949997509661981183645 3094856249066123242943867)
                      ·
                        rfl

theorem cell23_6027211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 1, 4, 2, 3].length) (baseStart_6027211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6027211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6027211 prefixEnd_6027211 := by exact prefixLift 6027211
  have htrace : WordTrace (prefixWord ++ tailWord_6027211) baseStart_6027211 baseEnd_6027211 := by
    simpa [prefixWord, tailWord_6027211, baseEnd_6027211] using wordTrace_append hprefix tailTrace_6027211
  have hstable : (prefixWord ++ tailWord_6027211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6027211).length < 2 ^ (prefixWord ++ tailWord_6027211).sum := by decide
  have hdescent : baseEnd_6027211 < baseStart_6027211 := by decide
  rcases family_descends (prefixWord ++ tailWord_6027211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6027244 : List Nat := [2, 2, 1, 1, 2, 1, 1, 2, 2, 9]
def baseStart_6027244 : Nat := 118140960795 + 6027244 * 2 ^ 59
def prefixEnd_6027244 : Nat := 4983230072969 + 3 ^ 40 * 6027244 * 2
def baseEnd_6027244 : Nat := 1031624397975907204610405

theorem tailTrace_6027244 : CollatzResearch.WordTrace tailWord_6027244 prefixEnd_6027244 1031624397975907204610405 := by
  unfold tailWord_6027244
  simp only [CollatzResearch.WordTrace]
  refine ⟨109915824288165917083936393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146554432384221222778581857 109915824288165917083936393)
  ·
    refine ⟨82436868216124437812952295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109915824288165917083936393 82436868216124437812952295)
    ·
      refine ⟨123655302324186656719428443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82436868216124437812952295 123655302324186656719428443)
      ·
        refine ⟨185482953486279985079142665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123655302324186656719428443 185482953486279985079142665)
        ·
          refine ⟨139112215114709988809356999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 185482953486279985079142665 139112215114709988809356999)
          ·
            refine ⟨208668322672064983214035499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139112215114709988809356999 208668322672064983214035499)
            ·
              refine ⟨313002484008097474821053249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 208668322672064983214035499 313002484008097474821053249)
              ·
                refine ⟨234751863006073106115789937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 313002484008097474821053249 234751863006073106115789937)
                ·
                  refine ⟨176063897254554829586842453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 234751863006073106115789937 176063897254554829586842453)
                  ·
                    refine ⟨1031624397975907204610405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 176063897254554829586842453 1031624397975907204610405)
                    ·
                      rfl

theorem cell23_6027244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 9].length) (baseStart_6027244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6027244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6027244 prefixEnd_6027244 := by exact prefixLift 6027244
  have htrace : WordTrace (prefixWord ++ tailWord_6027244) baseStart_6027244 baseEnd_6027244 := by
    simpa [prefixWord, tailWord_6027244, baseEnd_6027244] using wordTrace_append hprefix tailTrace_6027244
  have hstable : (prefixWord ++ tailWord_6027244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6027244).length < 2 ^ (prefixWord ++ tailWord_6027244).sum := by decide
  have hdescent : baseEnd_6027244 < baseStart_6027244 := by decide
  rcases family_descends (prefixWord ++ tailWord_6027244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6027291 : List Nat := [1, 1, 1, 1, 1, 1, 3, 4, 6, 4]
def baseStart_6027291 : Nat := 118140960795 + 6027291 * 2 ^ 59
def prefixEnd_6027291 : Nat := 4983230072969 + 3 ^ 40 * 6027291 * 2
def baseEnd_6027291 : Nat := 1031632442506160976647833

theorem tailTrace_6027291 : CollatzResearch.WordTrace tailWord_6027291 prefixEnd_6027291 1031632442506160976647833 := by
  unfold tailWord_6027291
  simp only [CollatzResearch.WordTrace]
  refine ⟨219833362807161561194833727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146555575204774374129889151 219833362807161561194833727)
  ·
    refine ⟨329750044210742341792250591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219833362807161561194833727 329750044210742341792250591)
    ·
      refine ⟨494625066316113512688375887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 329750044210742341792250591 494625066316113512688375887)
      ·
        refine ⟨741937599474170269032563831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 494625066316113512688375887 741937599474170269032563831)
        ·
          refine ⟨1112906399211255403548845747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 741937599474170269032563831 1112906399211255403548845747)
          ·
            refine ⟨1669359598816883105323268621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1112906399211255403548845747 1669359598816883105323268621)
            ·
              refine ⟨626009849556331164496225733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1669359598816883105323268621 626009849556331164496225733)
              ·
                refine ⟨117376846791812093343042325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 626009849556331164496225733 117376846791812093343042325)
                ·
                  refine ⟨5502039693366191875455109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 117376846791812093343042325 5502039693366191875455109)
                  ·
                    refine ⟨1031632442506160976647833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5502039693366191875455109 1031632442506160976647833)
                    ·
                      rfl

theorem cell23_6027291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 6, 4].length) (baseStart_6027291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6027291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6027291 prefixEnd_6027291 := by exact prefixLift 6027291
  have htrace : WordTrace (prefixWord ++ tailWord_6027291) baseStart_6027291 baseEnd_6027291 := by
    simpa [prefixWord, tailWord_6027291, baseEnd_6027291] using wordTrace_append hprefix tailTrace_6027291
  have hstable : (prefixWord ++ tailWord_6027291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6027291).length < 2 ^ (prefixWord ++ tailWord_6027291).sum := by decide
  have hdescent : baseEnd_6027291 < baseStart_6027291 := by decide
  rcases family_descends (prefixWord ++ tailWord_6027291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6027298 : List Nat := [3, 3, 1, 1, 1, 2, 3, 1, 3, 1, 4]
def baseStart_6027298 : Nat := 118140960795 + 6027298 * 2 ^ 59
def prefixEnd_6027298 : Nat := 4983230072969 + 3 ^ 40 * 6027298 * 2
def baseEnd_6027298 : Nat := 3094900921883064402555967

theorem tailTrace_6027298 : CollatzResearch.WordTrace tailWord_6027298 prefixEnd_6027298 3094900921883064402555967 := by
  unfold tailWord_6027298
  simp only [CollatzResearch.WordTrace]
  refine ⟨54958404529534050347584637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146555745412090800926892365 54958404529534050347584637)
  ·
    refine ⟨20609401698575268880344239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54958404529534050347584637 20609401698575268880344239)
    ·
      refine ⟨30914102547862903320516359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20609401698575268880344239 30914102547862903320516359)
      ·
        refine ⟨46371153821794354980774539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30914102547862903320516359 46371153821794354980774539)
        ·
          refine ⟨69556730732691532471161809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46371153821794354980774539 69556730732691532471161809)
          ·
            refine ⟨52167548049518649353371357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69556730732691532471161809 52167548049518649353371357)
            ·
              refine ⟨19562830518569493507514259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52167548049518649353371357 19562830518569493507514259)
              ·
                refine ⟨29344245777854240261271389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19562830518569493507514259 29344245777854240261271389)
                ·
                  refine ⟨11004092166695340097976771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29344245777854240261271389 11004092166695340097976771)
                  ·
                    refine ⟨16506138250043010146965157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11004092166695340097976771 16506138250043010146965157)
                    ·
                      refine ⟨3094900921883064402555967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16506138250043010146965157 3094900921883064402555967)
                      ·
                        rfl

theorem cell23_6027298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 3, 1, 3, 1, 4].length) (baseStart_6027298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6027298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6027298 prefixEnd_6027298 := by exact prefixLift 6027298
  have htrace : WordTrace (prefixWord ++ tailWord_6027298) baseStart_6027298 baseEnd_6027298 := by
    simpa [prefixWord, tailWord_6027298, baseEnd_6027298] using wordTrace_append hprefix tailTrace_6027298
  have hstable : (prefixWord ++ tailWord_6027298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6027298).length < 2 ^ (prefixWord ++ tailWord_6027298).sum := by decide
  have hdescent : baseEnd_6027298 < baseStart_6027298 := by decide
  rcases family_descends (prefixWord ++ tailWord_6027298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6027321 : List Nat := [1, 2, 1, 5, 3, 11]
def baseStart_6027321 : Nat := 118140960795 + 6027321 * 2 ^ 59
def prefixEnd_6027321 : Nat := 4983230072969 + 3 ^ 40 * 6027321 * 2
def baseEnd_6027321 : Nat := 12736266386576616512627

theorem tailTrace_6027321 : CollatzResearch.WordTrace tailWord_6027321 prefixEnd_6027321 12736266386576616512627 := by
  unfold tailWord_6027321
  simp only [CollatzResearch.WordTrace]
  refine ⟨219834456997052876318425817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146556304664701917545617211 219834456997052876318425817)
  ·
    refine ⟨164875842747789657238819363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219834456997052876318425817 164875842747789657238819363)
    ·
      refine ⟨247313764121684485858229045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164875842747789657238819363 247313764121684485858229045)
      ·
        refine ⟨23185665386407920549208973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 247313764121684485858229045 23185665386407920549208973)
        ·
          refine ⟨8694624519902970205953365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23185665386407920549208973 8694624519902970205953365)
          ·
            refine ⟨12736266386576616512627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 8694624519902970205953365 12736266386576616512627)
            ·
              rfl

theorem cell23_6027321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 11].length) (baseStart_6027321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6027321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6027321 prefixEnd_6027321 := by exact prefixLift 6027321
  have htrace : WordTrace (prefixWord ++ tailWord_6027321) baseStart_6027321 baseEnd_6027321 := by
    simpa [prefixWord, tailWord_6027321, baseEnd_6027321] using wordTrace_append hprefix tailTrace_6027321
  have hstable : (prefixWord ++ tailWord_6027321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6027321).length < 2 ^ (prefixWord ++ tailWord_6027321).sum := by decide
  have hdescent : baseEnd_6027321 < baseStart_6027321 := by decide
  rcases family_descends (prefixWord ++ tailWord_6027321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6027325 : List Nat := [1, 4, 1, 3, 1, 1, 4, 2, 2, 4]
def baseStart_6027325 : Nat := 118140960795 + 6027325 * 2 ^ 59
def prefixEnd_6027325 : Nat := 4983230072969 + 3 ^ 40 * 6027325 * 2
def baseEnd_6027325 : Nat := 1031638261953578598972781

theorem tailTrace_6027325 : CollatzResearch.WordTrace tailWord_6027325 prefixEnd_6027325 1031638261953578598972781 := by
  unfold tailWord_6027325
  simp only [CollatzResearch.WordTrace]
  refine ⟨219834602889038385001571429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146556401926025590001047619 219834602889038385001571429)
  ·
    refine ⟨41218988041694697187794643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 219834602889038385001571429 41218988041694697187794643)
    ·
      refine ⟨61828482062542045781691965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41218988041694697187794643 61828482062542045781691965)
      ·
        refine ⟨23185680773453267168134487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61828482062542045781691965 23185680773453267168134487)
        ·
          refine ⟨34778521160179900752201731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23185680773453267168134487 34778521160179900752201731)
          ·
            refine ⟨52167781740269851128302597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34778521160179900752201731 52167781740269851128302597)
            ·
              refine ⟨9781459076300597086556737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52167781740269851128302597 9781459076300597086556737)
              ·
                refine ⟨7336094307225447814917553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9781459076300597086556737 7336094307225447814917553)
                ·
                  refine ⟨5502070730419085861188165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7336094307225447814917553 5502070730419085861188165)
                  ·
                    refine ⟨1031638261953578598972781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5502070730419085861188165 1031638261953578598972781)
                    ·
                      rfl

theorem cell23_6027325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 4, 2, 2, 4].length) (baseStart_6027325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6027325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6027325 prefixEnd_6027325 := by exact prefixLift 6027325
  have htrace : WordTrace (prefixWord ++ tailWord_6027325) baseStart_6027325 baseEnd_6027325 := by
    simpa [prefixWord, tailWord_6027325, baseEnd_6027325] using wordTrace_append hprefix tailTrace_6027325
  have hstable : (prefixWord ++ tailWord_6027325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6027325).length < 2 ^ (prefixWord ++ tailWord_6027325).sum := by decide
  have hdescent : baseEnd_6027325 < baseStart_6027325 := by decide
  rcases family_descends (prefixWord ++ tailWord_6027325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6027361 : List Nat := [1, 2, 3, 1, 1, 2, 1, 3, 2, 2, 5]
def baseStart_6027361 : Nat := 118140960795 + 6027361 * 2 ^ 59
def prefixEnd_6027361 : Nat := 4983230072969 + 3 ^ 40 * 6027361 * 2
def baseEnd_6027361 : Nat := 3094933271164297656068177

theorem tailTrace_6027361 : CollatzResearch.WordTrace tailWord_6027361 prefixEnd_6027361 3094933271164297656068177 := by
  unfold tailWord_6027361
  simp only [CollatzResearch.WordTrace]
  refine ⟨219835915916907963149881937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146557277277938642099921291 219835915916907963149881937)
  ·
    refine ⟨164876936937680972362411453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219835915916907963149881937 164876936937680972362411453)
    ·
      refine ⟨61828851351630364635904295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 164876936937680972362411453 61828851351630364635904295)
      ·
        refine ⟨92743277027445546953856443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61828851351630364635904295 92743277027445546953856443)
        ·
          refine ⟨139114915541168320430784665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92743277027445546953856443 139114915541168320430784665)
          ·
            refine ⟨104336186655876240323088499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 139114915541168320430784665 104336186655876240323088499)
            ·
              refine ⟨156504279983814360484632749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104336186655876240323088499 156504279983814360484632749)
              ·
                refine ⟨58689104993930385181737281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 156504279983814360484632749 58689104993930385181737281)
                ·
                  refine ⟨44016828745447788886302961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58689104993930385181737281 44016828745447788886302961)
                  ·
                    refine ⟨33012621559085841664727221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 44016828745447788886302961 33012621559085841664727221)
                    ·
                      refine ⟨3094933271164297656068177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33012621559085841664727221 3094933271164297656068177)
                      ·
                        rfl

theorem cell23_6027361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 3, 2, 2, 5].length) (baseStart_6027361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6027361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6027361 prefixEnd_6027361 := by exact prefixLift 6027361
  have htrace : WordTrace (prefixWord ++ tailWord_6027361) baseStart_6027361 baseEnd_6027361 := by
    simpa [prefixWord, tailWord_6027361, baseEnd_6027361] using wordTrace_append hprefix tailTrace_6027361
  have hstable : (prefixWord ++ tailWord_6027361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6027361).length < 2 ^ (prefixWord ++ tailWord_6027361).sum := by decide
  have hdescent : baseEnd_6027361 < baseStart_6027361 := by decide
  rcases family_descends (prefixWord ++ tailWord_6027361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6027382 : List Nat := [5, 1, 1, 2, 1, 3, 1, 1, 4, 1, 3]
def baseStart_6027382 : Nat := 118140960795 + 6027382 * 2 ^ 59
def prefixEnd_6027382 : Nat := 4983230072969 + 3 ^ 40 * 6027382 * 2
def baseEnd_6027382 : Nat := 3094944054258042073905581

theorem tailTrace_6027382 : CollatzResearch.WordTrace tailWord_6027382 prefixEnd_6027382 3094944054258042073905581 := by
  unfold tailWord_6027382
  simp only [CollatzResearch.WordTrace]
  refine ⟨13739792615614492733524775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 146557787899887922490930933 13739792615614492733524775)
  ·
    refine ⟨20609688923421739100287163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13739792615614492733524775 20609688923421739100287163)
    ·
      refine ⟨30914533385132608650430745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20609688923421739100287163 30914533385132608650430745)
      ·
        refine ⟨23185900038849456487823059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30914533385132608650430745 23185900038849456487823059)
        ·
          refine ⟨34778850058274184731734589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23185900038849456487823059 34778850058274184731734589)
          ·
            refine ⟨13042068771852819274400471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34778850058274184731734589 13042068771852819274400471)
            ·
              refine ⟨19563103157779228911600707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13042068771852819274400471 19563103157779228911600707)
              ·
                refine ⟨29344654736668843367401061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19563103157779228911600707 29344654736668843367401061)
                ·
                  refine ⟨5502122763125408131387699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29344654736668843367401061 5502122763125408131387699)
                  ·
                    refine ⟨8253184144688112197081549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5502122763125408131387699 8253184144688112197081549)
                    ·
                      refine ⟨3094944054258042073905581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8253184144688112197081549 3094944054258042073905581)
                      ·
                        rfl

theorem cell23_6027382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 1, 1, 4, 1, 3].length) (baseStart_6027382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6027382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6027382 prefixEnd_6027382 := by exact prefixLift 6027382
  have htrace : WordTrace (prefixWord ++ tailWord_6027382) baseStart_6027382 baseEnd_6027382 := by
    simpa [prefixWord, tailWord_6027382, baseEnd_6027382] using wordTrace_append hprefix tailTrace_6027382
  have hstable : (prefixWord ++ tailWord_6027382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6027382).length < 2 ^ (prefixWord ++ tailWord_6027382).sum := by decide
  have hdescent : baseEnd_6027382 < baseStart_6027382 := by decide
  rcases family_descends (prefixWord ++ tailWord_6027382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6027456 : List Nat := [2, 1, 1, 2, 5, 3, 2, 1, 2, 2, 2]
def baseStart_6027456 : Nat := 118140960795 + 6027456 * 2 ^ 59
def prefixEnd_6027456 : Nat := 4983230072969 + 3 ^ 40 * 6027456 * 2
def baseEnd_6027456 : Nat := 3094982051826474784380241

theorem tailTrace_6027456 : CollatzResearch.WordTrace tailWord_6027456 prefixEnd_6027456 3094982051826474784380241 := by
  unfold tailWord_6027456
  simp only [CollatzResearch.WordTrace]
  refine ⟨109919690425781897187295111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146559587234375862916393481 109919690425781897187295111)
  ·
    refine ⟨164879535638672845780942667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109919690425781897187295111 164879535638672845780942667)
    ·
      refine ⟨247319303458009268671414001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164879535638672845780942667 247319303458009268671414001)
      ·
        refine ⟨185489477593506951503560501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 247319303458009268671414001 185489477593506951503560501)
        ·
          refine ⟨17389638524391276703458797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 185489477593506951503560501 17389638524391276703458797)
          ·
            refine ⟨6521114446646728763797049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17389638524391276703458797 6521114446646728763797049)
            ·
              refine ⟨4890835834985046572847787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6521114446646728763797049 4890835834985046572847787)
              ·
                refine ⟨7336253752477569859271681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4890835834985046572847787 7336253752477569859271681)
                ·
                  refine ⟨5502190314358177394453761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7336253752477569859271681 5502190314358177394453761)
                  ·
                    refine ⟨4126642735768633045840321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5502190314358177394453761 4126642735768633045840321)
                    ·
                      refine ⟨3094982051826474784380241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4126642735768633045840321 3094982051826474784380241)
                      ·
                        rfl

theorem cell23_6027456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 2, 1, 2, 2, 2].length) (baseStart_6027456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6027456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6027456 prefixEnd_6027456 := by exact prefixLift 6027456
  have htrace : WordTrace (prefixWord ++ tailWord_6027456) baseStart_6027456 baseEnd_6027456 := by
    simpa [prefixWord, tailWord_6027456, baseEnd_6027456] using wordTrace_append hprefix tailTrace_6027456
  have hstable : (prefixWord ++ tailWord_6027456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6027456).length < 2 ^ (prefixWord ++ tailWord_6027456).sum := by decide
  have hdescent : baseEnd_6027456 < baseStart_6027456 := by decide
  rcases family_descends (prefixWord ++ tailWord_6027456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6027485 : List Nat := [1, 4, 3, 2, 1, 1, 1, 2, 1, 2, 5]
def baseStart_6027485 : Nat := 118140960795 + 6027485 * 2 ^ 59
def prefixEnd_6027485 : Nat := 4983230072969 + 3 ^ 40 * 6027485 * 2
def baseEnd_6027485 : Nat := 3094996942765455170917607

theorem tailTrace_6027485 : CollatzResearch.WordTrace tailWord_6027485 prefixEnd_6027485 3094996942765455170917607 := by
  unfold tailWord_6027485
  simp only [CollatzResearch.WordTrace]
  refine ⟨219840438568458732327395909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146560292378972488218263939 219840438568458732327395909)
  ·
    refine ⟨41220082231586012311386733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 219840438568458732327395909 41220082231586012311386733)
    ·
      refine ⟨15457530836844754616770025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41220082231586012311386733 15457530836844754616770025)
      ·
        refine ⟨11593148127633565962577519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15457530836844754616770025 11593148127633565962577519)
        ·
          refine ⟨17389722191450348943866279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11593148127633565962577519 17389722191450348943866279)
          ·
            refine ⟨26084583287175523415799419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17389722191450348943866279 26084583287175523415799419)
            ·
              refine ⟨39126874930763285123699129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26084583287175523415799419 39126874930763285123699129)
              ·
                refine ⟨29345156198072463842774347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39126874930763285123699129 29345156198072463842774347)
                ·
                  refine ⟨44017734297108695764161521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29345156198072463842774347 44017734297108695764161521)
                  ·
                    refine ⟨33013300722831521823121141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 44017734297108695764161521 33013300722831521823121141)
                    ·
                      refine ⟨3094996942765455170917607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33013300722831521823121141 3094996942765455170917607)
                      ·
                        rfl

theorem cell23_6027485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_6027485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6027485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6027485 prefixEnd_6027485 := by exact prefixLift 6027485
  have htrace : WordTrace (prefixWord ++ tailWord_6027485) baseStart_6027485 baseEnd_6027485 := by
    simpa [prefixWord, tailWord_6027485, baseEnd_6027485] using wordTrace_append hprefix tailTrace_6027485
  have hstable : (prefixWord ++ tailWord_6027485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6027485).length < 2 ^ (prefixWord ++ tailWord_6027485).sum := by decide
  have hdescent : baseEnd_6027485 < baseStart_6027485 := by decide
  rcases family_descends (prefixWord ++ tailWord_6027485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6027490 : List Nat := [3, 3, 4, 1, 1, 1, 2, 2, 2, 2, 2]
def baseStart_6027490 : Nat := 118140960795 + 6027490 * 2 ^ 59
def prefixEnd_6027490 : Nat := 4983230072969 + 3 ^ 40 * 6027490 * 2
def baseEnd_6027490 : Nat := 3094999510168727651355085

theorem tailTrace_6027490 : CollatzResearch.WordTrace tailWord_6027490 prefixEnd_6027490 3094999510168727651355085 := by
  unfold tailWord_6027490
  simp only [CollatzResearch.WordTrace]
  refine ⟨54960155233360154545331981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146560413955627078787551949 54960155233360154545331981)
  ·
    refine ⟨20610058212510057954499493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54960155233360154545331981 20610058212510057954499493)
    ·
      refine ⟨3864385914845635866468655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20610058212510057954499493 3864385914845635866468655)
      ·
        refine ⟨5796578872268453799702983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3864385914845635866468655 5796578872268453799702983)
        ·
          refine ⟨8694868308402680699554475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5796578872268453799702983 8694868308402680699554475)
          ·
            refine ⟨13042302462604021049331713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8694868308402680699554475 13042302462604021049331713)
            ·
              refine ⟨9781726846953015786998785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13042302462604021049331713 9781726846953015786998785)
              ·
                refine ⟨7336295135214761840249089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9781726846953015786998785 7336295135214761840249089)
                ·
                  refine ⟨5502221351411071380186817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7336295135214761840249089 5502221351411071380186817)
                  ·
                    refine ⟨4126666013558303535140113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5502221351411071380186817 4126666013558303535140113)
                    ·
                      refine ⟨3094999510168727651355085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4126666013558303535140113 3094999510168727651355085)
                      ·
                        rfl

theorem cell23_6027490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 2, 2, 2, 2, 2].length) (baseStart_6027490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6027490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6027490 prefixEnd_6027490 := by exact prefixLift 6027490
  have htrace : WordTrace (prefixWord ++ tailWord_6027490) baseStart_6027490 baseEnd_6027490 := by
    simpa [prefixWord, tailWord_6027490, baseEnd_6027490] using wordTrace_append hprefix tailTrace_6027490
  have hstable : (prefixWord ++ tailWord_6027490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6027490).length < 2 ^ (prefixWord ++ tailWord_6027490).sum := by decide
  have hdescent : baseEnd_6027490 < baseStart_6027490 := by decide
  rcases family_descends (prefixWord ++ tailWord_6027490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6027498 : List Nat := [3, 1, 3, 1, 1, 2, 1, 1, 2, 3, 5]
def baseStart_6027498 : Nat := 118140960795 + 6027498 * 2 ^ 59
def prefixEnd_6027498 : Nat := 4983230072969 + 3 ^ 40 * 6027498 * 2
def baseEnd_6027498 : Nat := 3095003618013963620055047

theorem tailTrace_6027498 : CollatzResearch.WordTrace tailWord_6027498 prefixEnd_6027498 3095003618013963620055047 := by
  unfold tailWord_6027498
  simp only [CollatzResearch.WordTrace]
  refine ⟨54960228179352908886904787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146560608478274423698412765 54960228179352908886904787)
  ·
    refine ⟨82440342269029363330357181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54960228179352908886904787 82440342269029363330357181)
    ·
      refine ⟨30915128350886011248883943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82440342269029363330357181 30915128350886011248883943)
      ·
        refine ⟨46372692526329016873325915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30915128350886011248883943 46372692526329016873325915)
        ·
          refine ⟨69559038789493525309988873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46372692526329016873325915 69559038789493525309988873)
          ·
            refine ⟨52169279092120143982491655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69559038789493525309988873 52169279092120143982491655)
            ·
              refine ⟨78253918638180215973737483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52169279092120143982491655 78253918638180215973737483)
              ·
                refine ⟨117380877957270323960606225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78253918638180215973737483 117380877957270323960606225)
                ·
                  refine ⟨88035658467952742970454669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 117380877957270323960606225 88035658467952742970454669)
                  ·
                    refine ⟨33013371925482278613920501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 88035658467952742970454669 33013371925482278613920501)
                    ·
                      refine ⟨3095003618013963620055047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33013371925482278613920501 3095003618013963620055047)
                      ·
                        rfl

theorem cell23_6027498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 1, 2, 3, 5].length) (baseStart_6027498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6027498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6027498 prefixEnd_6027498 := by exact prefixLift 6027498
  have htrace : WordTrace (prefixWord ++ tailWord_6027498) baseStart_6027498 baseEnd_6027498 := by
    simpa [prefixWord, tailWord_6027498, baseEnd_6027498] using wordTrace_append hprefix tailTrace_6027498
  have hstable : (prefixWord ++ tailWord_6027498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6027498).length < 2 ^ (prefixWord ++ tailWord_6027498).sum := by decide
  have hdescent : baseEnd_6027498 < baseStart_6027498 := by decide
  rcases family_descends (prefixWord ++ tailWord_6027498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6027522 : List Nat := [3, 4, 1, 1, 2, 1, 1, 1, 5, 4]
def baseStart_6027522 : Nat := 118140960795 + 6027522 * 2 ^ 59
def prefixEnd_6027522 : Nat := 4983230072969 + 3 ^ 40 * 6027522 * 2
def baseEnd_6027522 : Nat := 1031671980516557175384979

theorem tailTrace_6027522 : CollatzResearch.WordTrace tailWord_6027522 prefixEnd_6027522 1031671980516557175384979 := by
  unfold tailWord_6027522
  simp only [CollatzResearch.WordTrace]
  refine ⟨54960447017331171911623205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146561192046216458430995213 54960447017331171911623205)
  ·
    refine ⟨10305083815749594733429351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54960447017331171911623205 10305083815749594733429351)
    ·
      refine ⟨15457625723624392100144027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10305083815749594733429351 15457625723624392100144027)
      ·
        refine ⟨23186438585436588150216041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15457625723624392100144027 23186438585436588150216041)
        ·
          refine ⟨17389828939077441112662031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23186438585436588150216041 17389828939077441112662031)
          ·
            refine ⟨26084743408616161668993047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17389828939077441112662031 26084743408616161668993047)
            ·
              refine ⟨39127115112924242503489571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26084743408616161668993047 39127115112924242503489571)
              ·
                refine ⟨58690672669386363755234357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39127115112924242503489571 58690672669386363755234357)
                ·
                  refine ⟨5502250562754971602053221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 58690672669386363755234357 5502250562754971602053221)
                  ·
                    refine ⟨1031671980516557175384979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5502250562754971602053221 1031671980516557175384979)
                    ·
                      rfl

theorem cell23_6027522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 1, 5, 4].length) (baseStart_6027522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6027522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6027522 prefixEnd_6027522 := by exact prefixLift 6027522
  have htrace : WordTrace (prefixWord ++ tailWord_6027522) baseStart_6027522 baseEnd_6027522 := by
    simpa [prefixWord, tailWord_6027522, baseEnd_6027522] using wordTrace_append hprefix tailTrace_6027522
  have hstable : (prefixWord ++ tailWord_6027522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6027522).length < 2 ^ (prefixWord ++ tailWord_6027522).sum := by decide
  have hdescent : baseEnd_6027522 < baseStart_6027522 := by decide
  rcases family_descends (prefixWord ++ tailWord_6027522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6027552 : List Nat := [2, 1, 1, 5, 2, 3, 1, 2, 6]
def baseStart_6027552 : Nat := 118140960795 + 6027552 * 2 ^ 59
def prefixEnd_6027552 : Nat := 4983230072969 + 3 ^ 40 * 6027552 * 2
def baseEnd_6027552 : Nat := 343892371774367378753311

theorem tailTrace_6027552 : CollatzResearch.WordTrace tailWord_6027552 prefixEnd_6027552 343892371774367378753311 := by
  unfold tailWord_6027552
  simp only [CollatzResearch.WordTrace]
  refine ⟨109921441129608001385042455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146561921506144001846723273 109921441129608001385042455)
  ·
    refine ⟨164882161694412002077563683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109921441129608001385042455 164882161694412002077563683)
    ·
      refine ⟨247323242541618003116345525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164882161694412002077563683 247323242541618003116345525)
      ·
        refine ⟨23186553988276687792157393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 247323242541618003116345525 23186553988276687792157393)
        ·
          refine ⟨17389915491207515844118045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23186553988276687792157393 17389915491207515844118045)
          ·
            refine ⟨6521218309202818441544267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17389915491207515844118045 6521218309202818441544267)
            ·
              refine ⟨9781827463804227662316401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6521218309202818441544267 9781827463804227662316401)
              ·
                refine ⟨7336370597853170746737301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9781827463804227662316401 7336370597853170746737301)
                ·
                  refine ⟨343892371774367378753311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7336370597853170746737301 343892371774367378753311)
                  ·
                    rfl

theorem cell23_6027552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 1, 2, 6].length) (baseStart_6027552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6027552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6027552 prefixEnd_6027552 := by exact prefixLift 6027552
  have htrace : WordTrace (prefixWord ++ tailWord_6027552) baseStart_6027552 baseEnd_6027552 := by
    simpa [prefixWord, tailWord_6027552, baseEnd_6027552] using wordTrace_append hprefix tailTrace_6027552
  have hstable : (prefixWord ++ tailWord_6027552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6027552).length < 2 ^ (prefixWord ++ tailWord_6027552).sum := by decide
  have hdescent : baseEnd_6027552 < baseStart_6027552 := by decide
  rcases family_descends (prefixWord ++ tailWord_6027552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6027568 : List Nat := [2, 1, 1, 1, 2, 2, 2, 1, 2, 5, 4]
def baseStart_6027568 : Nat := 118140960795 + 6027568 * 2 ^ 59
def prefixEnd_6027568 : Nat := 4983230072969 + 3 ^ 40 * 6027568 * 2
def baseEnd_6027568 : Nat := 3095039561659778346179725

theorem tailTrace_6027568 : CollatzResearch.WordTrace tailWord_6027568 prefixEnd_6027568 3095039561659778346179725 := by
  unfold tailWord_6027568
  simp only [CollatzResearch.WordTrace]
  refine ⟨109921732913579018751333679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146562310551438691668444905 109921732913579018751333679)
  ·
    refine ⟨164882599370368528127000519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109921732913579018751333679 164882599370368528127000519)
    ·
      refine ⟨247323899055552792190500779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164882599370368528127000519 247323899055552792190500779)
      ·
        refine ⟨370985848583329188285751169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 247323899055552792190500779 370985848583329188285751169)
        ·
          refine ⟨278239386437496891214313377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 370985848583329188285751169 278239386437496891214313377)
          ·
            refine ⟨208679539828122668410735033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 278239386437496891214313377 208679539828122668410735033)
            ·
              refine ⟨156509654871092001308051275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 208679539828122668410735033 156509654871092001308051275)
              ·
                refine ⟨234764482306638001962076913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 156509654871092001308051275 234764482306638001962076913)
                ·
                  refine ⟨176073361729978501471557685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 234764482306638001962076913 176073361729978501471557685)
                  ·
                    refine ⟨16506877662185484512958533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 176073361729978501471557685 16506877662185484512958533)
                    ·
                      refine ⟨3095039561659778346179725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16506877662185484512958533 3095039561659778346179725)
                      ·
                        rfl

theorem cell23_6027568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 2, 5, 4].length) (baseStart_6027568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6027568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6027568 prefixEnd_6027568 := by exact prefixLift 6027568
  have htrace : WordTrace (prefixWord ++ tailWord_6027568) baseStart_6027568 baseEnd_6027568 := by
    simpa [prefixWord, tailWord_6027568, baseEnd_6027568] using wordTrace_append hprefix tailTrace_6027568
  have hstable : (prefixWord ++ tailWord_6027568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6027568).length < 2 ^ (prefixWord ++ tailWord_6027568).sum := by decide
  have hdescent : baseEnd_6027568 < baseStart_6027568 := by decide
  rcases family_descends (prefixWord ++ tailWord_6027568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6027582 : List Nat := [4, 2, 1, 2, 1, 2, 1, 4, 1, 5]
def baseStart_6027582 : Nat := 118140960795 + 6027582 * 2 ^ 59
def prefixEnd_6027582 : Nat := 4983230072969 + 3 ^ 40 * 6027582 * 2
def baseEnd_6027582 : Nat := 1031682250129647097134887

theorem tailTrace_6027582 : CollatzResearch.WordTrace tailWord_6027582 prefixEnd_6027582 1031682250129647097134887 := by
  unfold tailWord_6027582
  simp only [CollatzResearch.WordTrace]
  refine ⟨27480497056138414736709625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 146562650966071545262451333 27480497056138414736709625)
  ·
    refine ⟨20610372792103811052532219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27480497056138414736709625 20610372792103811052532219)
    ·
      refine ⟨30915559188155716578798329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20610372792103811052532219 30915559188155716578798329)
      ·
        refine ⟨23186669391116787434098747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30915559188155716578798329 23186669391116787434098747)
        ·
          refine ⟨34780004086675181151148121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23186669391116787434098747 34780004086675181151148121)
          ·
            refine ⟨26085003065006385863361091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34780004086675181151148121 26085003065006385863361091)
            ·
              refine ⟨39127504597509578795041637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26085003065006385863361091 39127504597509578795041637)
              ·
                refine ⟨7336407112033046024070307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39127504597509578795041637 7336407112033046024070307)
                ·
                  refine ⟨11004610668049569036105461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7336407112033046024070307 11004610668049569036105461)
                  ·
                    refine ⟨1031682250129647097134887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11004610668049569036105461 1031682250129647097134887)
                    ·
                      rfl

theorem cell23_6027582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 4, 1, 5].length) (baseStart_6027582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6027582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6027582 prefixEnd_6027582 := by exact prefixLift 6027582
  have htrace : WordTrace (prefixWord ++ tailWord_6027582) baseStart_6027582 baseEnd_6027582 := by
    simpa [prefixWord, tailWord_6027582, baseEnd_6027582] using wordTrace_append hprefix tailTrace_6027582
  have hstable : (prefixWord ++ tailWord_6027582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6027582).length < 2 ^ (prefixWord ++ tailWord_6027582).sum := by decide
  have hdescent : baseEnd_6027582 < baseStart_6027582 := by decide
  rcases family_descends (prefixWord ++ tailWord_6027582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6027602 : List Nat := [3, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4]
def baseStart_6027602 : Nat := 118140960795 + 6027602 * 2 ^ 59
def prefixEnd_6027602 : Nat := 4983230072969 + 3 ^ 40 * 6027602 * 2
def baseEnd_6027602 : Nat := 3095057020002031213154569

theorem tailTrace_6027602 : CollatzResearch.WordTrace tailWord_6027602 prefixEnd_6027602 3095057020002031213154569 := by
  unfold tailWord_6027602
  simp only [CollatzResearch.WordTrace]
  refine ⟨54961176477258715327351265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146563137272689907539603373 54961176477258715327351265)
  ·
    refine ⟨41220882357944036495513449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54961176477258715327351265 41220882357944036495513449)
    ·
      refine ⟨30915661768458027371635087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41220882357944036495513449 30915661768458027371635087)
      ·
        refine ⟨46373492652687041057452631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30915661768458027371635087 46373492652687041057452631)
        ·
          refine ⟨69560238979030561586178947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46373492652687041057452631 69560238979030561586178947)
          ·
            refine ⟨104340358468545842379268421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69560238979030561586178947 104340358468545842379268421)
            ·
              refine ⟨19563817212852345446112829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 104340358468545842379268421 19563817212852345446112829)
              ·
                refine ⟨7336431454819629542292311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19563817212852345446112829 7336431454819629542292311)
                ·
                  refine ⟨11004647182229444313438467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7336431454819629542292311 11004647182229444313438467)
                  ·
                    refine ⟨16506970773344166470157701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11004647182229444313438467 16506970773344166470157701)
                    ·
                      refine ⟨3095057020002031213154569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16506970773344166470157701 3095057020002031213154569)
                      ·
                        rfl

theorem cell23_6027602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4].length) (baseStart_6027602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6027602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6027602 prefixEnd_6027602 := by exact prefixLift 6027602
  have htrace : WordTrace (prefixWord ++ tailWord_6027602) baseStart_6027602 baseEnd_6027602 := by
    simpa [prefixWord, tailWord_6027602, baseEnd_6027602] using wordTrace_append hprefix tailTrace_6027602
  have hstable : (prefixWord ++ tailWord_6027602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6027602).length < 2 ^ (prefixWord ++ tailWord_6027602).sum := by decide
  have hdescent : baseEnd_6027602 < baseStart_6027602 := by decide
  rcases family_descends (prefixWord ++ tailWord_6027602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6027652 : List Nat := [2, 3, 2, 1, 1, 2, 3, 2, 1, 3, 3]
def baseStart_6027652 : Nat := 118140960795 + 6027652 * 2 ^ 59
def prefixEnd_6027652 : Nat := 4983230072969 + 3 ^ 40 * 6027652 * 2
def baseEnd_6027652 : Nat := 3095082694034756017529339

theorem tailTrace_6027652 : CollatzResearch.WordTrace tailWord_6027652 prefixEnd_6027652 3095082694034756017529339 := by
  unfold tailWord_6027652
  simp only [CollatzResearch.WordTrace]
  refine ⟨109923264779426859924362605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146564353039235813232483473 109923264779426859924362605)
  ·
    refine ⟨41221224292285072471635977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109923264779426859924362605 41221224292285072471635977)
    ·
      refine ⟨30915918219213804353726983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41221224292285072471635977 30915918219213804353726983)
      ·
        refine ⟨46373877328820706530590475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30915918219213804353726983 46373877328820706530590475)
        ·
          refine ⟨69560815993231059795885713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46373877328820706530590475 69560815993231059795885713)
          ·
            refine ⟨52170611994923294846914285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69560815993231059795885713 52170611994923294846914285)
            ·
              refine ⟨19563979498096235567592857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52170611994923294846914285 19563979498096235567592857)
              ·
                refine ⟨14672984623572176675694643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19563979498096235567592857 14672984623572176675694643)
                ·
                  refine ⟨22009476935358265013541965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14672984623572176675694643 22009476935358265013541965)
                  ·
                    refine ⟨8253553850759349380078237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22009476935358265013541965 8253553850759349380078237)
                    ·
                      refine ⟨3095082694034756017529339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8253553850759349380078237 3095082694034756017529339)
                      ·
                        rfl

theorem cell23_6027652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 3, 2, 1, 3, 3].length) (baseStart_6027652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6027652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6027652 prefixEnd_6027652 := by exact prefixLift 6027652
  have htrace : WordTrace (prefixWord ++ tailWord_6027652) baseStart_6027652 baseEnd_6027652 := by
    simpa [prefixWord, tailWord_6027652, baseEnd_6027652] using wordTrace_append hprefix tailTrace_6027652
  have hstable : (prefixWord ++ tailWord_6027652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6027652).length < 2 ^ (prefixWord ++ tailWord_6027652).sum := by decide
  have hdescent : baseEnd_6027652 < baseStart_6027652 := by decide
  rcases family_descends (prefixWord ++ tailWord_6027652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6027685 : List Nat := [1, 3, 1, 2, 1, 1, 5, 1, 2, 6]
def baseStart_6027685 : Nat := 118140960795 + 6027685 * 2 ^ 59
def prefixEnd_6027685 : Nat := 4983230072969 + 3 ^ 40 * 6027685 * 2
def baseEnd_6027685 : Nat := 1031699879632118129472229

theorem tailTrace_6027685 : CollatzResearch.WordTrace tailWord_6027685 prefixEnd_6027685 1031699879632118129472229 := by
  unfold tailWord_6027685
  simp only [CollatzResearch.WordTrace]
  refine ⟨219847733167734166484676509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146565155445156110989784339 219847733167734166484676509)
  ·
    refine ⟨82442899937900312431753691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 219847733167734166484676509 82442899937900312431753691)
    ·
      refine ⟨123664349906850468647630537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82442899937900312431753691 123664349906850468647630537)
      ·
        refine ⟨92748262430137851485722903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123664349906850468647630537 92748262430137851485722903)
        ·
          refine ⟨139122393645206777228584355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92748262430137851485722903 139122393645206777228584355)
          ·
            refine ⟨208683590467810165842876533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139122393645206777228584355 208683590467810165842876533)
            ·
              refine ⟨19564086606357203047769675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 208683590467810165842876533 19564086606357203047769675)
              ·
                refine ⟨29346129909535804571654513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19564086606357203047769675 29346129909535804571654513)
                ·
                  refine ⟨22009597432151853428740885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29346129909535804571654513 22009597432151853428740885)
                  ·
                    refine ⟨1031699879632118129472229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22009597432151853428740885 1031699879632118129472229)
                    ·
                      rfl

theorem cell23_6027685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5, 1, 2, 6].length) (baseStart_6027685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6027685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6027685 prefixEnd_6027685 := by exact prefixLift 6027685
  have htrace : WordTrace (prefixWord ++ tailWord_6027685) baseStart_6027685 baseEnd_6027685 := by
    simpa [prefixWord, tailWord_6027685, baseEnd_6027685] using wordTrace_append hprefix tailTrace_6027685
  have hstable : (prefixWord ++ tailWord_6027685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6027685).length < 2 ^ (prefixWord ++ tailWord_6027685).sum := by decide
  have hdescent : baseEnd_6027685 < baseStart_6027685 := by decide
  rcases family_descends (prefixWord ++ tailWord_6027685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6027709 : List Nat := [1, 4, 1, 2, 2, 2, 2, 2, 1, 4, 2]
def baseStart_6027709 : Nat := 118140960795 + 6027709 * 2 ^ 59
def prefixEnd_6027709 : Nat := 4983230072969 + 3 ^ 40 * 6027709 * 2
def baseEnd_6027709 : Nat := 3095111962432062294516577

theorem tailTrace_6027709 : CollatzResearch.WordTrace tailWord_6027709 prefixEnd_6027709 3095111962432062294516577 := by
  unfold tailWord_6027709
  simp only [CollatzResearch.WordTrace]
  refine ⟨219848608519647218583550181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146565739013098145722366787 219848608519647218583550181)
  ·
    refine ⟨41221614097433853484415659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 219848608519647218583550181 41221614097433853484415659)
    ·
      refine ⟨61832421146150780226623489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41221614097433853484415659 61832421146150780226623489)
      ·
        refine ⟨46374315859613085169967617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61832421146150780226623489 46374315859613085169967617)
        ·
          refine ⟨34780736894709813877475713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46374315859613085169967617 34780736894709813877475713)
          ·
            refine ⟨26085552671032360408106785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34780736894709813877475713 26085552671032360408106785)
            ·
              refine ⟨19564164503274270306080089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26085552671032360408106785 19564164503274270306080089)
              ·
                refine ⟨14673123377455702729560067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19564164503274270306080089 14673123377455702729560067)
                ·
                  refine ⟨22009685066183554094340101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14673123377455702729560067 22009685066183554094340101)
                  ·
                    refine ⟨4126815949909416392688769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22009685066183554094340101 4126815949909416392688769)
                    ·
                      refine ⟨3095111962432062294516577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4126815949909416392688769 3095111962432062294516577)
                      ·
                        rfl

theorem cell23_6027709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 2, 2, 1, 4, 2].length) (baseStart_6027709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6027709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6027709 prefixEnd_6027709 := by exact prefixLift 6027709
  have htrace : WordTrace (prefixWord ++ tailWord_6027709) baseStart_6027709 baseEnd_6027709 := by
    simpa [prefixWord, tailWord_6027709, baseEnd_6027709] using wordTrace_append hprefix tailTrace_6027709
  have hstable : (prefixWord ++ tailWord_6027709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6027709).length < 2 ^ (prefixWord ++ tailWord_6027709).sum := by decide
  have hdescent : baseEnd_6027709 < baseStart_6027709 := by decide
  rcases family_descends (prefixWord ++ tailWord_6027709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6027732 : List Nat := [2, 4, 1, 2, 2, 1, 1, 3, 7]
def baseStart_6027732 : Nat := 118140960795 + 6027732 * 2 ^ 59
def prefixEnd_6027732 : Nat := 4983230072969 + 3 ^ 40 * 6027732 * 2
def baseEnd_6027732 : Nat := 343902641387457300503219

theorem tailTrace_6027732 : CollatzResearch.WordTrace tailWord_6027732 prefixEnd_6027732 343902641387457300503219 := by
  unfold tailWord_6027732
  simp only [CollatzResearch.WordTrace]
  refine ⟨109924723699281946755818725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146566298265709262341091633 109924723699281946755818725)
  ·
    refine ⟨20610885693615365016716011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 109924723699281946755818725 20610885693615365016716011)
    ·
      refine ⟨30916328540423047525074017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20610885693615365016716011 30916328540423047525074017)
      ·
        refine ⟨23187246405317285643805513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30916328540423047525074017 23187246405317285643805513)
        ·
          refine ⟨17390434803987964232854135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23187246405317285643805513 17390434803987964232854135)
          ·
            refine ⟨26085652205981946349281203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17390434803987964232854135 26085652205981946349281203)
            ·
              refine ⟨39128478308972919523921805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26085652205981946349281203 39128478308972919523921805)
              ·
                refine ⟨14673179365864844821470677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39128478308972919523921805 14673179365864844821470677)
                ·
                  refine ⟨343902641387457300503219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14673179365864844821470677 343902641387457300503219)
                  ·
                    rfl

theorem cell23_6027732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 3, 7].length) (baseStart_6027732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6027732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6027732 prefixEnd_6027732 := by exact prefixLift 6027732
  have htrace : WordTrace (prefixWord ++ tailWord_6027732) baseStart_6027732 baseEnd_6027732 := by
    simpa [prefixWord, tailWord_6027732, baseEnd_6027732] using wordTrace_append hprefix tailTrace_6027732
  have hstable : (prefixWord ++ tailWord_6027732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6027732).length < 2 ^ (prefixWord ++ tailWord_6027732).sum := by decide
  have hdescent : baseEnd_6027732 < baseStart_6027732 := by decide
  rcases family_descends (prefixWord ++ tailWord_6027732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6027743 : List Nat := [1, 1, 2, 3, 3, 3, 3, 1, 2, 2, 2]
def baseStart_6027743 : Nat := 118140960795 + 6027743 * 2 ^ 59
def prefixEnd_6027743 : Nat := 4983230072969 + 3 ^ 40 * 6027743 * 2
def baseEnd_6027743 : Nat := 3095129420774315161491421

theorem tailTrace_6027743 : CollatzResearch.WordTrace tailWord_6027743 prefixEnd_6027743 3095129420774315161491421 := by
  unfold tailWord_6027743
  simp only [CollatzResearch.WordTrace]
  refine ⟨219849848601524042390287883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146566565734349361593525255 219849848601524042390287883)
  ·
    refine ⟨329774772902286063585431825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219849848601524042390287883 329774772902286063585431825)
    ·
      refine ⟨247331079676714547689073869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 329774772902286063585431825 247331079676714547689073869)
      ·
        refine ⟨92749154878767955383402701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 247331079676714547689073869 92749154878767955383402701)
        ·
          refine ⟨34780933079537983268776013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92749154878767955383402701 34780933079537983268776013)
          ·
            refine ⟨13042849904826743725791005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34780933079537983268776013 13042849904826743725791005)
            ·
              refine ⟨4891068714310028897171627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13042849904826743725791005 4891068714310028897171627)
              ·
                refine ⟨7336603071465043345757441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4891068714310028897171627 7336603071465043345757441)
                ·
                  refine ⟨5502452303598782509318081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7336603071465043345757441 5502452303598782509318081)
                  ·
                    refine ⟨4126839227699086881988561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5502452303598782509318081 4126839227699086881988561)
                    ·
                      refine ⟨3095129420774315161491421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4126839227699086881988561 3095129420774315161491421)
                      ·
                        rfl

theorem cell23_6027743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 3, 1, 2, 2, 2].length) (baseStart_6027743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6027743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6027743 prefixEnd_6027743 := by exact prefixLift 6027743
  have htrace : WordTrace (prefixWord ++ tailWord_6027743) baseStart_6027743 baseEnd_6027743 := by
    simpa [prefixWord, tailWord_6027743, baseEnd_6027743] using wordTrace_append hprefix tailTrace_6027743
  have hstable : (prefixWord ++ tailWord_6027743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6027743).length < 2 ^ (prefixWord ++ tailWord_6027743).sum := by decide
  have hdescent : baseEnd_6027743 < baseStart_6027743 := by decide
  rcases family_descends (prefixWord ++ tailWord_6027743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6027745 : List Nat := [1, 2, 3, 1, 2, 2, 1, 1, 3, 7]
def baseStart_6027745 : Nat := 118140960795 + 6027745 * 2 ^ 59
def prefixEnd_6027745 : Nat := 4983230072969 + 3 ^ 40 * 6027745 * 2
def baseEnd_6027745 : Nat := 1031710149245208051222137

theorem tailTrace_6027745 : CollatzResearch.WordTrace tailWord_6027745 prefixEnd_6027745 1031710149245208051222137 := by
  unfold tailWord_6027745
  simp only [CollatzResearch.WordTrace]
  refine ⟨219849921547516796731860689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146566614365011197821240459 219849921547516796731860689)
  ·
    refine ⟨164887441160637597548895517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219849921547516796731860689 164887441160637597548895517)
    ·
      refine ⟨61832790435239099080835819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 164887441160637597548895517 61832790435239099080835819)
      ·
        refine ⟨92749185652858648621253729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61832790435239099080835819 92749185652858648621253729)
        ·
          refine ⟨69561889239643986465940297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92749185652858648621253729 69561889239643986465940297)
          ·
            refine ⟨52171416929732989849455223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69561889239643986465940297 52171416929732989849455223)
            ·
              refine ⟨78257125394599484774182835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52171416929732989849455223 78257125394599484774182835)
              ·
                refine ⟨117385688091899227161274253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78257125394599484774182835 117385688091899227161274253)
                ·
                  refine ⟨44019633034462210185477845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 117385688091899227161274253 44019633034462210185477845)
                  ·
                    refine ⟨1031710149245208051222137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44019633034462210185477845 1031710149245208051222137)
                    ·
                      rfl

theorem cell23_6027745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 1, 3, 7].length) (baseStart_6027745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6027745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6027745 prefixEnd_6027745 := by exact prefixLift 6027745
  have htrace : WordTrace (prefixWord ++ tailWord_6027745) baseStart_6027745 baseEnd_6027745 := by
    simpa [prefixWord, tailWord_6027745, baseEnd_6027745] using wordTrace_append hprefix tailTrace_6027745
  have hstable : (prefixWord ++ tailWord_6027745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6027745).length < 2 ^ (prefixWord ++ tailWord_6027745).sum := by decide
  have hdescent : baseEnd_6027745 < baseStart_6027745 := by decide
  rcases family_descends (prefixWord ++ tailWord_6027745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6027785 : List Nat := [1, 2, 1, 1, 3, 1, 2, 1, 1, 5, 5]
def baseStart_6027785 : Nat := 118140960795 + 6027785 * 2 ^ 59
def prefixEnd_6027785 : Nat := 4983230072969 + 3 ^ 40 * 6027785 * 2
def baseEnd_6027785 : Nat := 3095150986961803997166227

theorem tailTrace_6027785 : CollatzResearch.WordTrace tailWord_6027785 prefixEnd_6027785 3095150986961803997166227 := by
  unfold tailWord_6027785
  simp only [CollatzResearch.WordTrace]
  refine ⟨219851380467371883563316809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146567586978247922375544539 219851380467371883563316809)
  ·
    refine ⟨164888535350528912672487607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219851380467371883563316809 164888535350528912672487607)
    ·
      refine ⟨247332803025793369008731411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164888535350528912672487607 247332803025793369008731411)
      ·
        refine ⟨370999204538690053513097117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 247332803025793369008731411 370999204538690053513097117)
        ·
          refine ⟨139124701702008770067411419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 370999204538690053513097117 139124701702008770067411419)
          ·
            refine ⟨208687052553013155101117129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139124701702008770067411419 208687052553013155101117129)
            ·
              refine ⟨156515289414759866325837847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 208687052553013155101117129 156515289414759866325837847)
              ·
                refine ⟨234772934122139799488756771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 156515289414759866325837847 234772934122139799488756771)
                ·
                  refine ⟨352159401183209699233135157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 234772934122139799488756771 352159401183209699233135157)
                  ·
                    refine ⟨33014943860925909303106421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 352159401183209699233135157 33014943860925909303106421)
                    ·
                      refine ⟨3095150986961803997166227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33014943860925909303106421 3095150986961803997166227)
                      ·
                        rfl

theorem cell23_6027785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 5, 5].length) (baseStart_6027785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6027785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6027785 prefixEnd_6027785 := by exact prefixLift 6027785
  have htrace : WordTrace (prefixWord ++ tailWord_6027785) baseStart_6027785 baseEnd_6027785 := by
    simpa [prefixWord, tailWord_6027785, baseEnd_6027785] using wordTrace_append hprefix tailTrace_6027785
  have hstable : (prefixWord ++ tailWord_6027785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6027785).length < 2 ^ (prefixWord ++ tailWord_6027785).sum := by decide
  have hdescent : baseEnd_6027785 < baseStart_6027785 := by decide
  rcases family_descends (prefixWord ++ tailWord_6027785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6027802 : List Nat := [3, 1, 1, 3, 1, 1, 2, 1, 3, 4, 3]
def baseStart_6027802 : Nat := 118140960795 + 6027802 * 2 ^ 59
def prefixEnd_6027802 : Nat := 4983230072969 + 3 ^ 40 * 6027802 * 2
def baseEnd_6027802 : Nat := 3095159716132930430653649

theorem tailTrace_6027802 : CollatzResearch.WordTrace tailWord_6027802 prefixEnd_6027802 3095159716132930430653649 := by
  unfold tailWord_6027802
  simp only [CollatzResearch.WordTrace]
  refine ⟨54963000127077573866671415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146568000338873530311123773 54963000127077573866671415)
  ·
    refine ⟨82444500190616360800007123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54963000127077573866671415 82444500190616360800007123)
    ·
      refine ⟨123666750285924541200010685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82444500190616360800007123 123666750285924541200010685)
      ·
        refine ⟨46375031357221702950004007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123666750285924541200010685 46375031357221702950004007)
        ·
          refine ⟨69562547035832554425006011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46375031357221702950004007 69562547035832554425006011)
          ·
            refine ⟨104343820553748831637509017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69562547035832554425006011 104343820553748831637509017)
            ·
              refine ⟨78257865415311623728131763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104343820553748831637509017 78257865415311623728131763)
              ·
                refine ⟨117386798122967435592197645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78257865415311623728131763 117386798122967435592197645)
                ·
                  refine ⟨44020049296112788347074117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 117386798122967435592197645 44020049296112788347074117)
                  ·
                    refine ⟨8253759243021147815076397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 44020049296112788347074117 8253759243021147815076397)
                    ·
                      refine ⟨3095159716132930430653649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8253759243021147815076397 3095159716132930430653649)
                      ·
                        rfl

theorem cell23_6027802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 1, 3, 4, 3].length) (baseStart_6027802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6027802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6027802 prefixEnd_6027802 := by exact prefixLift 6027802
  have htrace : WordTrace (prefixWord ++ tailWord_6027802) baseStart_6027802 baseEnd_6027802 := by
    simpa [prefixWord, tailWord_6027802, baseEnd_6027802] using wordTrace_append hprefix tailTrace_6027802
  have hstable : (prefixWord ++ tailWord_6027802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6027802).length < 2 ^ (prefixWord ++ tailWord_6027802).sum := by decide
  have hdescent : baseEnd_6027802 < baseStart_6027802 := by decide
  rcases family_descends (prefixWord ++ tailWord_6027802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6027816 : List Nat := [2, 1, 5, 2, 1, 2, 2, 1, 2, 1, 4]
def baseStart_6027816 : Nat := 118140960795 + 6027816 * 2 ^ 59
def prefixEnd_6027816 : Nat := 4983230072969 + 3 ^ 40 * 6027816 * 2
def baseEnd_6027816 : Nat := 3095166904862093375878585

theorem tailTrace_6027816 : CollatzResearch.WordTrace tailWord_6027816 prefixEnd_6027816 3095166904862093375878585 := by
  unfold tailWord_6027816
  simp only [CollatzResearch.WordTrace]
  refine ⟨109926255565129787928847651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146568340753506383905130201 109926255565129787928847651)
  ·
    refine ⟨164889383347694681893271477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109926255565129787928847651 164889383347694681893271477)
    ·
      refine ⟨15458379688846376427494201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 164889383347694681893271477 15458379688846376427494201)
      ·
        refine ⟨11593784766634782320620651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15458379688846376427494201 11593784766634782320620651)
        ·
          refine ⟨17390677149952173480930977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11593784766634782320620651 17390677149952173480930977)
          ·
            refine ⟨13043007862464130110698233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17390677149952173480930977 13043007862464130110698233)
            ·
              refine ⟨9782255896848097583023675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13043007862464130110698233 9782255896848097583023675)
              ·
                refine ⟨14673383845272146374535513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9782255896848097583023675 14673383845272146374535513)
                ·
                  refine ⟨11005037883954109780901635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14673383845272146374535513 11005037883954109780901635)
                  ·
                    refine ⟨16507556825931164671352453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11005037883954109780901635 16507556825931164671352453)
                    ·
                      refine ⟨3095166904862093375878585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16507556825931164671352453 3095166904862093375878585)
                      ·
                        rfl

theorem cell23_6027816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 2, 1, 2, 1, 4].length) (baseStart_6027816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6027816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6027816 prefixEnd_6027816 := by exact prefixLift 6027816
  have htrace : WordTrace (prefixWord ++ tailWord_6027816) baseStart_6027816 baseEnd_6027816 := by
    simpa [prefixWord, tailWord_6027816, baseEnd_6027816] using wordTrace_append hprefix tailTrace_6027816
  have hstable : (prefixWord ++ tailWord_6027816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6027816).length < 2 ^ (prefixWord ++ tailWord_6027816).sum := by decide
  have hdescent : baseEnd_6027816 < baseStart_6027816 := by decide
  rcases family_descends (prefixWord ++ tailWord_6027816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6027835 : List Nat := [1, 1, 1, 1, 1, 2, 1, 2, 4, 9]
def baseStart_6027835 : Nat := 118140960795 + 6027835 * 2 ^ 59
def prefixEnd_6027835 : Nat := 4983230072969 + 3 ^ 40 * 6027835 * 2
def baseEnd_6027835 : Nat := 1031725553664842933846999

theorem tailTrace_6027835 : CollatzResearch.WordTrace tailWord_6027835 prefixEnd_6027835 1031725553664842933846999 := by
  unfold tailWord_6027835
  simp only [CollatzResearch.WordTrace]
  refine ⟨219853204117190742102636959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146568802744793828068424639 219853204117190742102636959)
  ·
    refine ⟨329779806175786113153955439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219853204117190742102636959 329779806175786113153955439)
    ·
      refine ⟨494669709263679169730933159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 329779806175786113153955439 494669709263679169730933159)
      ·
        refine ⟨742004563895518754596399739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 494669709263679169730933159 742004563895518754596399739)
        ·
          refine ⟨1113006845843278131894599609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 742004563895518754596399739 1113006845843278131894599609)
          ·
            refine ⟨834755134382458598920949707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1113006845843278131894599609 834755134382458598920949707)
            ·
              refine ⟨1252132701573687898381424561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 834755134382458598920949707 1252132701573687898381424561)
              ·
                refine ⟨939099526180265923786068421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1252132701573687898381424561 939099526180265923786068421)
                ·
                  refine ⟨176081161158799860709887829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 939099526180265923786068421 176081161158799860709887829)
                  ·
                    refine ⟨1031725553664842933846999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 176081161158799860709887829 1031725553664842933846999)
                    ·
                      rfl

theorem cell23_6027835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 4, 9].length) (baseStart_6027835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6027835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6027835 prefixEnd_6027835 := by exact prefixLift 6027835
  have htrace : WordTrace (prefixWord ++ tailWord_6027835) baseStart_6027835 baseEnd_6027835 := by
    simpa [prefixWord, tailWord_6027835, baseEnd_6027835] using wordTrace_append hprefix tailTrace_6027835
  have hstable : (prefixWord ++ tailWord_6027835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6027835).length < 2 ^ (prefixWord ++ tailWord_6027835).sum := by decide
  have hdescent : baseEnd_6027835 < baseStart_6027835 := by decide
  rcases family_descends (prefixWord ++ tailWord_6027835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6027852 : List Nat := [2, 2, 1, 3, 1, 2, 1, 1, 5, 5]
def baseStart_6027852 : Nat := 118140960795 + 6027852 * 2 ^ 59
def prefixEnd_6027852 : Nat := 4983230072969 + 3 ^ 40 * 6027852 * 2
def baseEnd_6027852 : Nat := 1031728463388551745009473

theorem tailTrace_6027852 : CollatzResearch.WordTrace tailWord_6027852 prefixEnd_6027852 1031728463388551745009473 := by
  unfold tailWord_6027852
  simp only [CollatzResearch.WordTrace]
  refine ⟨109926912079064577003002905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146569216105419436004003873 109926912079064577003002905)
  ·
    refine ⟨82445184059298432752252179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109926912079064577003002905 82445184059298432752252179)
    ·
      refine ⟨123667776088947649128378269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82445184059298432752252179 123667776088947649128378269)
      ·
        refine ⟨46375416033355368423141851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123667776088947649128378269 46375416033355368423141851)
        ·
          refine ⟨69563124050033052634712777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46375416033355368423141851 69563124050033052634712777)
          ·
            refine ⟨52172343037524789476034583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69563124050033052634712777 52172343037524789476034583)
            ·
              refine ⟨78258514556287184214051875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52172343037524789476034583 78258514556287184214051875)
              ·
                refine ⟨117387771834430776321077813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78258514556287184214051875 117387771834430776321077813)
                ·
                  refine ⟨11005103609477885280101045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 117387771834430776321077813 11005103609477885280101045)
                  ·
                    refine ⟨1031728463388551745009473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11005103609477885280101045 1031728463388551745009473)
                    ·
                      rfl

theorem cell23_6027852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 1, 5, 5].length) (baseStart_6027852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6027852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6027852 prefixEnd_6027852 := by exact prefixLift 6027852
  have htrace : WordTrace (prefixWord ++ tailWord_6027852) baseStart_6027852 baseEnd_6027852 := by
    simpa [prefixWord, tailWord_6027852, baseEnd_6027852] using wordTrace_append hprefix tailTrace_6027852
  have hstable : (prefixWord ++ tailWord_6027852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6027852).length < 2 ^ (prefixWord ++ tailWord_6027852).sum := by decide
  have hdescent : baseEnd_6027852 < baseStart_6027852 := by decide
  rcases family_descends (prefixWord ++ tailWord_6027852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6027870 : List Nat := [4, 4, 1, 2, 1, 1, 1, 1, 1, 4, 3]
def baseStart_6027870 : Nat := 118140960795 + 6027870 * 2 ^ 59
def prefixEnd_6027870 : Nat := 4983230072969 + 3 ^ 40 * 6027870 * 2
def baseEnd_6027870 : Nat := 3095194632817436164603337

theorem tailTrace_6027870 : CollatzResearch.WordTrace tailWord_6027870 prefixEnd_6027870 3095194632817436164603337 := by
  unfold tailWord_6027870
  simp only [CollatzResearch.WordTrace]
  refine ⟨27481810084007992885020133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 146569653781375962053440709 27481810084007992885020133)
  ·
    refine ⟨5152839390751498665941275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27481810084007992885020133 5152839390751498665941275)
    ·
      refine ⟨7729259086127247998911913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5152839390751498665941275 7729259086127247998911913)
      ·
        refine ⟨5796944314595435999183935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7729259086127247998911913 5796944314595435999183935)
        ·
          refine ⟨8695416471893153998775903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5796944314595435999183935 8695416471893153998775903)
          ·
            refine ⟨13043124707839730998163855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8695416471893153998775903 13043124707839730998163855)
            ·
              refine ⟨19564687061759596497245783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13043124707839730998163855 19564687061759596497245783)
              ·
                refine ⟨29347030592639394745868675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19564687061759596497245783 29347030592639394745868675)
                ·
                  refine ⟨44020545888959092118803013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29347030592639394745868675 44020545888959092118803013)
                  ·
                    refine ⟨8253852354179829772275565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 44020545888959092118803013 8253852354179829772275565)
                    ·
                      refine ⟨3095194632817436164603337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8253852354179829772275565 3095194632817436164603337)
                      ·
                        rfl

theorem cell23_6027870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 1, 1, 1, 4, 3].length) (baseStart_6027870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6027870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6027870 prefixEnd_6027870 := by exact prefixLift 6027870
  have htrace : WordTrace (prefixWord ++ tailWord_6027870) baseStart_6027870 baseEnd_6027870 := by
    simpa [prefixWord, tailWord_6027870, baseEnd_6027870] using wordTrace_append hprefix tailTrace_6027870
  have hstable : (prefixWord ++ tailWord_6027870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6027870).length < 2 ^ (prefixWord ++ tailWord_6027870).sum := by decide
  have hdescent : baseEnd_6027870 < baseStart_6027870 := by decide
  rcases family_descends (prefixWord ++ tailWord_6027870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6027886 : List Nat := [4, 1, 2, 2, 2, 2, 1, 3, 1, 5]
def baseStart_6027886 : Nat := 118140960795 + 6027886 * 2 ^ 59
def prefixEnd_6027886 : Nat := 4983230072969 + 3 ^ 40 * 6027886 * 2
def baseEnd_6027886 : Nat := 1031734282835969367334421

theorem tailTrace_6027886 : CollatzResearch.WordTrace tailWord_6027886 prefixEnd_6027886 1031734282835969367334421 := by
  unfold tailWord_6027886
  simp only [CollatzResearch.WordTrace]
  refine ⟨27481883030000747226592939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 146570042826670651875162341 27481883030000747226592939)
  ·
    refine ⟨41222824545001120839889409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27481883030000747226592939 41222824545001120839889409)
    ·
      refine ⟨30917118408750840629917057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41222824545001120839889409 30917118408750840629917057)
      ·
        refine ⟨23187838806563130472437793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30917118408750840629917057 23187838806563130472437793)
        ·
          refine ⟨17390879104922347854328345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23187838806563130472437793 17390879104922347854328345)
          ·
            refine ⟨13043159328691760890746259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17390879104922347854328345 13043159328691760890746259)
            ·
              refine ⟨19564738993037641336119389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13043159328691760890746259 19564738993037641336119389)
              ·
                refine ⟨7336777122389115501044771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19564738993037641336119389 7336777122389115501044771)
                ·
                  refine ⟨11005165683583673251567157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7336777122389115501044771 11005165683583673251567157)
                  ·
                    refine ⟨1031734282835969367334421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11005165683583673251567157 1031734282835969367334421)
                    ·
                      rfl

theorem cell23_6027886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 1, 3, 1, 5].length) (baseStart_6027886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6027886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6027886 prefixEnd_6027886 := by exact prefixLift 6027886
  have htrace : WordTrace (prefixWord ++ tailWord_6027886) baseStart_6027886 baseEnd_6027886 := by
    simpa [prefixWord, tailWord_6027886, baseEnd_6027886] using wordTrace_append hprefix tailTrace_6027886
  have hstable : (prefixWord ++ tailWord_6027886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6027886).length < 2 ^ (prefixWord ++ tailWord_6027886).sum := by decide
  have hdescent : baseEnd_6027886 < baseStart_6027886 := by decide
  rcases family_descends (prefixWord ++ tailWord_6027886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6027899 : List Nat := [1, 1, 1, 1, 1, 4, 2, 6, 2, 4]
def baseStart_6027899 : Nat := 118140960795 + 6027899 * 2 ^ 59
def prefixEnd_6027899 : Nat := 4983230072969 + 3 ^ 40 * 6027899 * 2
def baseEnd_6027899 : Nat := 1031736507918805517046901

theorem tailTrace_6027899 : CollatzResearch.WordTrace tailWord_6027899 prefixEnd_6027899 1031736507918805517046901 := by
  unfold tailWord_6027899
  simp only [CollatzResearch.WordTrace]
  refine ⟨219855538388958881032966751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146570358925972587355311167 219855538388958881032966751)
  ·
    refine ⟨329783307583438321549450127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219855538388958881032966751 329783307583438321549450127)
    ·
      refine ⟨494674961375157482324175191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 329783307583438321549450127 494674961375157482324175191)
      ·
        refine ⟨742012442062736223486262787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 494674961375157482324175191 742012442062736223486262787)
        ·
          refine ⟨1113018663094104335229394181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 742012442062736223486262787 1113018663094104335229394181)
          ·
            refine ⟨208690999330144562855511409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1113018663094104335229394181 208690999330144562855511409)
            ·
              refine ⟨156518249497608422141633557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 208690999330144562855511409 156518249497608422141633557)
              ·
                refine ⟨7336792945200394787889073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 156518249497608422141633557 7336792945200394787889073)
                ·
                  refine ⟨5502594708900296090916805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7336792945200394787889073 5502594708900296090916805)
                  ·
                    refine ⟨1031736507918805517046901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5502594708900296090916805 1031736507918805517046901)
                    ·
                      rfl

theorem cell23_6027899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 6, 2, 4].length) (baseStart_6027899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6027899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6027899 prefixEnd_6027899 := by exact prefixLift 6027899
  have htrace : WordTrace (prefixWord ++ tailWord_6027899) baseStart_6027899 baseEnd_6027899 := by
    simpa [prefixWord, tailWord_6027899, baseEnd_6027899] using wordTrace_append hprefix tailTrace_6027899
  have hstable : (prefixWord ++ tailWord_6027899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6027899).length < 2 ^ (prefixWord ++ tailWord_6027899).sum := by decide
  have hdescent : baseEnd_6027899 < baseStart_6027899 := by decide
  rcases family_descends (prefixWord ++ tailWord_6027899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6027909 : List Nat := [1, 3, 1, 1, 4, 3, 1, 2, 1, 1, 5]
def baseStart_6027909 : Nat := 118140960795 + 6027909 * 2 ^ 59
def prefixEnd_6027909 : Nat := 4983230072969 + 3 ^ 40 * 6027909 * 2
def baseEnd_6027909 : Nat := 3095214658562961512015657

theorem tailTrace_6027909 : CollatzResearch.WordTrace tailWord_6027909 prefixEnd_6027909 3095214658562961512015657 := by
  unfold tailWord_6027909
  simp only [CollatzResearch.WordTrace]
  refine ⟨219855903118922652740830781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146570602079281768493887187 219855903118922652740830781)
  ·
    refine ⟨82445963669595994777811543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 219855903118922652740830781 82445963669595994777811543)
    ·
      refine ⟨123668945504393992166717315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82445963669595994777811543 123668945504393992166717315)
      ·
        refine ⟨185503418256590988250075973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123668945504393992166717315 185503418256590988250075973)
        ·
          refine ⟨34781890923110810296889245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 185503418256590988250075973 34781890923110810296889245)
          ·
            refine ⟨13043209096166553861333467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34781890923110810296889245 13043209096166553861333467)
            ·
              refine ⟨19564813644249830792000201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13043209096166553861333467 19564813644249830792000201)
              ·
                refine ⟨14673610233187373094000151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19564813644249830792000201 14673610233187373094000151)
                ·
                  refine ⟨22010415349781059641000227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14673610233187373094000151 22010415349781059641000227)
                  ·
                    refine ⟨33015623024671589461500341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22010415349781059641000227 33015623024671589461500341)
                    ·
                      refine ⟨3095214658562961512015657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33015623024671589461500341 3095214658562961512015657)
                      ·
                        rfl

theorem cell23_6027909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 1, 2, 1, 1, 5].length) (baseStart_6027909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6027909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6027909 prefixEnd_6027909 := by exact prefixLift 6027909
  have htrace : WordTrace (prefixWord ++ tailWord_6027909) baseStart_6027909 baseEnd_6027909 := by
    simpa [prefixWord, tailWord_6027909, baseEnd_6027909] using wordTrace_append hprefix tailTrace_6027909
  have hstable : (prefixWord ++ tailWord_6027909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6027909).length < 2 ^ (prefixWord ++ tailWord_6027909).sum := by decide
  have hdescent : baseEnd_6027909 < baseStart_6027909 := by decide
  rcases family_descends (prefixWord ++ tailWord_6027909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6027943 : List Nat := [1, 1, 6, 3, 1, 1, 2, 1, 1, 1, 5]
def baseStart_6027943 : Nat := 118140960795 + 6027943 * 2 ^ 59
def prefixEnd_6027943 : Nat := 4983230072969 + 3 ^ 40 * 6027943 * 2
def baseEnd_6027943 : Nat := 3095232116905214378990501

theorem tailTrace_6027943 : CollatzResearch.WordTrace tailWord_6027943 prefixEnd_6027943 3095232116905214378990501 := by
  unfold tailWord_6027943
  simp only [CollatzResearch.WordTrace]
  refine ⟨219857143200799476547568483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146571428800532984365045655 219857143200799476547568483)
  ·
    refine ⟨329785714801199214821352725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219857143200799476547568483 329785714801199214821352725)
    ·
      refine ⟨15458705381306213194750909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 329785714801199214821352725 15458705381306213194750909)
      ·
        refine ⟨5797014517989829948031591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15458705381306213194750909 5797014517989829948031591)
        ·
          refine ⟨8695521776984744922047387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5797014517989829948031591 8695521776984744922047387)
          ·
            refine ⟨13043282665477117383071081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8695521776984744922047387 13043282665477117383071081)
            ·
              refine ⟨9782461999107838037303311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13043282665477117383071081 9782461999107838037303311)
              ·
                refine ⟨14673692998661757055954967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9782461999107838037303311 14673692998661757055954967)
                ·
                  refine ⟨22010539497992635583932451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14673692998661757055954967 22010539497992635583932451)
                  ·
                    refine ⟨33015809246988953375898677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22010539497992635583932451 33015809246988953375898677)
                    ·
                      refine ⟨3095232116905214378990501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33015809246988953375898677 3095232116905214378990501)
                      ·
                        rfl

theorem cell23_6027943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 2, 1, 1, 1, 5].length) (baseStart_6027943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6027943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6027943 prefixEnd_6027943 := by exact prefixLift 6027943
  have htrace : WordTrace (prefixWord ++ tailWord_6027943) baseStart_6027943 baseEnd_6027943 := by
    simpa [prefixWord, tailWord_6027943, baseEnd_6027943] using wordTrace_append hprefix tailTrace_6027943
  have hstable : (prefixWord ++ tailWord_6027943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6027943).length < 2 ^ (prefixWord ++ tailWord_6027943).sum := by decide
  have hdescent : baseEnd_6027943 < baseStart_6027943 := by decide
  rcases family_descends (prefixWord ++ tailWord_6027943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6027952 : List Nat := [2, 1, 1, 1, 2, 1, 3, 1, 4, 2, 5]
def baseStart_6027952 : Nat := 118140960795 + 6027952 * 2 ^ 59
def prefixEnd_6027952 : Nat := 4983230072969 + 3 ^ 40 * 6027952 * 2
def baseEnd_6027952 : Nat := 3095236738231104843777959

theorem tailTrace_6027952 : CollatzResearch.WordTrace tailWord_6027952 prefixEnd_6027952 3095236738231104843777959 := by
  unfold tailWord_6027952
  simp only [CollatzResearch.WordTrace]
  refine ⟨109928735728883435542323055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146571647638511247389764073 109928735728883435542323055)
  ·
    refine ⟨164893103593325153313484583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109928735728883435542323055 164893103593325153313484583)
    ·
      refine ⟨247339655389987729970226875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164893103593325153313484583 247339655389987729970226875)
      ·
        refine ⟨371009483084981594955340313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 247339655389987729970226875 371009483084981594955340313)
        ·
          refine ⟨278257112313736196216505235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 371009483084981594955340313 278257112313736196216505235)
          ·
            refine ⟨417385668470604294324757853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 278257112313736196216505235 417385668470604294324757853)
            ·
              refine ⟨156519625676476610371784195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 417385668470604294324757853 156519625676476610371784195)
              ·
                refine ⟨234779438514714915557676293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 156519625676476610371784195 234779438514714915557676293)
                ·
                  refine ⟨44021144721509046667064305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 234779438514714915557676293 44021144721509046667064305)
                  ·
                    refine ⟨33015858541131785000298229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 44021144721509046667064305 33015858541131785000298229)
                    ·
                      refine ⟨3095236738231104843777959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33015858541131785000298229 3095236738231104843777959)
                      ·
                        rfl

theorem cell23_6027952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 4, 2, 5].length) (baseStart_6027952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6027952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6027952 prefixEnd_6027952 := by exact prefixLift 6027952
  have htrace : WordTrace (prefixWord ++ tailWord_6027952) baseStart_6027952 baseEnd_6027952 := by
    simpa [prefixWord, tailWord_6027952, baseEnd_6027952] using wordTrace_append hprefix tailTrace_6027952
  have hstable : (prefixWord ++ tailWord_6027952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6027952).length < 2 ^ (prefixWord ++ tailWord_6027952).sum := by decide
  have hdescent : baseEnd_6027952 < baseStart_6027952 := by decide
  rcases family_descends (prefixWord ++ tailWord_6027952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6027974 : List Nat := [6, 1, 2, 1, 3, 1, 1, 2, 1, 1, 4]
def baseStart_6027974 : Nat := 118140960795 + 6027974 * 2 ^ 59
def prefixEnd_6027974 : Nat := 4983230072969 + 3 ^ 40 * 6027974 * 2
def baseEnd_6027974 : Nat := 3095248034805503757702859

theorem tailTrace_6027974 : CollatzResearch.WordTrace tailWord_6027974 prefixEnd_6027974 3095248034805503757702859 := by
  unfold tailWord_6027974
  simp only [CollatzResearch.WordTrace]
  refine ⟨6870571058240224026310843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 146572182575791445894631317 6870571058240224026310843)
  ·
    refine ⟨10305856587360336039466265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6870571058240224026310843 10305856587360336039466265)
    ·
      refine ⟨7729392440520252029599699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10305856587360336039466265 7729392440520252029599699)
      ·
        refine ⟨11594088660780378044399549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7729392440520252029599699 11594088660780378044399549)
        ·
          refine ⟨4347783247792641766649831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11594088660780378044399549 4347783247792641766649831)
          ·
            refine ⟨6521674871688962649974747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4347783247792641766649831 6521674871688962649974747)
            ·
              refine ⟨9782512307533443974962121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6521674871688962649974747 9782512307533443974962121)
              ·
                refine ⟨7336884230650082981221591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9782512307533443974962121 7336884230650082981221591)
                ·
                  refine ⟨11005326345975124471832387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7336884230650082981221591 11005326345975124471832387)
                  ·
                    refine ⟨16507989518962686707748581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11005326345975124471832387 16507989518962686707748581)
                    ·
                      refine ⟨3095248034805503757702859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16507989518962686707748581 3095248034805503757702859)
                      ·
                        rfl

theorem cell23_6027974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 1, 2, 1, 1, 4].length) (baseStart_6027974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6027974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6027974 prefixEnd_6027974 := by exact prefixLift 6027974
  have htrace : WordTrace (prefixWord ++ tailWord_6027974) baseStart_6027974 baseEnd_6027974 := by
    simpa [prefixWord, tailWord_6027974, baseEnd_6027974] using wordTrace_append hprefix tailTrace_6027974
  have hstable : (prefixWord ++ tailWord_6027974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6027974).length < 2 ^ (prefixWord ++ tailWord_6027974).sum := by decide
  have hdescent : baseEnd_6027974 < baseStart_6027974 := by decide
  rcases family_descends (prefixWord ++ tailWord_6027974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6027999 : List Nat := [1, 1, 2, 3, 2, 3, 2, 1, 2, 1, 5]
def baseStart_6027999 : Nat := 118140960795 + 6027999 * 2 ^ 59
def prefixEnd_6027999 : Nat := 4983230072969 + 3 ^ 40 * 6027999 * 2
def baseEnd_6027999 : Nat := 3095260871821866159890243

theorem tailTrace_6027999 : CollatzResearch.WordTrace tailWord_6027999 prefixEnd_6027999 3095260871821866159890243 := by
  unfold tailWord_6027999
  simp only [CollatzResearch.WordTrace]
  refine ⟨219859185688596598111607051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146572790459064398741071367 219859185688596598111607051)
  ·
    refine ⟨329788778532894897167410577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219859185688596598111607051 329788778532894897167410577)
    ·
      refine ⟨247341583899671172875557933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 329788778532894897167410577 247341583899671172875557933)
      ·
        refine ⟨92753093962376689828334225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 247341583899671172875557933 92753093962376689828334225)
        ·
          refine ⟨69564820471782517371250669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92753093962376689828334225 69564820471782517371250669)
          ·
            refine ⟨26086807676918444014219001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69564820471782517371250669 26086807676918444014219001)
            ·
              refine ⟨19565105757688833010664251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26086807676918444014219001 19565105757688833010664251)
              ·
                refine ⟨29347658636533249515996377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19565105757688833010664251 29347658636533249515996377)
                ·
                  refine ⟨22010743977399937136997283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29347658636533249515996377 22010743977399937136997283)
                  ·
                    refine ⟨33016115966099905705495925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22010743977399937136997283 33016115966099905705495925)
                    ·
                      refine ⟨3095260871821866159890243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33016115966099905705495925 3095260871821866159890243)
                      ·
                        rfl

theorem cell23_6027999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 2, 1, 2, 1, 5].length) (baseStart_6027999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6027999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6027999 prefixEnd_6027999 := by exact prefixLift 6027999
  have htrace : WordTrace (prefixWord ++ tailWord_6027999) baseStart_6027999 baseEnd_6027999 := by
    simpa [prefixWord, tailWord_6027999, baseEnd_6027999] using wordTrace_append hprefix tailTrace_6027999
  have hstable : (prefixWord ++ tailWord_6027999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6027999).length < 2 ^ (prefixWord ++ tailWord_6027999).sum := by decide
  have hdescent : baseEnd_6027999 < baseStart_6027999 := by decide
  rcases family_descends (prefixWord ++ tailWord_6027999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6028030 : List Nat := [4, 2, 2, 1, 2, 2, 2, 1, 1, 4, 2]
def baseStart_6028030 : Nat := 118140960795 + 6028030 * 2 ^ 59
def prefixEnd_6028030 : Nat := 4983230072969 + 3 ^ 40 * 6028030 * 2
def baseEnd_6028030 : Nat := 3095276789722155538602601

theorem tailTrace_6028030 : CollatzResearch.WordTrace tailWord_6028030 prefixEnd_6028030 3095276789722155538602601 := by
  unfold tailWord_6028030
  simp only [CollatzResearch.WordTrace]
  refine ⟨27482539543935536300748193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 146573544234322860270657029 27482539543935536300748193)
  ·
    refine ⟨20611904657951652225561145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27482539543935536300748193 20611904657951652225561145)
    ·
      refine ⟨15458928493463739169170859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20611904657951652225561145 15458928493463739169170859)
      ·
        refine ⟨23188392740195608753756289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15458928493463739169170859 23188392740195608753756289)
        ·
          refine ⟨17391294555146706565317217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23188392740195608753756289 17391294555146706565317217)
          ·
            refine ⟨13043470916360029923987913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17391294555146706565317217 13043470916360029923987913)
            ·
              refine ⟨9782603187270022442990935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13043470916360029923987913 9782603187270022442990935)
              ·
                refine ⟨14673904780905033664486403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9782603187270022442990935 14673904780905033664486403)
                ·
                  refine ⟨22010857171357550496729605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14673904780905033664486403 22010857171357550496729605)
                  ·
                    refine ⟨4127035719629540718136801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22010857171357550496729605 4127035719629540718136801)
                    ·
                      refine ⟨3095276789722155538602601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4127035719629540718136801 3095276789722155538602601)
                      ·
                        rfl

theorem cell23_6028030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 2, 1, 1, 4, 2].length) (baseStart_6028030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6028030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6028030 prefixEnd_6028030 := by exact prefixLift 6028030
  have htrace : WordTrace (prefixWord ++ tailWord_6028030) baseStart_6028030 baseEnd_6028030 := by
    simpa [prefixWord, tailWord_6028030, baseEnd_6028030] using wordTrace_append hprefix tailTrace_6028030
  have hstable : (prefixWord ++ tailWord_6028030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6028030).length < 2 ^ (prefixWord ++ tailWord_6028030).sum := by decide
  have hdescent : baseEnd_6028030 < baseStart_6028030 := by decide
  rcases family_descends (prefixWord ++ tailWord_6028030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6028099 : List Nat := [1, 1, 1, 3, 1, 4, 1, 1, 2, 4, 4]
def baseStart_6028099 : Nat := 118140960795 + 6028099 * 2 ^ 59
def prefixEnd_6028099 : Nat := 4983230072969 + 3 ^ 40 * 6028099 * 2
def baseEnd_6028099 : Nat := 3095312219887315768639783

theorem tailTrace_6028099 : CollatzResearch.WordTrace tailWord_6028099 prefixEnd_6028099 3095312219887315768639783 := by
  unfold tailWord_6028099
  simp only [CollatzResearch.WordTrace]
  refine ⟨219862832988234315190247351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146575221992156210126831567 219862832988234315190247351)
  ·
    refine ⟨329794249482351472785371027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219862832988234315190247351 329794249482351472785371027)
    ·
      refine ⟨494691374223527209178056541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 329794249482351472785371027 494691374223527209178056541)
      ·
        refine ⟨185509265333822703441771203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 494691374223527209178056541 185509265333822703441771203)
        ·
          refine ⟨278263898000734055162656805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185509265333822703441771203 278263898000734055162656805)
          ·
            refine ⟨52174480875137635342998151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 278263898000734055162656805 52174480875137635342998151)
            ·
              refine ⟨78261721312706453014497227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52174480875137635342998151 78261721312706453014497227)
              ·
                refine ⟨117392581969059679521745841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78261721312706453014497227 117392581969059679521745841)
                ·
                  refine ⟨88044436476794759641309381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 117392581969059679521745841 88044436476794759641309381)
                  ·
                    refine ⟨16508331839399017432745509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 88044436476794759641309381 16508331839399017432745509)
                    ·
                      refine ⟨3095312219887315768639783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16508331839399017432745509 3095312219887315768639783)
                      ·
                        rfl

theorem cell23_6028099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 1, 2, 4, 4].length) (baseStart_6028099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6028099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6028099 prefixEnd_6028099 := by exact prefixLift 6028099
  have htrace : WordTrace (prefixWord ++ tailWord_6028099) baseStart_6028099 baseEnd_6028099 := by
    simpa [prefixWord, tailWord_6028099, baseEnd_6028099] using wordTrace_append hprefix tailTrace_6028099
  have hstable : (prefixWord ++ tailWord_6028099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6028099).length < 2 ^ (prefixWord ++ tailWord_6028099).sum := by decide
  have hdescent : baseEnd_6028099 < baseStart_6028099 := by decide
  rcases family_descends (prefixWord ++ tailWord_6028099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6028129 : List Nat := [1, 2, 3, 1, 1, 1, 2, 3, 1, 2, 6]
def baseStart_6028129 : Nat := 118140960795 + 6028129 * 2 ^ 59
def prefixEnd_6028129 : Nat := 4983230072969 + 3 ^ 40 * 6028129 * 2
def baseEnd_6028129 : Nat := 3095327624306950651264645

theorem tailTrace_6028129 : CollatzResearch.WordTrace tailWord_6028129 prefixEnd_6028129 3095327624306950651264645 := by
  unfold tailWord_6028129
  simp only [CollatzResearch.WordTrace]
  refine ⟨219863927178125630313839441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146575951452083753542559627 219863927178125630313839441)
  ·
    refine ⟨164897945383594222735379581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219863927178125630313839441 164897945383594222735379581)
    ·
      refine ⟨61836729518847833525767343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 164897945383594222735379581 61836729518847833525767343)
      ·
        refine ⟨92755094278271750288651015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61836729518847833525767343 92755094278271750288651015)
        ·
          refine ⟨139132641417407625432976523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92755094278271750288651015 139132641417407625432976523)
          ·
            refine ⟨208698962126111438149464785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139132641417407625432976523 208698962126111438149464785)
            ·
              refine ⟨156524221594583578612098589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 208698962126111438149464785 156524221594583578612098589)
              ·
                refine ⟨58696583097968841979536971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 156524221594583578612098589 58696583097968841979536971)
                ·
                  refine ⟨88044874646953262969305457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58696583097968841979536971 88044874646953262969305457)
                  ·
                    refine ⟨66033655985214947226979093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 88044874646953262969305457 66033655985214947226979093)
                    ·
                      refine ⟨3095327624306950651264645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 66033655985214947226979093 3095327624306950651264645)
                      ·
                        rfl

theorem cell23_6028129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 3, 1, 2, 6].length) (baseStart_6028129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6028129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6028129 prefixEnd_6028129 := by exact prefixLift 6028129
  have htrace : WordTrace (prefixWord ++ tailWord_6028129) baseStart_6028129 baseEnd_6028129 := by
    simpa [prefixWord, tailWord_6028129, baseEnd_6028129] using wordTrace_append hprefix tailTrace_6028129
  have hstable : (prefixWord ++ tailWord_6028129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6028129).length < 2 ^ (prefixWord ++ tailWord_6028129).sum := by decide
  have hdescent : baseEnd_6028129 < baseStart_6028129 := by decide
  rcases family_descends (prefixWord ++ tailWord_6028129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6028180 : List Nat := [2, 4, 2, 1, 1, 1, 1, 4, 2, 3, 2]
def baseStart_6028180 : Nat := 118140960795 + 6028180 * 2 ^ 59
def prefixEnd_6028180 : Nat := 4983230072969 + 3 ^ 40 * 6028180 * 2
def baseEnd_6028180 : Nat := 3095353811820329951726911

theorem tailTrace_6028180 : CollatzResearch.WordTrace tailWord_6028180 prefixEnd_6028180 3095353811820329951726911 := by
  unfold tailWord_6028180
  simp only [CollatzResearch.WordTrace]
  refine ⟨109932893650470433011972997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146577191533960577349297329 109932893650470433011972997)
  ·
    refine ⟨20612417559463206189744937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 109932893650470433011972997 20612417559463206189744937)
    ·
      refine ⟨15459313169597404642308703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20612417559463206189744937 15459313169597404642308703)
      ·
        refine ⟨23188969754396106963463055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15459313169597404642308703 23188969754396106963463055)
        ·
          refine ⟨34783454631594160445194583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23188969754396106963463055 34783454631594160445194583)
          ·
            refine ⟨52175181947391240667791875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34783454631594160445194583 52175181947391240667791875)
            ·
              refine ⟨78262772921086861001687813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52175181947391240667791875 78262772921086861001687813)
              ·
                refine ⟨14674269922703786437816465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 78262772921086861001687813 14674269922703786437816465)
                ·
                  refine ⟨11005702442027839828362349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14674269922703786437816465 11005702442027839828362349)
                  ·
                    refine ⟨4127138415760439935635881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11005702442027839828362349 4127138415760439935635881)
                    ·
                      refine ⟨3095353811820329951726911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4127138415760439935635881 3095353811820329951726911)
                      ·
                        rfl

theorem cell23_6028180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 4, 2, 3, 2].length) (baseStart_6028180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6028180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6028180 prefixEnd_6028180 := by exact prefixLift 6028180
  have htrace : WordTrace (prefixWord ++ tailWord_6028180) baseStart_6028180 baseEnd_6028180 := by
    simpa [prefixWord, tailWord_6028180, baseEnd_6028180] using wordTrace_append hprefix tailTrace_6028180
  have hstable : (prefixWord ++ tailWord_6028180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6028180).length < 2 ^ (prefixWord ++ tailWord_6028180).sum := by decide
  have hdescent : baseEnd_6028180 < baseStart_6028180 := by decide
  rcases family_descends (prefixWord ++ tailWord_6028180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6028193 : List Nat := [1, 2, 3, 4, 1, 1, 1, 2, 3, 1, 4]
def baseStart_6028193 : Nat := 118140960795 + 6028193 * 2 ^ 59
def prefixEnd_6028193 : Nat := 4983230072969 + 3 ^ 40 * 6028193 * 2
def baseEnd_6028193 : Nat := 3095360487068838400864351

theorem tailTrace_6028193 : CollatzResearch.WordTrace tailWord_6028193 prefixEnd_6028193 3095360487068838400864351 := by
  unfold tailWord_6028193
  simp only [CollatzResearch.WordTrace]
  refine ⟨219866261449893769244169233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146577507633262512829446155 219866261449893769244169233)
  ·
    refine ⟨164899696087420326933126925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219866261449893769244169233 164899696087420326933126925)
    ·
      refine ⟨61837386032782622599922597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 164899696087420326933126925 61837386032782622599922597)
      ·
        refine ⟨11594509881146741737485487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61837386032782622599922597 11594509881146741737485487)
        ·
          refine ⟨17391764821720112606228231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11594509881146741737485487 17391764821720112606228231)
          ·
            refine ⟨26087647232580168909342347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17391764821720112606228231 26087647232580168909342347)
            ·
              refine ⟨39131470848870253364013521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26087647232580168909342347 39131470848870253364013521)
              ·
                refine ⟨29348603136652690023010141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39131470848870253364013521 29348603136652690023010141)
                ·
                  refine ⟨11005726176244758758628803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29348603136652690023010141 11005726176244758758628803)
                  ·
                    refine ⟨16508589264367138137943205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11005726176244758758628803 16508589264367138137943205)
                    ·
                      refine ⟨3095360487068838400864351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16508589264367138137943205 3095360487068838400864351)
                      ·
                        rfl

theorem cell23_6028193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_6028193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6028193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6028193 prefixEnd_6028193 := by exact prefixLift 6028193
  have htrace : WordTrace (prefixWord ++ tailWord_6028193) baseStart_6028193 baseEnd_6028193 := by
    simpa [prefixWord, tailWord_6028193, baseEnd_6028193] using wordTrace_append hprefix tailTrace_6028193
  have hstable : (prefixWord ++ tailWord_6028193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6028193).length < 2 ^ (prefixWord ++ tailWord_6028193).sum := by decide
  have hdescent : baseEnd_6028193 < baseStart_6028193 := by decide
  rcases family_descends (prefixWord ++ tailWord_6028193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6028196 : List Nat := [2, 3, 1, 2, 1, 2, 2, 1, 3, 1, 5]
def baseStart_6028196 : Nat := 118140960795 + 6028196 * 2 ^ 59
def prefixEnd_6028196 : Nat := 4983230072969 + 3 ^ 40 * 6028196 * 2
def baseEnd_6028196 : Nat := 3095362027510801889126837

theorem tailTrace_6028196 : CollatzResearch.WordTrace tailWord_6028196 prefixEnd_6028196 3095362027510801889126837 := by
  unfold tailWord_6028196
  simp only [CollatzResearch.WordTrace]
  refine ⟨109933185434441450378264221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146577580579255267171018961 109933185434441450378264221)
  ·
    refine ⟨41224944537915543891849083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109933185434441450378264221 41224944537915543891849083)
    ·
      refine ⟨61837416806873315837773625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41224944537915543891849083 61837416806873315837773625)
      ·
        refine ⟨46378062605154986878330219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61837416806873315837773625 46378062605154986878330219)
        ·
          refine ⟨69567093907732480317495329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46378062605154986878330219 69567093907732480317495329)
          ·
            refine ⟨52175320430799360238121497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69567093907732480317495329 52175320430799360238121497)
            ·
              refine ⟨39131490323099520178591123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52175320430799360238121497 39131490323099520178591123)
              ·
                refine ⟨58697235484649280267886685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39131490323099520178591123 58697235484649280267886685)
                ·
                  refine ⟨22011463306743480100457507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58697235484649280267886685 22011463306743480100457507)
                  ·
                    refine ⟨33017194960115220150686261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22011463306743480100457507 33017194960115220150686261)
                    ·
                      refine ⟨3095362027510801889126837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33017194960115220150686261 3095362027510801889126837)
                      ·
                        rfl

theorem cell23_6028196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 1, 3, 1, 5].length) (baseStart_6028196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6028196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6028196 prefixEnd_6028196 := by exact prefixLift 6028196
  have htrace : WordTrace (prefixWord ++ tailWord_6028196) baseStart_6028196 baseEnd_6028196 := by
    simpa [prefixWord, tailWord_6028196, baseEnd_6028196] using wordTrace_append hprefix tailTrace_6028196
  have hstable : (prefixWord ++ tailWord_6028196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6028196).length < 2 ^ (prefixWord ++ tailWord_6028196).sum := by decide
  have hdescent : baseEnd_6028196 < baseStart_6028196 := by decide
  rcases family_descends (prefixWord ++ tailWord_6028196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6028213 : List Nat := [1, 3, 3, 2, 1, 1, 1, 3, 3, 2, 3]
def baseStart_6028213 : Nat := 118140960795 + 6028213 * 2 ^ 59
def prefixEnd_6028213 : Nat := 4983230072969 + 3 ^ 40 * 6028213 * 2
def baseEnd_6028213 : Nat := 3095370756681928322614259

theorem tailTrace_6028213 : CollatzResearch.WordTrace tailWord_6028213 prefixEnd_6028213 3095370756681928322614259 := by
  unfold tailWord_6028213
  simp only [CollatzResearch.WordTrace]
  refine ⟨219866990909821312659897293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146577993939880875106598195 219866990909821312659897293)
  ·
    refine ⟨82450121591182992247461485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 219866990909821312659897293 82450121591182992247461485)
    ·
      refine ⟨30918795596693622092798057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82450121591182992247461485 30918795596693622092798057)
      ·
        refine ⟨23189096697520216569598543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30918795596693622092798057 23189096697520216569598543)
        ·
          refine ⟨34783645046280324854397815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23189096697520216569598543 34783645046280324854397815)
          ·
            refine ⟨52175467569420487281596723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34783645046280324854397815 52175467569420487281596723)
            ·
              refine ⟨78263201354130730922395085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52175467569420487281596723 78263201354130730922395085)
              ·
                refine ⟨29348700507799024095898157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78263201354130730922395085 29348700507799024095898157)
                ·
                  refine ⟨11005762690424634035961809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29348700507799024095898157 11005762690424634035961809)
                  ·
                    refine ⟨8254322017818475526971357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11005762690424634035961809 8254322017818475526971357)
                    ·
                      refine ⟨3095370756681928322614259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8254322017818475526971357 3095370756681928322614259)
                      ·
                        rfl

theorem cell23_6028213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 3, 3, 2, 3].length) (baseStart_6028213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6028213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6028213 prefixEnd_6028213 := by exact prefixLift 6028213
  have htrace : WordTrace (prefixWord ++ tailWord_6028213) baseStart_6028213 baseEnd_6028213 := by
    simpa [prefixWord, tailWord_6028213, baseEnd_6028213] using wordTrace_append hprefix tailTrace_6028213
  have hstable : (prefixWord ++ tailWord_6028213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6028213).length < 2 ^ (prefixWord ++ tailWord_6028213).sum := by decide
  have hdescent : baseEnd_6028213 < baseStart_6028213 := by decide
  rcases family_descends (prefixWord ++ tailWord_6028213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6028244 : List Nat := [2, 4, 1, 2, 1, 2, 2, 4, 1, 2, 2]
def baseStart_6028244 : Nat := 118140960795 + 6028244 * 2 ^ 59
def prefixEnd_6028244 : Nat := 4983230072969 + 3 ^ 40 * 6028244 * 2
def baseEnd_6028244 : Nat := 3095386674582217701326617

theorem tailTrace_6028244 : CollatzResearch.WordTrace tailWord_6028244 prefixEnd_6028244 3095386674582217701326617 := by
  unfold tailWord_6028244
  simp only [CollatzResearch.WordTrace]
  refine ⟨109934060786354502477137893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146578747715139336636183857 109934060786354502477137893)
  ·
    refine ⟨20612636397441469214463355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 109934060786354502477137893 20612636397441469214463355)
    ·
      refine ⟨30918954596162203821695033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20612636397441469214463355 30918954596162203821695033)
      ·
        refine ⟨23189215947121652866271275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30918954596162203821695033 23189215947121652866271275)
        ·
          refine ⟨34783823920682479299406913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23189215947121652866271275 34783823920682479299406913)
          ·
            refine ⟨26087867940511859474555185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34783823920682479299406913 26087867940511859474555185)
            ·
              refine ⟨19565900955383894605916389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26087867940511859474555185 19565900955383894605916389)
              ·
                refine ⟨3668606429134480238609323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19565900955383894605916389 3668606429134480238609323)
                ·
                  refine ⟨5502909643701720357913985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3668606429134480238609323 5502909643701720357913985)
                  ·
                    refine ⟨4127182232776290268435489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5502909643701720357913985 4127182232776290268435489)
                    ·
                      refine ⟨3095386674582217701326617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4127182232776290268435489 3095386674582217701326617)
                      ·
                        rfl

theorem cell23_6028244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 4, 1, 2, 2].length) (baseStart_6028244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6028244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6028244 prefixEnd_6028244 := by exact prefixLift 6028244
  have htrace : WordTrace (prefixWord ++ tailWord_6028244) baseStart_6028244 baseEnd_6028244 := by
    simpa [prefixWord, tailWord_6028244, baseEnd_6028244] using wordTrace_append hprefix tailTrace_6028244
  have hstable : (prefixWord ++ tailWord_6028244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6028244).length < 2 ^ (prefixWord ++ tailWord_6028244).sum := by decide
  have hdescent : baseEnd_6028244 < baseStart_6028244 := by decide
  rcases family_descends (prefixWord ++ tailWord_6028244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6028283 : List Nat := [1, 1, 1, 1, 1, 3, 3, 3, 3, 4, 2]
def baseStart_6028283 : Nat := 118140960795 + 6028283 * 2 ^ 59
def prefixEnd_6028283 : Nat := 4983230072969 + 3 ^ 40 * 6028283 * 2
def baseEnd_6028283 : Nat := 3095406700327743048738937

theorem tailTrace_6028283 : CollatzResearch.WordTrace tailWord_6028283 prefixEnd_6028283 3095406700327743048738937 := by
  unfold tailWord_6028283
  simp only [CollatzResearch.WordTrace]
  refine ⟨219869544019567714614945503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146579696013045143076630335 219869544019567714614945503)
  ·
    refine ⟨329804316029351571922418255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219869544019567714614945503 329804316029351571922418255)
    ·
      refine ⟨494706474044027357883627383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 329804316029351571922418255 494706474044027357883627383)
      ·
        refine ⟨742059711066041036825441075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 494706474044027357883627383 742059711066041036825441075)
        ·
          refine ⟨1113089566599061555238161613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 742059711066041036825441075 1113089566599061555238161613)
          ·
            refine ⟨417408587474648083214310605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1113089566599061555238161613 417408587474648083214310605)
            ·
              refine ⟨156528220302993031205366477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 417408587474648083214310605 156528220302993031205366477)
              ·
                refine ⟨58698082613622386702012429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 156528220302993031205366477 58698082613622386702012429)
                ·
                  refine ⟨22011780980108395013254661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58698082613622386702012429 22011780980108395013254661)
                  ·
                    refine ⟨4127208933770324064985249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22011780980108395013254661 4127208933770324064985249)
                    ·
                      refine ⟨3095406700327743048738937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4127208933770324064985249 3095406700327743048738937)
                      ·
                        rfl

theorem cell23_6028283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 3, 4, 2].length) (baseStart_6028283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6028283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6028283 prefixEnd_6028283 := by exact prefixLift 6028283
  have htrace : WordTrace (prefixWord ++ tailWord_6028283) baseStart_6028283 baseEnd_6028283 := by
    simpa [prefixWord, tailWord_6028283, baseEnd_6028283] using wordTrace_append hprefix tailTrace_6028283
  have hstable : (prefixWord ++ tailWord_6028283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6028283).length < 2 ^ (prefixWord ++ tailWord_6028283).sum := by decide
  have hdescent : baseEnd_6028283 < baseStart_6028283 := by decide
  rcases family_descends (prefixWord ++ tailWord_6028283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6028373 : List Nat := [1, 3, 2, 2, 1, 2, 2, 2, 1, 3, 4]
def baseStart_6028373 : Nat := 118140960795 + 6028373 * 2 ^ 59
def prefixEnd_6028373 : Nat := 4983230072969 + 3 ^ 40 * 6028373 * 2
def baseEnd_6028373 : Nat := 3095452913586647696613523

theorem tailTrace_6028373 : CollatzResearch.WordTrace tailWord_6028373 prefixEnd_6028373 3095452913586647696613523 := by
  unfold tailWord_6028373
  simp only [CollatzResearch.WordTrace]
  refine ⟨219872826589241659985721773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146581884392827773323814515 219872826589241659985721773)
  ·
    refine ⟨82452309970965622494645665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 219872826589241659985721773 82452309970965622494645665)
    ·
      refine ⟨61839232478224216870984249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82452309970965622494645665 61839232478224216870984249)
      ·
        refine ⟨46379424358668162653238187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61839232478224216870984249 46379424358668162653238187)
        ·
          refine ⟨69569136538002243979857281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46379424358668162653238187 69569136538002243979857281)
          ·
            refine ⟨52176852403501682984892961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69569136538002243979857281 52176852403501682984892961)
            ·
              refine ⟨39132639302626262238669721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52176852403501682984892961 39132639302626262238669721)
              ·
                refine ⟨29349479476969696679002291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39132639302626262238669721 29349479476969696679002291)
                ·
                  refine ⟨44024219215454545018503437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29349479476969696679002291 44024219215454545018503437)
                  ·
                    refine ⟨16509082205795454381938789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 44024219215454545018503437 16509082205795454381938789)
                    ·
                      refine ⟨3095452913586647696613523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16509082205795454381938789 3095452913586647696613523)
                      ·
                        rfl

theorem cell23_6028373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 2, 1, 3, 4].length) (baseStart_6028373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6028373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6028373 prefixEnd_6028373 := by exact prefixLift 6028373
  have htrace : WordTrace (prefixWord ++ tailWord_6028373) baseStart_6028373 baseEnd_6028373 := by
    simpa [prefixWord, tailWord_6028373, baseEnd_6028373] using wordTrace_append hprefix tailTrace_6028373
  have hstable : (prefixWord ++ tailWord_6028373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6028373).length < 2 ^ (prefixWord ++ tailWord_6028373).sum := by decide
  have hdescent : baseEnd_6028373 < baseStart_6028373 := by decide
  rcases family_descends (prefixWord ++ tailWord_6028373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6028413 : List Nat := [1, 4, 1, 1, 3, 1, 3, 1, 8]
def baseStart_6028413 : Nat := 118140960795 + 6028413 * 2 ^ 59
def prefixEnd_6028413 : Nat := 4983230072969 + 3 ^ 40 * 6028413 * 2
def baseEnd_6028413 : Nat := 343941494756980837790371

theorem tailTrace_6028413 : CollatzResearch.WordTrace tailWord_6028413 prefixEnd_6028413 343941494756980837790371 := by
  unfold tailWord_6028413
  simp only [CollatzResearch.WordTrace]
  refine ⟨219874285509096746817177893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146582857006064497878118595 219874285509096746817177893)
  ·
    refine ⟨41226428532955640028220855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 219874285509096746817177893 41226428532955640028220855)
    ·
      refine ⟨61839642799433460042331283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41226428532955640028220855 61839642799433460042331283)
      ·
        refine ⟨92759464199150190063496925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61839642799433460042331283 92759464199150190063496925)
        ·
          refine ⟨34784799074681321273811347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92759464199150190063496925 34784799074681321273811347)
          ·
            refine ⟨52177198612021981910717021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34784799074681321273811347 52177198612021981910717021)
            ·
              refine ⟨19566449479508243216518883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52177198612021981910717021 19566449479508243216518883)
              ·
                refine ⟨29349674219262364824778325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19566449479508243216518883 29349674219262364824778325)
                ·
                  refine ⟨343941494756980837790371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 29349674219262364824778325 343941494756980837790371)
                  ·
                    rfl

theorem cell23_6028413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 3, 1, 8].length) (baseStart_6028413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6028413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6028413 prefixEnd_6028413 := by exact prefixLift 6028413
  have htrace : WordTrace (prefixWord ++ tailWord_6028413) baseStart_6028413 baseEnd_6028413 := by
    simpa [prefixWord, tailWord_6028413, baseEnd_6028413] using wordTrace_append hprefix tailTrace_6028413
  have hstable : (prefixWord ++ tailWord_6028413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6028413).length < 2 ^ (prefixWord ++ tailWord_6028413).sum := by decide
  have hdescent : baseEnd_6028413 < baseStart_6028413 := by decide
  rcases family_descends (prefixWord ++ tailWord_6028413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6028417 : List Nat := [1, 2, 4, 2, 2, 2, 2, 1, 3, 4]
def baseStart_6028417 : Nat := 118140960795 + 6028417 * 2 ^ 59
def prefixEnd_6028417 : Nat := 4983230072969 + 3 ^ 40 * 6028417 * 2
def baseEnd_6028417 : Nat := 1031825168911815174821107

theorem tailTrace_6028417 : CollatzResearch.WordTrace tailWord_6028417 prefixEnd_6028417 1031825168911815174821107 := by
  unfold tailWord_6028417
  simp only [CollatzResearch.WordTrace]
  refine ⟨219874431401082255500323505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146582954267388170333549003 219874431401082255500323505)
  ·
    refine ⟨164905823550811691625242629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219874431401082255500323505 164905823550811691625242629)
    ·
      refine ⟨30919841915777192179732993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 164905823550811691625242629 30919841915777192179732993)
      ·
        refine ⟨23189881436832894134799745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30919841915777192179732993 23189881436832894134799745)
        ·
          refine ⟨17392411077624670601099809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23189881436832894134799745 17392411077624670601099809)
          ·
            refine ⟨13044308308218502950824857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17392411077624670601099809 13044308308218502950824857)
            ·
              refine ⟨9783231231163877213118643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13044308308218502950824857 9783231231163877213118643)
              ·
                refine ⟨14674846846745815819677965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9783231231163877213118643 14674846846745815819677965)
                ·
                  refine ⟨5503067567529680932379237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14674846846745815819677965 5503067567529680932379237)
                  ·
                    refine ⟨1031825168911815174821107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5503067567529680932379237 1031825168911815174821107)
                    ·
                      rfl

theorem cell23_6028417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 2, 1, 3, 4].length) (baseStart_6028417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6028417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6028417 prefixEnd_6028417 := by exact prefixLift 6028417
  have htrace : WordTrace (prefixWord ++ tailWord_6028417) baseStart_6028417 baseEnd_6028417 := by
    simpa [prefixWord, tailWord_6028417, baseEnd_6028417] using wordTrace_append hprefix tailTrace_6028417
  have hstable : (prefixWord ++ tailWord_6028417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6028417).length < 2 ^ (prefixWord ++ tailWord_6028417).sum := by decide
  have hdescent : baseEnd_6028417 < baseStart_6028417 := by decide
  rcases family_descends (prefixWord ++ tailWord_6028417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6028483 : List Nat := [1, 1, 1, 3, 1, 1, 1, 5, 3, 1, 5]
def baseStart_6028483 : Nat := 118140960795 + 6028483 * 2 ^ 59
def prefixEnd_6028483 : Nat := 4983230072969 + 3 ^ 40 * 6028483 * 2
def baseEnd_6028483 : Nat := 3095509396458642266238017

theorem tailTrace_6028483 : CollatzResearch.WordTrace tailWord_6028483 prefixEnd_6028483 3095509396458642266238017 := by
  unfold tailWord_6028483
  simp only [CollatzResearch.WordTrace]
  refine ⟨219876838618843148772226103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146584559079228765848150735 219876838618843148772226103)
  ·
    refine ⟨329815257928264723158339155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219876838618843148772226103 329815257928264723158339155)
    ·
      refine ⟨494722886892397084737508733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 329815257928264723158339155 494722886892397084737508733)
      ·
        refine ⟨185521082584648906776565775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 494722886892397084737508733 185521082584648906776565775)
        ·
          refine ⟨278281623876973360164848663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185521082584648906776565775 278281623876973360164848663)
          ·
            refine ⟨417422435815460040247272995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 278281623876973360164848663 417422435815460040247272995)
            ·
              refine ⟨626133653723190060370909493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 417422435815460040247272995 626133653723190060370909493)
              ·
                refine ⟨58700030036549068159772765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 626133653723190060370909493 58700030036549068159772765)
                ·
                  refine ⟨22012511263705900559914787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58700030036549068159772765 22012511263705900559914787)
                  ·
                    refine ⟨33018766895558850839872181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22012511263705900559914787 33018766895558850839872181)
                    ·
                      refine ⟨3095509396458642266238017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33018766895558850839872181 3095509396458642266238017)
                      ·
                        rfl

theorem cell23_6028483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 5, 3, 1, 5].length) (baseStart_6028483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6028483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6028483 prefixEnd_6028483 := by exact prefixLift 6028483
  have htrace : WordTrace (prefixWord ++ tailWord_6028483) baseStart_6028483 baseEnd_6028483 := by
    simpa [prefixWord, tailWord_6028483, baseEnd_6028483] using wordTrace_append hprefix tailTrace_6028483
  have hstable : (prefixWord ++ tailWord_6028483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6028483).length < 2 ^ (prefixWord ++ tailWord_6028483).sum := by decide
  have hdescent : baseEnd_6028483 < baseStart_6028483 := by decide
  rcases family_descends (prefixWord ++ tailWord_6028483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6028494 : List Nat := [4, 1, 1, 1, 5, 2, 1, 2, 1, 5]
def baseStart_6028494 : Nat := 118140960795 + 6028494 * 2 ^ 59
def prefixEnd_6028494 : Nat := 4983230072969 + 3 ^ 40 * 6028494 * 2
def baseEnd_6028494 : Nat := 1031838348248613907733489

theorem tailTrace_6028494 : CollatzResearch.WordTrace tailWord_6028494 prefixEnd_6028494 1031838348248613907733489 := by
  unfold tailWord_6028494
  simp only [CollatzResearch.WordTrace]
  refine ⟨27484654977725412206359567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 146584826547868865100584357 27484654977725412206359567)
  ·
    refine ⟨41226982466588118309539351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27484654977725412206359567 41226982466588118309539351)
    ·
      refine ⟨61840473699882177464309027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41226982466588118309539351 61840473699882177464309027)
      ·
        refine ⟨92760710549823266196463541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61840473699882177464309027 92760710549823266196463541)
        ·
          refine ⟨8696316614045931205918457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 92760710549823266196463541 8696316614045931205918457)
          ·
            refine ⟨6522237460534448404438843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8696316614045931205918457 6522237460534448404438843)
            ·
              refine ⟨9783356190801672606658265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6522237460534448404438843 9783356190801672606658265)
              ·
                refine ⟨7337517143101254454993699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9783356190801672606658265 7337517143101254454993699)
                ·
                  refine ⟨11006275714651881682490549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7337517143101254454993699 11006275714651881682490549)
                  ·
                    refine ⟨1031838348248613907733489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11006275714651881682490549 1031838348248613907733489)
                    ·
                      rfl

theorem cell23_6028494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 1, 2, 1, 5].length) (baseStart_6028494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6028494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6028494 prefixEnd_6028494 := by exact prefixLift 6028494
  have htrace : WordTrace (prefixWord ++ tailWord_6028494) baseStart_6028494 baseEnd_6028494 := by
    simpa [prefixWord, tailWord_6028494, baseEnd_6028494] using wordTrace_append hprefix tailTrace_6028494
  have hstable : (prefixWord ++ tailWord_6028494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6028494).length < 2 ^ (prefixWord ++ tailWord_6028494).sum := by decide
  have hdescent : baseEnd_6028494 < baseStart_6028494 := by decide
  rcases family_descends (prefixWord ++ tailWord_6028494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6028497 : List Nat := [1, 2, 2, 1, 2, 2, 1, 3, 5, 2, 2]
def baseStart_6028497 : Nat := 118140960795 + 6028497 * 2 ^ 59
def prefixEnd_6028497 : Nat := 4983230072969 + 3 ^ 40 * 6028497 * 2
def baseEnd_6028497 : Nat := 3095516585187805211462953

theorem tailTrace_6028497 : CollatzResearch.WordTrace tailWord_6028497 prefixEnd_6028497 3095516585187805211462953 := by
  unfold tailWord_6028497
  simp only [CollatzResearch.WordTrace]
  refine ⟨219877349240792429163235745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146584899493861619442157163 219877349240792429163235745)
  ·
    refine ⟨164908011930594321872426809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219877349240792429163235745 164908011930594321872426809)
    ·
      refine ⟨123681008947945741404320107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164908011930594321872426809 123681008947945741404320107)
      ·
        refine ⟨185521513421918612106480161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123681008947945741404320107 185521513421918612106480161)
        ·
          refine ⟨139141135066438959079860121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 185521513421918612106480161 139141135066438959079860121)
          ·
            refine ⟨104355851299829219309895091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 139141135066438959079860121 104355851299829219309895091)
            ·
              refine ⟨156533776949743828964842637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104355851299829219309895091 156533776949743828964842637)
              ·
                refine ⟨58700166356153935861815989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 156533776949743828964842637 58700166356153935861815989)
                ·
                  refine ⟨5503140595889431487045249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 58700166356153935861815989 5503140595889431487045249)
                  ·
                    refine ⟨4127355446917073615283937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5503140595889431487045249 4127355446917073615283937)
                    ·
                      refine ⟨3095516585187805211462953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4127355446917073615283937 3095516585187805211462953)
                      ·
                        rfl

theorem cell23_6028497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 3, 5, 2, 2].length) (baseStart_6028497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6028497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6028497 prefixEnd_6028497 := by exact prefixLift 6028497
  have htrace : WordTrace (prefixWord ++ tailWord_6028497) baseStart_6028497 baseEnd_6028497 := by
    simpa [prefixWord, tailWord_6028497, baseEnd_6028497] using wordTrace_append hprefix tailTrace_6028497
  have hstable : (prefixWord ++ tailWord_6028497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6028497).length < 2 ^ (prefixWord ++ tailWord_6028497).sum := by decide
  have hdescent : baseEnd_6028497 < baseStart_6028497 := by decide
  rcases family_descends (prefixWord ++ tailWord_6028497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6028503 : List Nat := [1, 1, 3, 2, 1, 2, 4, 9]
def baseStart_6028503 : Nat := 118140960795 + 6028503 * 2 ^ 59
def prefixEnd_6028503 : Nat := 4983230072969 + 3 ^ 40 * 6028503 * 2
def baseEnd_6028503 : Nat := 114648876521175266221775

theorem tailTrace_6028503 : CollatzResearch.WordTrace tailWord_6028503 prefixEnd_6028503 114648876521175266221775 := by
  unfold tailWord_6028503
  simp only [CollatzResearch.WordTrace]
  refine ⟨219877568078770692187954163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146585045385847128125302775 219877568078770692187954163)
  ·
    refine ⟨329816352118156038281931245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219877568078770692187954163 329816352118156038281931245)
    ·
      refine ⟨123681132044308514355724217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 329816352118156038281931245 123681132044308514355724217)
      ·
        refine ⟨92760849033231385766793163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123681132044308514355724217 92760849033231385766793163)
        ·
          refine ⟨139141273549847078650189745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92760849033231385766793163 139141273549847078650189745)
          ·
            refine ⟨104355955162385308987642309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 139141273549847078650189745 104355955162385308987642309)
            ·
              refine ⟨19566741592947245435182933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 104355955162385308987642309 19566741592947245435182933)
              ·
                refine ⟨114648876521175266221775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 19566741592947245435182933 114648876521175266221775)
                ·
                  rfl

theorem cell23_6028503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4, 9].length) (baseStart_6028503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6028503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6028503 prefixEnd_6028503 := by exact prefixLift 6028503
  have htrace : WordTrace (prefixWord ++ tailWord_6028503) baseStart_6028503 baseEnd_6028503 := by
    simpa [prefixWord, tailWord_6028503, baseEnd_6028503] using wordTrace_append hprefix tailTrace_6028503
  have hstable : (prefixWord ++ tailWord_6028503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6028503).length < 2 ^ (prefixWord ++ tailWord_6028503).sum := by decide
  have hdescent : baseEnd_6028503 < baseStart_6028503 := by decide
  rcases family_descends (prefixWord ++ tailWord_6028503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6028531 : List Nat := [1, 1, 1, 2, 2, 6, 1, 4, 1, 2, 2]
def baseStart_6028531 : Nat := 118140960795 + 6028531 * 2 ^ 59
def prefixEnd_6028531 : Nat := 4983230072969 + 3 ^ 40 * 6028531 * 2
def baseEnd_6028531 : Nat := 3095534043530058078437797

theorem tailTrace_6028531 : CollatzResearch.WordTrace tailWord_6028531 prefixEnd_6028531 3095534043530058078437797 := by
  unfold tailWord_6028531
  simp only [CollatzResearch.WordTrace]
  refine ⟨219878589322669252969973447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146585726215112835313315631 219878589322669252969973447)
  ·
    refine ⟨329817883984003879454960171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219878589322669252969973447 329817883984003879454960171)
    ·
      refine ⟨494726825976005819182440257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 329817883984003879454960171 494726825976005819182440257)
      ·
        refine ⟨371045119482004364386830193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 494726825976005819182440257 371045119482004364386830193)
        ·
          refine ⟨278283839611503273290122645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 371045119482004364386830193 278283839611503273290122645)
          ·
            refine ⟨13044554981789215935474499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 278283839611503273290122645 13044554981789215935474499)
            ·
              refine ⟨19566832472683823903211749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13044554981789215935474499 19566832472683823903211749)
              ·
                refine ⟨3668781088628216981852203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19566832472683823903211749 3668781088628216981852203)
                ·
                  refine ⟨5503171632942325472778305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3668781088628216981852203 5503171632942325472778305)
                  ·
                    refine ⟨4127378724706744104583729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5503171632942325472778305 4127378724706744104583729)
                    ·
                      refine ⟨3095534043530058078437797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4127378724706744104583729 3095534043530058078437797)
                      ·
                        rfl

theorem cell23_6028531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 1, 4, 1, 2, 2].length) (baseStart_6028531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6028531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6028531 prefixEnd_6028531 := by exact prefixLift 6028531
  have htrace : WordTrace (prefixWord ++ tailWord_6028531) baseStart_6028531 baseEnd_6028531 := by
    simpa [prefixWord, tailWord_6028531, baseEnd_6028531] using wordTrace_append hprefix tailTrace_6028531
  have hstable : (prefixWord ++ tailWord_6028531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6028531).length < 2 ^ (prefixWord ++ tailWord_6028531).sum := by decide
  have hdescent : baseEnd_6028531 < baseStart_6028531 := by decide
  rcases family_descends (prefixWord ++ tailWord_6028531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6028547 : List Nat := [1, 1, 1, 3, 2, 5, 2, 1, 1, 3, 3]
def baseStart_6028547 : Nat := 118140960795 + 6028547 * 2 ^ 59
def prefixEnd_6028547 : Nat := 4983230072969 + 3 ^ 40 * 6028547 * 2
def baseEnd_6028547 : Nat := 3095542259220530015837723

theorem tailTrace_6028547 : CollatzResearch.WordTrace tailWord_6028547 prefixEnd_6028547 3095542259220530015837723 := by
  unfold tailWord_6028547
  simp only [CollatzResearch.WordTrace]
  refine ⟨219879172890611287702555895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146586115260407525135037263 219879172890611287702555895)
  ·
    refine ⟨329818759335916931553833843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219879172890611287702555895 329818759335916931553833843)
    ·
      refine ⟨494728139003875397330750765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 329818759335916931553833843 494728139003875397330750765)
      ·
        refine ⟨185523052126453273999031537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 494728139003875397330750765 185523052126453273999031537)
        ·
          refine ⟨139142289094839955499273653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 185523052126453273999031537 139142289094839955499273653)
          ·
            refine ⟨13044589602641245828056905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 139142289094839955499273653 13044589602641245828056905)
            ·
              refine ⟨9783442201980934371042679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13044589602641245828056905 9783442201980934371042679)
              ·
                refine ⟨14675163302971401556564019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9783442201980934371042679 14675163302971401556564019)
                ·
                  refine ⟨22012744954457102334846029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14675163302971401556564019 22012744954457102334846029)
                  ·
                    refine ⟨8254779357921413375567261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22012744954457102334846029 8254779357921413375567261)
                    ·
                      refine ⟨3095542259220530015837723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8254779357921413375567261 3095542259220530015837723)
                      ·
                        rfl

theorem cell23_6028547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 2, 1, 1, 3, 3].length) (baseStart_6028547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6028547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6028547 prefixEnd_6028547 := by exact prefixLift 6028547
  have htrace : WordTrace (prefixWord ++ tailWord_6028547) baseStart_6028547 baseEnd_6028547 := by
    simpa [prefixWord, tailWord_6028547, baseEnd_6028547] using wordTrace_append hprefix tailTrace_6028547
  have hstable : (prefixWord ++ tailWord_6028547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6028547).length < 2 ^ (prefixWord ++ tailWord_6028547).sum := by decide
  have hdescent : baseEnd_6028547 < baseStart_6028547 := by decide
  rcases family_descends (prefixWord ++ tailWord_6028547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6028580 : List Nat := [2, 3, 1, 3, 1, 1, 1, 1, 4, 6]
def baseStart_6028580 : Nat := 118140960795 + 6028580 * 2 ^ 59
def prefixEnd_6028580 : Nat := 4983230072969 + 3 ^ 40 * 6028580 * 2
def baseEnd_6028580 : Nat := 1031853068027376128908357

theorem tailTrace_6028580 : CollatzResearch.WordTrace tailWord_6028580 prefixEnd_6028580 1031853068027376128908357 := by
  unfold tailWord_6028580
  simp only [CollatzResearch.WordTrace]
  refine ⟨109940188249745867169253597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146586917666327822892338129 109940188249745867169253597)
  ·
    refine ⟨41227570593654700188470099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109940188249745867169253597 41227570593654700188470099)
    ·
      refine ⟨61841355890482050282705149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41227570593654700188470099 61841355890482050282705149)
      ·
        refine ⟨23190508458930768856014431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61841355890482050282705149 23190508458930768856014431)
        ·
          refine ⟨34785762688396153284021647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23190508458930768856014431 34785762688396153284021647)
          ·
            refine ⟨52178644032594229926032471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34785762688396153284021647 52178644032594229926032471)
            ·
              refine ⟨78267966048891344889048707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52178644032594229926032471 78267966048891344889048707)
              ·
                refine ⟨117401949073337017333573061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78267966048891344889048707 117401949073337017333573061)
                ·
                  refine ⟨22012865451250690750044949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 117401949073337017333573061 22012865451250690750044949)
                  ·
                    refine ⟨1031853068027376128908357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22012865451250690750044949 1031853068027376128908357)
                    ·
                      rfl

theorem cell23_6028580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 1, 4, 6].length) (baseStart_6028580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6028580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6028580 prefixEnd_6028580 := by exact prefixLift 6028580
  have htrace : WordTrace (prefixWord ++ tailWord_6028580) baseStart_6028580 baseEnd_6028580 := by
    simpa [prefixWord, tailWord_6028580, baseEnd_6028580] using wordTrace_append hprefix tailTrace_6028580
  have hstable : (prefixWord ++ tailWord_6028580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6028580).length < 2 ^ (prefixWord ++ tailWord_6028580).sum := by decide
  have hdescent : baseEnd_6028580 < baseStart_6028580 := by decide
  rcases family_descends (prefixWord ++ tailWord_6028580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6028581 : List Nat := [1, 3, 1, 2, 4, 3, 1, 2, 2, 1, 3]
def baseStart_6028581 : Nat := 118140960795 + 6028581 * 2 ^ 59
def prefixEnd_6028581 : Nat := 4983230072969 + 3 ^ 40 * 6028581 * 2
def baseEnd_6028581 : Nat := 3095559717562782882812567

theorem tailTrace_6028581 : CollatzResearch.WordTrace tailWord_6028581 prefixEnd_6028581 3095559717562782882812567 := by
  unfold tailWord_6028581
  simp only [CollatzResearch.WordTrace]
  refine ⟨219880412972488111509293597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146586941981658741006195731 219880412972488111509293597)
  ·
    refine ⟨82455154864683041815985099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 219880412972488111509293597 82455154864683041815985099)
    ·
      refine ⟨123682732297024562723977649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82455154864683041815985099 123682732297024562723977649)
      ·
        refine ⟨92762049222768422042983237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123682732297024562723977649 92762049222768422042983237)
        ·
          refine ⟨17392884229269079133059357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 92762049222768422042983237 17392884229269079133059357)
          ·
            refine ⟨6522331585975904674897259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17392884229269079133059357 6522331585975904674897259)
            ·
              refine ⟨9783497378963857012345889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6522331585975904674897259 9783497378963857012345889)
              ·
                refine ⟨7337623034222892759259417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9783497378963857012345889 7337623034222892759259417)
                ·
                  refine ⟨5503217275667169569444563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7337623034222892759259417 5503217275667169569444563)
                  ·
                    refine ⟨8254825913500754354166845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5503217275667169569444563 8254825913500754354166845)
                    ·
                      refine ⟨3095559717562782882812567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8254825913500754354166845 3095559717562782882812567)
                      ·
                        rfl

theorem cell23_6028581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 1, 2, 2, 1, 3].length) (baseStart_6028581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6028581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6028581 prefixEnd_6028581 := by exact prefixLift 6028581
  have htrace : WordTrace (prefixWord ++ tailWord_6028581) baseStart_6028581 baseEnd_6028581 := by
    simpa [prefixWord, tailWord_6028581, baseEnd_6028581] using wordTrace_append hprefix tailTrace_6028581
  have hstable : (prefixWord ++ tailWord_6028581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6028581).length < 2 ^ (prefixWord ++ tailWord_6028581).sum := by decide
  have hdescent : baseEnd_6028581 < baseStart_6028581 := by decide
  rcases family_descends (prefixWord ++ tailWord_6028581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6028598 : List Nat := [5, 1, 2, 3, 1, 2, 1, 1, 1, 3, 3]
def baseStart_6028598 : Nat := 118140960795 + 6028598 * 2 ^ 59
def prefixEnd_6028598 : Nat := 4983230072969 + 3 ^ 40 * 6028598 * 2
def baseEnd_6028598 : Nat := 3095568446733909316299989

theorem tailTrace_6028598 : CollatzResearch.WordTrace tailWord_6028598 prefixEnd_6028598 3095568446733909316299989 := by
  unfold tailWord_6028598
  simp only [CollatzResearch.WordTrace]
  refine ⟨13742564563339157713291403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 146587355342284348941774965 13742564563339157713291403)
  ·
    refine ⟨20613846845008736569937105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13742564563339157713291403 20613846845008736569937105)
    ·
      refine ⟨15460385133756552427452829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20613846845008736569937105 15460385133756552427452829)
      ·
        refine ⟨5797644425158707160294811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15460385133756552427452829 5797644425158707160294811)
        ·
          refine ⟨8696466637738060740442217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5797644425158707160294811 8696466637738060740442217)
          ·
            refine ⟨6522349978303545555331663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8696466637738060740442217 6522349978303545555331663)
            ·
              refine ⟨9783524967455318332997495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6522349978303545555331663 9783524967455318332997495)
              ·
                refine ⟨14675287451182977499496243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9783524967455318332997495 14675287451182977499496243)
                ·
                  refine ⟨22012931176774466249244365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14675287451182977499496243 22012931176774466249244365)
                  ·
                    refine ⟨8254849191290424843466637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22012931176774466249244365 8254849191290424843466637)
                    ·
                      refine ⟨3095568446733909316299989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8254849191290424843466637 3095568446733909316299989)
                      ·
                        rfl

theorem cell23_6028598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 1, 1, 1, 3, 3].length) (baseStart_6028598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6028598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6028598 prefixEnd_6028598 := by exact prefixLift 6028598
  have htrace : WordTrace (prefixWord ++ tailWord_6028598) baseStart_6028598 baseEnd_6028598 := by
    simpa [prefixWord, tailWord_6028598, baseEnd_6028598] using wordTrace_append hprefix tailTrace_6028598
  have hstable : (prefixWord ++ tailWord_6028598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6028598).length < 2 ^ (prefixWord ++ tailWord_6028598).sum := by decide
  have hdescent : baseEnd_6028598 < baseStart_6028598 := by decide
  rcases family_descends (prefixWord ++ tailWord_6028598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6028604 : List Nat := [2, 2, 2, 2, 1, 3, 3, 1, 1, 4, 2]
def baseStart_6028604 : Nat := 118140960795 + 6028604 * 2 ^ 59
def prefixEnd_6028604 : Nat := 4983230072969 + 3 ^ 40 * 6028604 * 2
def baseEnd_6028604 : Nat := 3095571527617836292824961

theorem tailTrace_6028604 : CollatzResearch.WordTrace tailWord_6028604 prefixEnd_6028604 3095571527617836292824961 := by
  unfold tailWord_6028604
  simp only [CollatzResearch.WordTrace]
  refine ⟨109940625925702393218690433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146587501234269857624920577 109940625925702393218690433)
  ·
    refine ⟨82455469444276794914017825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109940625925702393218690433 82455469444276794914017825)
    ·
      refine ⟨61841602083207596185513369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82455469444276794914017825 61841602083207596185513369)
      ·
        refine ⟨46381201562405697139135027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61841602083207596185513369 46381201562405697139135027)
        ·
          refine ⟨69571802343608545708702541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46381201562405697139135027 69571802343608545708702541)
          ·
            refine ⟨26089425878853204640763453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69571802343608545708702541 26089425878853204640763453)
            ·
              refine ⟨9783534704569951740286295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26089425878853204640763453 9783534704569951740286295)
              ·
                refine ⟨14675302056854927610429443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9783534704569951740286295 14675302056854927610429443)
                ·
                  refine ⟨22012953085282391415644165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14675302056854927610429443 22012953085282391415644165)
                  ·
                    refine ⟨4127428703490448390433281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22012953085282391415644165 4127428703490448390433281)
                    ·
                      refine ⟨3095571527617836292824961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4127428703490448390433281 3095571527617836292824961)
                      ·
                        rfl

theorem cell23_6028604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 3, 1, 1, 4, 2].length) (baseStart_6028604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6028604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6028604 prefixEnd_6028604 := by exact prefixLift 6028604
  have htrace : WordTrace (prefixWord ++ tailWord_6028604) baseStart_6028604 baseEnd_6028604 := by
    simpa [prefixWord, tailWord_6028604, baseEnd_6028604] using wordTrace_append hprefix tailTrace_6028604
  have hstable : (prefixWord ++ tailWord_6028604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6028604).length < 2 ^ (prefixWord ++ tailWord_6028604).sum := by decide
  have hdescent : baseEnd_6028604 < baseStart_6028604 := by decide
  rcases family_descends (prefixWord ++ tailWord_6028604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6028677 : List Nat := [1, 3, 1, 1, 3, 1, 3, 3, 2, 1, 4]
def baseStart_6028677 : Nat := 118140960795 + 6028677 * 2 ^ 59
def prefixEnd_6028677 : Nat := 4983230072969 + 3 ^ 40 * 6028677 * 2
def baseEnd_6028677 : Nat := 3095609011705614507212125

theorem tailTrace_6028677 : CollatzResearch.WordTrace tailWord_6028677 prefixEnd_6028677 3095609011705614507212125 := by
  unfold tailWord_6028677
  simp only [CollatzResearch.WordTrace]
  refine ⟨219883914380140319904788285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146589276253426879936525523 219883914380140319904788285)
  ·
    refine ⟨82456467892552619964295607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 219883914380140319904788285 82456467892552619964295607)
    ·
      refine ⟨123684701838828929946443411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82456467892552619964295607 123684701838828929946443411)
      ·
        refine ⟨185527052758243394919665117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123684701838828929946443411 185527052758243394919665117)
        ·
          refine ⟨69572644784341273094874419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 185527052758243394919665117 69572644784341273094874419)
          ·
            refine ⟨104358967176511909642311629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69572644784341273094874419 104358967176511909642311629)
            ·
              refine ⟨39134612691191966115866861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 104358967176511909642311629 39134612691191966115866861)
              ·
                refine ⟨14675479759196987293450073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39134612691191966115866861 14675479759196987293450073)
                ·
                  refine ⟨11006609819397740470087555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14675479759196987293450073 11006609819397740470087555)
                  ·
                    refine ⟨16509914729096610705131333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11006609819397740470087555 16509914729096610705131333)
                    ·
                      refine ⟨3095609011705614507212125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16509914729096610705131333 3095609011705614507212125)
                      ·
                        rfl

theorem cell23_6028677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 3, 2, 1, 4].length) (baseStart_6028677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6028677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6028677 prefixEnd_6028677 := by exact prefixLift 6028677
  have htrace : WordTrace (prefixWord ++ tailWord_6028677) baseStart_6028677 baseEnd_6028677 := by
    simpa [prefixWord, tailWord_6028677, baseEnd_6028677] using wordTrace_append hprefix tailTrace_6028677
  have hstable : (prefixWord ++ tailWord_6028677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6028677).length < 2 ^ (prefixWord ++ tailWord_6028677).sum := by decide
  have hdescent : baseEnd_6028677 < baseStart_6028677 := by decide
  rcases family_descends (prefixWord ++ tailWord_6028677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6028720 : List Nat := [2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 6]
def baseStart_6028720 : Nat := 118140960795 + 6028720 * 2 ^ 59
def prefixEnd_6028720 : Nat := 4983230072969 + 3 ^ 40 * 6028720 * 2
def baseEnd_6028720 : Nat := 3095631091373757838974427

theorem tailTrace_6028720 : CollatzResearch.WordTrace tailWord_6028720 prefixEnd_6028720 3095631091373757838974427 := by
  unfold tailWord_6028720
  simp only [CollatzResearch.WordTrace]
  refine ⟨109942741359492269124301807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146590321812656358832402409 109942741359492269124301807)
  ·
    refine ⟨164914112039238403686452711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109942741359492269124301807 164914112039238403686452711)
    ·
      refine ⟨247371168058857605529679067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164914112039238403686452711 247371168058857605529679067)
      ·
        refine ⟨371056752088286408294518601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 247371168058857605529679067 371056752088286408294518601)
        ·
          refine ⟨278292564066214806220888951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 371056752088286408294518601 278292564066214806220888951)
          ·
            refine ⟨417438846099322209331333427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 278292564066214806220888951 417438846099322209331333427)
            ·
              refine ⟨626158269148983313997000141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 417438846099322209331333427 626158269148983313997000141)
              ·
                refine ⟨234809350930868742748875053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 626158269148983313997000141 234809350930868742748875053)
                ·
                  refine ⟨88053506599075778530828145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 234809350930868742748875053 88053506599075778530828145)
                  ·
                    refine ⟨66040129949306833898121109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 88053506599075778530828145 66040129949306833898121109)
                    ·
                      refine ⟨3095631091373757838974427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 66040129949306833898121109 3095631091373757838974427)
                      ·
                        rfl

theorem cell23_6028720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 6].length) (baseStart_6028720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6028720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6028720 prefixEnd_6028720 := by exact prefixLift 6028720
  have htrace : WordTrace (prefixWord ++ tailWord_6028720) baseStart_6028720 baseEnd_6028720 := by
    simpa [prefixWord, tailWord_6028720, baseEnd_6028720] using wordTrace_append hprefix tailTrace_6028720
  have hstable : (prefixWord ++ tailWord_6028720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6028720).length < 2 ^ (prefixWord ++ tailWord_6028720).sum := by decide
  have hdescent : baseEnd_6028720 < baseStart_6028720 := by decide
  rcases family_descends (prefixWord ++ tailWord_6028720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6028744 : List Nat := [2, 1, 3, 1, 3, 1, 1, 2, 5, 1, 3]
def baseStart_6028744 : Nat := 118140960795 + 6028744 * 2 ^ 59
def prefixEnd_6028744 : Nat := 4983230072969 + 3 ^ 40 * 6028744 * 2
def baseEnd_6028744 : Nat := 3095643414909465745074317

theorem tailTrace_6028744 : CollatzResearch.WordTrace tailWord_6028744 prefixEnd_6028744 3095643414909465745074317 := by
  unfold tailWord_6028744
  simp only [CollatzResearch.WordTrace]
  refine ⟨109943179035448795173738643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146590905380598393564984857 109943179035448795173738643)
  ·
    refine ⟨164914768553173192760607965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109943179035448795173738643 164914768553173192760607965)
    ·
      refine ⟨61843038207439947285227987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 164914768553173192760607965 61843038207439947285227987)
      ·
        refine ⟨92764557311159920927841981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61843038207439947285227987 92764557311159920927841981)
        ·
          refine ⟨34786708991684970347940743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92764557311159920927841981 34786708991684970347940743)
          ·
            refine ⟨52180063487527455521911115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34786708991684970347940743 52180063487527455521911115)
            ·
              refine ⟨78270095231291183282866673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52180063487527455521911115 78270095231291183282866673)
              ·
                refine ⟨58702571423468387462150005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78270095231291183282866673 58702571423468387462150005)
                ·
                  refine ⟨5503366070950161324576563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 58702571423468387462150005 5503366070950161324576563)
                  ·
                    refine ⟨8255049106425241986864845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5503366070950161324576563 8255049106425241986864845)
                    ·
                      refine ⟨3095643414909465745074317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8255049106425241986864845 3095643414909465745074317)
                      ·
                        rfl

theorem cell23_6028744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 2, 5, 1, 3].length) (baseStart_6028744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6028744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6028744 prefixEnd_6028744 := by exact prefixLift 6028744
  have htrace : WordTrace (prefixWord ++ tailWord_6028744) baseStart_6028744 baseEnd_6028744 := by
    simpa [prefixWord, tailWord_6028744, baseEnd_6028744] using wordTrace_append hprefix tailTrace_6028744
  have hstable : (prefixWord ++ tailWord_6028744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6028744).length < 2 ^ (prefixWord ++ tailWord_6028744).sum := by decide
  have hdescent : baseEnd_6028744 < baseStart_6028744 := by decide
  rcases family_descends (prefixWord ++ tailWord_6028744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6028761 : List Nat := [1, 2, 1, 2, 4, 3, 2, 1, 3, 1, 3]
def baseStart_6028761 : Nat := 118140960795 + 6028761 * 2 ^ 59
def prefixEnd_6028761 : Nat := 4983230072969 + 3 ^ 40 * 6028761 * 2
def baseEnd_6028761 : Nat := 3095652144080592178561739

theorem tailTrace_6028761 : CollatzResearch.WordTrace tailWord_6028761 prefixEnd_6028761 3095652144080592178561739 := by
  unfold tailWord_6028761
  simp only [CollatzResearch.WordTrace]
  refine ⟨219886978111836002250846137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146591318741224001500564091 219886978111836002250846137)
  ·
    refine ⟨164915233583877001688134603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219886978111836002250846137 164915233583877001688134603)
    ·
      refine ⟨247372850375815502532201905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164915233583877001688134603 247372850375815502532201905)
      ·
        refine ⟨185529637781861626899151429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 247372850375815502532201905 185529637781861626899151429)
        ·
          refine ⟨34786807084099055043590893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 185529637781861626899151429 34786807084099055043590893)
          ·
            refine ⟨13045052656537145641346585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34786807084099055043590893 13045052656537145641346585)
            ·
              refine ⟨9783789492402859231009939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13045052656537145641346585 9783789492402859231009939)
              ·
                refine ⟨14675684238604288846514909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9783789492402859231009939 14675684238604288846514909)
                ·
                  refine ⟨5503381589476608317443091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14675684238604288846514909 5503381589476608317443091)
                  ·
                    refine ⟨8255072384214912476164637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5503381589476608317443091 8255072384214912476164637)
                    ·
                      refine ⟨3095652144080592178561739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8255072384214912476164637 3095652144080592178561739)
                      ·
                        rfl

theorem cell23_6028761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 2, 1, 3, 1, 3].length) (baseStart_6028761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6028761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6028761 prefixEnd_6028761 := by exact prefixLift 6028761
  have htrace : WordTrace (prefixWord ++ tailWord_6028761) baseStart_6028761 baseEnd_6028761 := by
    simpa [prefixWord, tailWord_6028761, baseEnd_6028761] using wordTrace_append hprefix tailTrace_6028761
  have hstable : (prefixWord ++ tailWord_6028761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6028761).length < 2 ^ (prefixWord ++ tailWord_6028761).sum := by decide
  have hdescent : baseEnd_6028761 < baseStart_6028761 := by decide
  rcases family_descends (prefixWord ++ tailWord_6028761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6028784 : List Nat := [2, 1, 1, 1, 3, 4, 1, 4, 1, 1, 4]
def baseStart_6028784 : Nat := 118140960795 + 6028784 * 2 ^ 59
def prefixEnd_6028784 : Nat := 4983230072969 + 3 ^ 40 * 6028784 * 2
def baseEnd_6028784 : Nat := 3095663954135645588574133

theorem tailTrace_6028784 : CollatzResearch.WordTrace tailWord_6028784 prefixEnd_6028784 3095663954135645588574133 := by
  unfold tailWord_6028784
  simp only [CollatzResearch.WordTrace]
  refine ⟨109943908495376338589466703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146591877993835118119288937 109943908495376338589466703)
  ·
    refine ⟨164915862743064507884200055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109943908495376338589466703 164915862743064507884200055)
    ·
      refine ⟨247373794114596761826300083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164915862743064507884200055 247373794114596761826300083)
      ·
        refine ⟨371060691171895142739450125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 247373794114596761826300083 371060691171895142739450125)
        ·
          refine ⟨139147759189460678527293797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 371060691171895142739450125 139147759189460678527293797)
          ·
            refine ⟨26090204848023877223867587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 139147759189460678527293797 26090204848023877223867587)
            ·
              refine ⟨39135307272035815835801381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26090204848023877223867587 39135307272035815835801381)
              ·
                refine ⟨7337870113506715469212759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39135307272035815835801381 7337870113506715469212759)
                ·
                  refine ⟨11006805170260073203819139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7337870113506715469212759 11006805170260073203819139)
                  ·
                    refine ⟨16510207755390109805728709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11006805170260073203819139 16510207755390109805728709)
                    ·
                      refine ⟨3095663954135645588574133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16510207755390109805728709 3095663954135645588574133)
                      ·
                        rfl

theorem cell23_6028784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 4, 1, 1, 4].length) (baseStart_6028784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6028784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6028784 prefixEnd_6028784 := by exact prefixLift 6028784
  have htrace : WordTrace (prefixWord ++ tailWord_6028784) baseStart_6028784 baseEnd_6028784 := by
    simpa [prefixWord, tailWord_6028784, baseEnd_6028784] using wordTrace_append hprefix tailTrace_6028784
  have hstable : (prefixWord ++ tailWord_6028784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6028784).length < 2 ^ (prefixWord ++ tailWord_6028784).sum := by decide
  have hdescent : baseEnd_6028784 < baseStart_6028784 := by decide
  rcases family_descends (prefixWord ++ tailWord_6028784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6028807 : List Nat := [1, 1, 4, 3, 2, 1, 11]
def baseStart_6028807 : Nat := 118140960795 + 6028807 * 2 ^ 59
def prefixEnd_6028807 : Nat := 4983230072969 + 3 ^ 40 * 6028807 * 2
def baseEnd_6028807 : Nat := 38218219310996283933167

theorem tailTrace_6028807 : CollatzResearch.WordTrace tailWord_6028807 prefixEnd_6028807 38218219310996283933167 := by
  unfold tailWord_6028807
  simp only [CollatzResearch.WordTrace]
  refine ⟨219888655869669352107020675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146592437246446234738013783 219888655869669352107020675)
  ·
    refine ⟨329832983804504028160531013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219888655869669352107020675 329832983804504028160531013)
    ·
      refine ⟨61843684463344505280099565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 329832983804504028160531013 61843684463344505280099565)
      ·
        refine ⟨23191381673754189480037337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61843684463344505280099565 23191381673754189480037337)
        ·
          refine ⟨17393536255315642110028003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23191381673754189480037337 17393536255315642110028003)
          ·
            refine ⟨26090304382973463165042005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17393536255315642110028003 26090304382973463165042005)
            ·
              refine ⟨38218219310996283933167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 26090304382973463165042005 38218219310996283933167)
              ·
                rfl

theorem cell23_6028807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 11].length) (baseStart_6028807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6028807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6028807 prefixEnd_6028807 := by exact prefixLift 6028807
  have htrace : WordTrace (prefixWord ++ tailWord_6028807) baseStart_6028807 baseEnd_6028807 := by
    simpa [prefixWord, tailWord_6028807, baseEnd_6028807] using wordTrace_append hprefix tailTrace_6028807
  have hstable : (prefixWord ++ tailWord_6028807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6028807).length < 2 ^ (prefixWord ++ tailWord_6028807).sum := by decide
  have hdescent : baseEnd_6028807 < baseStart_6028807 := by decide
  rcases family_descends (prefixWord ++ tailWord_6028807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6028824 : List Nat := [2, 1, 2, 3, 4, 1, 2, 8]
def baseStart_6028824 : Nat := 118140960795 + 6028824 * 2 ^ 59
def prefixEnd_6028824 : Nat := 4983230072969 + 3 ^ 40 * 6028824 * 2
def baseEnd_6028824 : Nat := 114654981235623164150887

theorem tailTrace_6028824 : CollatzResearch.WordTrace tailWord_6028824 prefixEnd_6028824 114654981235623164150887 := by
  unfold tailWord_6028824
  simp only [CollatzResearch.WordTrace]
  refine ⟨109944637955303882005194763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146592850607071842673593017 109944637955303882005194763)
  ·
    refine ⟨164916956932955823007792145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109944637955303882005194763 164916956932955823007792145)
    ·
      refine ⟨123687717699716867255844109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164916956932955823007792145 123687717699716867255844109)
      ·
        refine ⟨46382894137393825220941541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123687717699716867255844109 46382894137393825220941541)
        ·
          refine ⟨8696792650761342228926539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46382894137393825220941541 8696792650761342228926539)
          ·
            refine ⟨13045188976142013343389809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8696792650761342228926539 13045188976142013343389809)
            ·
              refine ⟨9783891732106510007542357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13045188976142013343389809 9783891732106510007542357)
              ·
                refine ⟨114654981235623164150887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9783891732106510007542357 114654981235623164150887)
                ·
                  rfl

theorem cell23_6028824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 2, 8].length) (baseStart_6028824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6028824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6028824 prefixEnd_6028824 := by exact prefixLift 6028824
  have htrace : WordTrace (prefixWord ++ tailWord_6028824) baseStart_6028824 baseEnd_6028824 := by
    simpa [prefixWord, tailWord_6028824, baseEnd_6028824] using wordTrace_append hprefix tailTrace_6028824
  have hstable : (prefixWord ++ tailWord_6028824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6028824).length < 2 ^ (prefixWord ++ tailWord_6028824).sum := by decide
  have hdescent : baseEnd_6028824 < baseStart_6028824 := by decide
  rcases family_descends (prefixWord ++ tailWord_6028824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6028884 : List Nat := [2, 4, 1, 1, 1, 2, 3, 1, 2, 6]
def baseStart_6028884 : Nat := 118140960795 + 6028884 * 2 ^ 59
def prefixEnd_6028884 : Nat := 4983230072969 + 3 ^ 40 * 6028884 * 2
def baseEnd_6028884 : Nat := 1031905100733698399107891

theorem tailTrace_6028884 : CollatzResearch.WordTrace tailWord_6028884 prefixEnd_6028884 1031905100733698399107891 := by
  unfold tailWord_6028884
  simp only [CollatzResearch.WordTrace]
  refine ⟨109945732145195197128786853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146594309526926929505049137 109945732145195197128786853)
  ·
    refine ⟨20614824777224099461647535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 109945732145195197128786853 20614824777224099461647535)
    ·
      refine ⟨30922237165836149192471303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20614824777224099461647535 30922237165836149192471303)
      ·
        refine ⟨46383355748754223788706955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30922237165836149192471303 46383355748754223788706955)
        ·
          refine ⟨69575033623131335683060433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46383355748754223788706955 69575033623131335683060433)
          ·
            refine ⟨52181275217348501762295325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69575033623131335683060433 52181275217348501762295325)
            ·
              refine ⟨19567978206505688160860747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52181275217348501762295325 19567978206505688160860747)
              ·
                refine ⟨29351967309758532241291121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19567978206505688160860747 29351967309758532241291121)
                ·
                  refine ⟨22013975482318899180968341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29351967309758532241291121 22013975482318899180968341)
                  ·
                    refine ⟨1031905100733698399107891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22013975482318899180968341 1031905100733698399107891)
                    ·
                      rfl

theorem cell23_6028884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 3, 1, 2, 6].length) (baseStart_6028884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6028884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6028884 prefixEnd_6028884 := by exact prefixLift 6028884
  have htrace : WordTrace (prefixWord ++ tailWord_6028884) baseStart_6028884 baseEnd_6028884 := by
    simpa [prefixWord, tailWord_6028884, baseEnd_6028884] using wordTrace_append hprefix tailTrace_6028884
  have hstable : (prefixWord ++ tailWord_6028884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6028884).length < 2 ^ (prefixWord ++ tailWord_6028884).sum := by decide
  have hdescent : baseEnd_6028884 < baseStart_6028884 := by decide
  rcases family_descends (prefixWord ++ tailWord_6028884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6028925 : List Nat := [1, 4, 1, 1, 4, 1, 3, 2, 2, 2, 2]
def baseStart_6028925 : Nat := 118140960795 + 6028925 * 2 ^ 59
def prefixEnd_6028925 : Nat := 4983230072969 + 3 ^ 40 * 6028925 * 2
def baseEnd_6028925 : Nat := 3095736354907929536910985

theorem tailTrace_6028925 : CollatzResearch.WordTrace tailWord_6028925 prefixEnd_6028925 3095736354907929536910985 := by
  unfold tailWord_6028925
  simp only [CollatzResearch.WordTrace]
  refine ⟨219892959683241858259816229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146595306455494572173210819 219892959683241858259816229)
  ·
    refine ⟨41229929940607848423715543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 219892959683241858259816229 41229929940607848423715543)
    ·
      refine ⟨61844894910911772635573315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41229929940607848423715543 61844894910911772635573315)
      ·
        refine ⟨92767342366367658953359973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61844894910911772635573315 92767342366367658953359973)
        ·
          refine ⟨17393876693693936053754995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 92767342366367658953359973 17393876693693936053754995)
          ·
            refine ⟨26090815040540904080632493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17393876693693936053754995 26090815040540904080632493)
            ·
              refine ⟨9784055640202839030237185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26090815040540904080632493 9784055640202839030237185)
              ·
                refine ⟨7338041730152129272677889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9784055640202839030237185 7338041730152129272677889)
                ·
                  refine ⟨5503531297614096954508417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7338041730152129272677889 5503531297614096954508417)
                  ·
                    refine ⟨4127648473210572715881313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5503531297614096954508417 4127648473210572715881313)
                    ·
                      refine ⟨3095736354907929536910985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4127648473210572715881313 3095736354907929536910985)
                      ·
                        rfl

theorem cell23_6028925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 3, 2, 2, 2, 2].length) (baseStart_6028925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6028925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6028925 prefixEnd_6028925 := by exact prefixLift 6028925
  have htrace : WordTrace (prefixWord ++ tailWord_6028925) baseStart_6028925 baseEnd_6028925 := by
    simpa [prefixWord, tailWord_6028925, baseEnd_6028925] using wordTrace_append hprefix tailTrace_6028925
  have hstable : (prefixWord ++ tailWord_6028925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6028925).length < 2 ^ (prefixWord ++ tailWord_6028925).sum := by decide
  have hdescent : baseEnd_6028925 < baseStart_6028925 := by decide
  rcases family_descends (prefixWord ++ tailWord_6028925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6028942 : List Nat := [4, 1, 1, 3, 1, 3, 3, 1, 2, 2, 2]
def baseStart_6028942 : Nat := 118140960795 + 6028942 * 2 ^ 59
def prefixEnd_6028942 : Nat := 4983230072969 + 3 ^ 40 * 6028942 * 2
def baseEnd_6028942 : Nat := 3095745084079055970398407

theorem tailTrace_6028942 : CollatzResearch.WordTrace tailWord_6028942 prefixEnd_6028942 3095745084079055970398407 := by
  unfold tailWord_6028942
  simp only [CollatzResearch.WordTrace]
  refine ⟨27486697465522533770398135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 146595719816120180108790053 27486697465522533770398135)
  ·
    refine ⟨41230046198283800655597203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27486697465522533770398135 41230046198283800655597203)
    ·
      refine ⟨61845069297425700983395805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41230046198283800655597203 61845069297425700983395805)
      ·
        refine ⟨23191900986534637868773427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61845069297425700983395805 23191900986534637868773427)
        ·
          refine ⟨34787851479801956803160141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23191900986534637868773427 34787851479801956803160141)
          ·
            refine ⟨13045444304925733801185053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34787851479801956803160141 13045444304925733801185053)
            ·
              refine ⟨4892041614347150175444395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13045444304925733801185053 4892041614347150175444395)
              ·
                refine ⟨7338062421520725263166593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4892041614347150175444395 7338062421520725263166593)
                ·
                  refine ⟨5503546816140543947374945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7338062421520725263166593 5503546816140543947374945)
                  ·
                    refine ⟨4127660112105407960531209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5503546816140543947374945 4127660112105407960531209)
                    ·
                      refine ⟨3095745084079055970398407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4127660112105407960531209 3095745084079055970398407)
                      ·
                        rfl

theorem cell23_6028942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 3, 1, 2, 2, 2].length) (baseStart_6028942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6028942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6028942 prefixEnd_6028942 := by exact prefixLift 6028942
  have htrace : WordTrace (prefixWord ++ tailWord_6028942) baseStart_6028942 baseEnd_6028942 := by
    simpa [prefixWord, tailWord_6028942, baseEnd_6028942] using wordTrace_append hprefix tailTrace_6028942
  have hstable : (prefixWord ++ tailWord_6028942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6028942).length < 2 ^ (prefixWord ++ tailWord_6028942).sum := by decide
  have hdescent : baseEnd_6028942 < baseStart_6028942 := by decide
  rcases family_descends (prefixWord ++ tailWord_6028942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6028982 : List Nat := [5, 1, 3, 1, 1, 2, 3, 2, 5]
def baseStart_6028982 : Nat := 118140960795 + 6028982 * 2 ^ 59
def prefixEnd_6028982 : Nat := 4983230072969 + 3 ^ 40 * 6028982 * 2
def baseEnd_6028982 : Nat := 343973958145026201544247

theorem tailTrace_6028982 : CollatzResearch.WordTrace tailWord_6028982 prefixEnd_6028982 343973958145026201544247 := by
  unfold tailWord_6028982
  simp only [CollatzResearch.WordTrace]
  refine ⟨13743439915252209812165075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 146596692429356904663094133 13743439915252209812165075)
  ·
    refine ⟨20615159872878314718247613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13743439915252209812165075 20615159872878314718247613)
    ·
      refine ⟨7730684952329368019342855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20615159872878314718247613 7730684952329368019342855)
      ·
        refine ⟨11596027428494052029014283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7730684952329368019342855 11596027428494052029014283)
        ·
          refine ⟨17394041142741078043521425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11596027428494052029014283 17394041142741078043521425)
          ·
            refine ⟨13045530857055808532641069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17394041142741078043521425 13045530857055808532641069)
            ·
              refine ⟨4892074071395928199740401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13045530857055808532641069 4892074071395928199740401)
              ·
                refine ⟨3669055553546946149805301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4892074071395928199740401 3669055553546946149805301)
                ·
                  refine ⟨343973958145026201544247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3669055553546946149805301 343973958145026201544247)
                  ·
                    rfl

theorem cell23_6028982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 3, 2, 5].length) (baseStart_6028982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6028982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6028982 prefixEnd_6028982 := by exact prefixLift 6028982
  have htrace : WordTrace (prefixWord ++ tailWord_6028982) baseStart_6028982 baseEnd_6028982 := by
    simpa [prefixWord, tailWord_6028982, baseEnd_6028982] using wordTrace_append hprefix tailTrace_6028982
  have hstable : (prefixWord ++ tailWord_6028982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6028982).length < 2 ^ (prefixWord ++ tailWord_6028982).sum := by decide
  have hdescent : baseEnd_6028982 < baseStart_6028982 := by decide
  rcases family_descends (prefixWord ++ tailWord_6028982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6029018 : List Nat := [3, 1, 1, 2, 2, 4, 2, 1, 2, 2, 3]
def baseStart_6029018 : Nat := 118140960795 + 6029018 * 2 ^ 59
def prefixEnd_6029018 : Nat := 4983230072969 + 3 ^ 40 * 6029018 * 2
def baseEnd_6029018 : Nat := 3095784108608797673048057

theorem tailTrace_6029018 : CollatzResearch.WordTrace tailWord_6029018 prefixEnd_6029018 3095784108608797673048057 := by
  unfold tailWord_6029018
  simp only [CollatzResearch.WordTrace]
  refine ⟨54974087917976233785737927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146597567781269956761967805 54974087917976233785737927)
  ·
    refine ⟨82461131876964350678606891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54974087917976233785737927 82461131876964350678606891)
    ·
      refine ⟨123691697815446526017910337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82461131876964350678606891 123691697815446526017910337)
      ·
        refine ⟨92768773361584894513432753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123691697815446526017910337 92768773361584894513432753)
        ·
          refine ⟨69576580021188670885074565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92768773361584894513432753 69576580021188670885074565)
          ·
            refine ⟨13045608753972875790951481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 69576580021188670885074565 13045608753972875790951481)
            ·
              refine ⟨9784206565479656843213611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13045608753972875790951481 9784206565479656843213611)
              ·
                refine ⟨14676309848219485264820417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9784206565479656843213611 14676309848219485264820417)
                ·
                  refine ⟨11007232386164613948615313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14676309848219485264820417 11007232386164613948615313)
                  ·
                    refine ⟨8255424289623460461461485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11007232386164613948615313 8255424289623460461461485)
                    ·
                      refine ⟨3095784108608797673048057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8255424289623460461461485 3095784108608797673048057)
                      ·
                        rfl

theorem cell23_6029018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 2, 1, 2, 2, 3].length) (baseStart_6029018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6029018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6029018 prefixEnd_6029018 := by exact prefixLift 6029018
  have htrace : WordTrace (prefixWord ++ tailWord_6029018) baseStart_6029018 baseEnd_6029018 := by
    simpa [prefixWord, tailWord_6029018, baseEnd_6029018] using wordTrace_append hprefix tailTrace_6029018
  have hstable : (prefixWord ++ tailWord_6029018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6029018).length < 2 ^ (prefixWord ++ tailWord_6029018).sum := by decide
  have hdescent : baseEnd_6029018 < baseStart_6029018 := by decide
  rcases family_descends (prefixWord ++ tailWord_6029018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6029069 : List Nat := [1, 7, 2, 1, 1, 1, 1, 1, 1, 4, 3]
def baseStart_6029069 : Nat := 118140960795 + 6029069 * 2 ^ 59
def prefixEnd_6029069 : Nat := 4983230072969 + 3 ^ 40 * 6029069 * 2
def baseEnd_6029069 : Nat := 3095810296122176973510323

theorem tailTrace_6029069 : CollatzResearch.WordTrace tailWord_6029069 prefixEnd_6029069 3095810296122176973510323 := by
  unfold tailWord_6029069
  simp only [CollatzResearch.WordTrace]
  refine ⟨219898211794720170853058261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146598807863146780568705507 219898211794720170853058261)
  ·
    refine ⟨5153864338938754004368553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 219898211794720170853058261 5153864338938754004368553)
    ·
      refine ⟨3865398254204065503276415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5153864338938754004368553 3865398254204065503276415)
      ·
        refine ⟨5798097381306098254914623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3865398254204065503276415 5798097381306098254914623)
        ·
          refine ⟨8697146071959147382371935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5798097381306098254914623 8697146071959147382371935)
          ·
            refine ⟨13045719107938721073557903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8697146071959147382371935 13045719107938721073557903)
            ·
              refine ⟨19568578661908081610336855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13045719107938721073557903 19568578661908081610336855)
              ·
                refine ⟨29352867992862122415505283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19568578661908081610336855 29352867992862122415505283)
                ·
                  refine ⟨44029301989293183623257925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29352867992862122415505283 44029301989293183623257925)
                  ·
                    refine ⟨8255494122992471929360861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 44029301989293183623257925 8255494122992471929360861)
                    ·
                      refine ⟨3095810296122176973510323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8255494122992471929360861 3095810296122176973510323)
                      ·
                        rfl

theorem cell23_6029069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 1, 1, 1, 4, 3].length) (baseStart_6029069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6029069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6029069 prefixEnd_6029069 := by exact prefixLift 6029069
  have htrace : WordTrace (prefixWord ++ tailWord_6029069) baseStart_6029069 baseEnd_6029069 := by
    simpa [prefixWord, tailWord_6029069, baseEnd_6029069] using wordTrace_append hprefix tailTrace_6029069
  have hstable : (prefixWord ++ tailWord_6029069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6029069).length < 2 ^ (prefixWord ++ tailWord_6029069).sum := by decide
  have hdescent : baseEnd_6029069 < baseStart_6029069 := by decide
  rcases family_descends (prefixWord ++ tailWord_6029069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6029071 : List Nat := [1, 1, 2, 1, 1, 1, 4, 1, 1, 8, 2]
def baseStart_6029071 : Nat := 118140960795 + 6029071 * 2 ^ 59
def prefixEnd_6029071 : Nat := 4983230072969 + 3 ^ 40 * 6029071 * 2
def baseEnd_6029071 : Nat := 3095811323083485965685313

theorem tailTrace_6029071 : CollatzResearch.WordTrace tailWord_6029071 prefixEnd_6029071 3095811323083485965685313 := by
  unfold tailWord_6029071
  simp only [CollatzResearch.WordTrace]
  refine ⟨219898284740712925194631067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146598856493808616796420711 219898284740712925194631067)
  ·
    refine ⟨329847427111069387791946601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219898284740712925194631067 329847427111069387791946601)
    ·
      refine ⟨247385570333302040843959951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 329847427111069387791946601 247385570333302040843959951)
      ·
        refine ⟨371078355499953061265939927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 247385570333302040843959951 371078355499953061265939927)
        ·
          refine ⟨556617533249929591898909891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 371078355499953061265939927 556617533249929591898909891)
          ·
            refine ⟨834926299874894387848364837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 556617533249929591898909891 834926299874894387848364837)
            ·
              refine ⟨156548681226542697721568407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 834926299874894387848364837 156548681226542697721568407)
              ·
                refine ⟨234823021839814046582352611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 156548681226542697721568407 234823021839814046582352611)
                ·
                  refine ⟨352234532759721069873528917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 234823021839814046582352611 352234532759721069873528917)
                  ·
                    refine ⟨4127748430777981287580417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 352234532759721069873528917 4127748430777981287580417)
                    ·
                      refine ⟨3095811323083485965685313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4127748430777981287580417 3095811323083485965685313)
                      ·
                        rfl

theorem cell23_6029071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 1, 1, 8, 2].length) (baseStart_6029071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6029071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6029071 prefixEnd_6029071 := by exact prefixLift 6029071
  have htrace : WordTrace (prefixWord ++ tailWord_6029071) baseStart_6029071 baseEnd_6029071 := by
    simpa [prefixWord, tailWord_6029071, baseEnd_6029071] using wordTrace_append hprefix tailTrace_6029071
  have hstable : (prefixWord ++ tailWord_6029071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6029071).length < 2 ^ (prefixWord ++ tailWord_6029071).sum := by decide
  have hdescent : baseEnd_6029071 < baseStart_6029071 := by decide
  rcases family_descends (prefixWord ++ tailWord_6029071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6029076 : List Nat := [2, 4, 4, 1, 1, 1, 2, 3, 1, 4]
def baseStart_6029076 : Nat := 118140960795 + 6029076 * 2 ^ 59
def prefixEnd_6029076 : Nat := 4983230072969 + 3 ^ 40 * 6029076 * 2
def baseEnd_6029076 : Nat := 1031937963495586148707597

theorem tailTrace_6029076 : CollatzResearch.WordTrace tailWord_6029076 prefixEnd_6029076 1031937963495586148707597 := by
  unfold tailWord_6029076
  simp only [CollatzResearch.WordTrace]
  refine ⟨109949233552847405524281541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146598978070463207365708721 109949233552847405524281541)
  ·
    refine ⟨20615481291158888535802789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 109949233552847405524281541 20615481291158888535802789)
    ·
      refine ⟨3865402742092291600463023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20615481291158888535802789 3865402742092291600463023)
      ·
        refine ⟨5798104113138437400694535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3865402742092291600463023 5798104113138437400694535)
        ·
          refine ⟨8697156169707656101041803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5798104113138437400694535 8697156169707656101041803)
          ·
            refine ⟨13045734254561484151562705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8697156169707656101041803 13045734254561484151562705)
            ·
              refine ⟨9784300690921113113672029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13045734254561484151562705 9784300690921113113672029)
              ·
                refine ⟨3669112759095417417627011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9784300690921113113672029 3669112759095417417627011)
                ·
                  refine ⟨5503669138643126126440517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3669112759095417417627011 5503669138643126126440517)
                  ·
                    refine ⟨1031937963495586148707597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5503669138643126126440517 1031937963495586148707597)
                    ·
                      rfl

theorem cell23_6029076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_6029076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6029076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6029076 prefixEnd_6029076 := by exact prefixLift 6029076
  have htrace : WordTrace (prefixWord ++ tailWord_6029076) baseStart_6029076 baseEnd_6029076 := by
    simpa [prefixWord, tailWord_6029076, baseEnd_6029076] using wordTrace_append hprefix tailTrace_6029076
  have hstable : (prefixWord ++ tailWord_6029076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6029076).length < 2 ^ (prefixWord ++ tailWord_6029076).sum := by decide
  have hdescent : baseEnd_6029076 < baseStart_6029076 := by decide
  rcases family_descends (prefixWord ++ tailWord_6029076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6029082 : List Nat := [3, 1, 1, 3, 2, 3, 2, 3, 1, 1, 3]
def baseStart_6029082 : Nat := 118140960795 + 6029082 * 2 ^ 59
def prefixEnd_6029082 : Nat := 4983230072969 + 3 ^ 40 * 6029082 * 2
def baseEnd_6029082 : Nat := 3095816971370685422647763

theorem tailTrace_6029082 : CollatzResearch.WordTrace tailWord_6029082 prefixEnd_6029082 3095816971370685422647763 := by
  unfold tailWord_6029082
  simp only [CollatzResearch.WordTrace]
  refine ⟨54974671485918268518320375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146599123962448716048854333 54974671485918268518320375)
  ·
    refine ⟨82462007228877402777480563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54974671485918268518320375 82462007228877402777480563)
    ·
      refine ⟨123693010843316104166220845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82462007228877402777480563 123693010843316104166220845)
      ·
        refine ⟨46384879066243539062332817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123693010843316104166220845 46384879066243539062332817)
        ·
          refine ⟨34788659299682654296749613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46384879066243539062332817 34788659299682654296749613)
          ·
            refine ⟨13045747237380995361281105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34788659299682654296749613 13045747237380995361281105)
            ·
              refine ⟨9784310428035746520960829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13045747237380995361281105 9784310428035746520960829)
              ·
                refine ⟨3669116410513404945360311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9784310428035746520960829 3669116410513404945360311)
                ·
                  refine ⟨5503674615770107418040467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3669116410513404945360311 5503674615770107418040467)
                  ·
                    refine ⟨8255511923655161127060701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5503674615770107418040467 8255511923655161127060701)
                    ·
                      refine ⟨3095816971370685422647763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8255511923655161127060701 3095816971370685422647763)
                      ·
                        rfl

theorem cell23_6029082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 2, 3, 1, 1, 3].length) (baseStart_6029082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6029082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6029082 prefixEnd_6029082 := by exact prefixLift 6029082
  have htrace : WordTrace (prefixWord ++ tailWord_6029082) baseStart_6029082 baseEnd_6029082 := by
    simpa [prefixWord, tailWord_6029082, baseEnd_6029082] using wordTrace_append hprefix tailTrace_6029082
  have hstable : (prefixWord ++ tailWord_6029082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6029082).length < 2 ^ (prefixWord ++ tailWord_6029082).sum := by decide
  have hdescent : baseEnd_6029082 < baseStart_6029082 := by decide
  rcases family_descends (prefixWord ++ tailWord_6029082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6029088 : List Nat := [2, 1, 1, 5, 1, 1, 3, 3, 1, 1, 4]
def baseStart_6029088 : Nat := 118140960795 + 6029088 * 2 ^ 59
def prefixEnd_6029088 : Nat := 4983230072969 + 3 ^ 40 * 6029088 * 2
def baseEnd_6029088 : Nat := 3095820052254612399172735

theorem tailTrace_6029088 : CollatzResearch.WordTrace tailWord_6029088 prefixEnd_6029088 3095820052254612399172735 := by
  unfold tailWord_6029088
  simp only [CollatzResearch.WordTrace]
  refine ⟨109949452390825668548999959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146599269854434224731999945 109949452390825668548999959)
  ·
    refine ⟨164924178586238502823499939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109949452390825668548999959 164924178586238502823499939)
    ·
      refine ⟨247386267879357754235249909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164924178586238502823499939 247386267879357754235249909)
      ·
        refine ⟨23192462613689789459554679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 247386267879357754235249909 23192462613689789459554679)
        ·
          refine ⟨34788693920534684189332019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23192462613689789459554679 34788693920534684189332019)
          ·
            refine ⟨52183040880802026283998029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34788693920534684189332019 52183040880802026283998029)
            ·
              refine ⟨19568640330300759856499261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52183040880802026283998029 19568640330300759856499261)
              ·
                refine ⟨7338240123862784946187223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19568640330300759856499261 7338240123862784946187223)
                ·
                  refine ⟨11007360185794177419280835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7338240123862784946187223 11007360185794177419280835)
                  ·
                    refine ⟨16511040278691266128921253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11007360185794177419280835 16511040278691266128921253)
                    ·
                      refine ⟨3095820052254612399172735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16511040278691266128921253 3095820052254612399172735)
                      ·
                        rfl

theorem cell23_6029088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3, 3, 1, 1, 4].length) (baseStart_6029088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6029088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6029088 prefixEnd_6029088 := by exact prefixLift 6029088
  have htrace : WordTrace (prefixWord ++ tailWord_6029088) baseStart_6029088 baseEnd_6029088 := by
    simpa [prefixWord, tailWord_6029088, baseEnd_6029088] using wordTrace_append hprefix tailTrace_6029088
  have hstable : (prefixWord ++ tailWord_6029088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6029088).length < 2 ^ (prefixWord ++ tailWord_6029088).sum := by decide
  have hdescent : baseEnd_6029088 < baseStart_6029088 := by decide
  rcases family_descends (prefixWord ++ tailWord_6029088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6029104 : List Nat := [2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 7]
def baseStart_6029104 : Nat := 118140960795 + 6029104 * 2 ^ 59
def prefixEnd_6029104 : Nat := 4983230072969 + 3 ^ 40 * 6029104 * 2
def baseEnd_6029104 : Nat := 3095828267945084336572661

theorem tailTrace_6029104 : CollatzResearch.WordTrace tailWord_6029104 prefixEnd_6029104 3095828267945084336572661 := by
  unfold tailWord_6029104
  simp only [CollatzResearch.WordTrace]
  refine ⟨109949744174796685915291183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146599658899728914553721577 109949744174796685915291183)
  ·
    refine ⟨164924616262195028872936775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109949744174796685915291183 164924616262195028872936775)
    ·
      refine ⟨247386924393292543309405163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164924616262195028872936775 247386924393292543309405163)
      ·
        refine ⟨371080386589938814964107745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 247386924393292543309405163 371080386589938814964107745)
        ·
          refine ⟨278310289942454111223080809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 371080386589938814964107745 278310289942454111223080809)
          ·
            refine ⟨208732717456840583417310607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 278310289942454111223080809 208732717456840583417310607)
            ·
              refine ⟨313099076185260875125965911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 208732717456840583417310607 313099076185260875125965911)
              ·
                refine ⟨469648614277891312688948867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 313099076185260875125965911 469648614277891312688948867)
                ·
                  refine ⟨704472921416836969033423301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 469648614277891312688948867 704472921416836969033423301)
                  ·
                    refine ⟨132088672765656931693766869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 704472921416836969033423301 132088672765656931693766869)
                    ·
                      refine ⟨3095828267945084336572661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 132088672765656931693766869 3095828267945084336572661)
                      ·
                        rfl

theorem cell23_6029104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 7].length) (baseStart_6029104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6029104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6029104 prefixEnd_6029104 := by exact prefixLift 6029104
  have htrace : WordTrace (prefixWord ++ tailWord_6029104) baseStart_6029104 baseEnd_6029104 := by
    simpa [prefixWord, tailWord_6029104, baseEnd_6029104] using wordTrace_append hprefix tailTrace_6029104
  have hstable : (prefixWord ++ tailWord_6029104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6029104).length < 2 ^ (prefixWord ++ tailWord_6029104).sum := by decide
  have hdescent : baseEnd_6029104 < baseStart_6029104 := by decide
  rcases family_descends (prefixWord ++ tailWord_6029104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6029105 : List Nat := [1, 2, 2, 3, 2, 2, 1, 3, 3, 2, 2]
def baseStart_6029105 : Nat := 118140960795 + 6029105 * 2 ^ 59
def prefixEnd_6029105 : Nat := 4983230072969 + 3 ^ 40 * 6029105 * 2
def baseEnd_6029105 : Nat := 3095828781425738832660157

theorem tailTrace_6029105 : CollatzResearch.WordTrace tailWord_6029105 prefixEnd_6029105 3095828781425738832660157 := by
  unfold tailWord_6029105
  simp only [CollatzResearch.WordTrace]
  refine ⟨219899524822589749001368769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146599683215059832667579179 219899524822589749001368769)
  ·
    refine ⟨164924643616942311751026577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219899524822589749001368769 164924643616942311751026577)
    ·
      refine ⟨123693482712706733813269933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164924643616942311751026577 123693482712706733813269933)
      ·
        refine ⟨46385056017265025179976225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123693482712706733813269933 46385056017265025179976225)
        ·
          refine ⟨34788792012948768884982169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46385056017265025179976225 34788792012948768884982169)
          ·
            refine ⟨26091594009711576663736627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34788792012948768884982169 26091594009711576663736627)
            ·
              refine ⟨39137391014567364995604941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26091594009711576663736627 39137391014567364995604941)
              ·
                refine ⟨14676521630462761873351853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39137391014567364995604941 14676521630462761873351853)
                ·
                  refine ⟨5503695611423535702506945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14676521630462761873351853 5503695611423535702506945)
                  ·
                    refine ⟨4127771708567651776880209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5503695611423535702506945 4127771708567651776880209)
                    ·
                      refine ⟨3095828781425738832660157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4127771708567651776880209 3095828781425738832660157)
                      ·
                        rfl

theorem cell23_6029105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 3, 3, 2, 2].length) (baseStart_6029105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6029105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6029105 prefixEnd_6029105 := by exact prefixLift 6029105
  have htrace : WordTrace (prefixWord ++ tailWord_6029105) baseStart_6029105 baseEnd_6029105 := by
    simpa [prefixWord, tailWord_6029105, baseEnd_6029105] using wordTrace_append hprefix tailTrace_6029105
  have hstable : (prefixWord ++ tailWord_6029105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6029105).length < 2 ^ (prefixWord ++ tailWord_6029105).sum := by decide
  have hdescent : baseEnd_6029105 < baseStart_6029105 := by decide
  rcases family_descends (prefixWord ++ tailWord_6029105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6029108 : List Nat := [2, 5, 1, 1, 2, 1, 1, 1, 3, 1, 5]
def baseStart_6029108 : Nat := 118140960795 + 6029108 * 2 ^ 59
def prefixEnd_6029108 : Nat := 4983230072969 + 3 ^ 40 * 6029108 * 2
def baseEnd_6029108 : Nat := 3095830321867702320922643

theorem tailTrace_6029108 : CollatzResearch.WordTrace tailWord_6029108 prefixEnd_6029108 3095830321867702320922643 := by
  unfold tailWord_6029108
  simp only [CollatzResearch.WordTrace]
  refine ⟨109949817120789440256863989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146599756161052587009151985 109949817120789440256863989)
  ·
    refine ⟨10307795355074010024080999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 109949817120789440256863989 10307795355074010024080999)
    ·
      refine ⟨15461693032611015036121499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10307795355074010024080999 15461693032611015036121499)
      ·
        refine ⟨23192539548916522554182249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15461693032611015036121499 23192539548916522554182249)
        ·
          refine ⟨17394404661687391915636687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23192539548916522554182249 17394404661687391915636687)
          ·
            refine ⟨26091606992531087873455031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17394404661687391915636687 26091606992531087873455031)
            ·
              refine ⟨39137410488796631810182547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26091606992531087873455031 39137410488796631810182547)
              ·
                refine ⟨58706115733194947715273821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39137410488796631810182547 58706115733194947715273821)
                ·
                  refine ⟨22014793399948105393227683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58706115733194947715273821 22014793399948105393227683)
                  ·
                    refine ⟨33022190099922158089841525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22014793399948105393227683 33022190099922158089841525)
                    ·
                      refine ⟨3095830321867702320922643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33022190099922158089841525 3095830321867702320922643)
                      ·
                        rfl

theorem cell23_6029108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 1, 3, 1, 5].length) (baseStart_6029108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6029108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6029108 prefixEnd_6029108 := by exact prefixLift 6029108
  have htrace : WordTrace (prefixWord ++ tailWord_6029108) baseStart_6029108 baseEnd_6029108 := by
    simpa [prefixWord, tailWord_6029108, baseEnd_6029108] using wordTrace_append hprefix tailTrace_6029108
  have hstable : (prefixWord ++ tailWord_6029108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6029108).length < 2 ^ (prefixWord ++ tailWord_6029108).sum := by decide
  have hdescent : baseEnd_6029108 < baseStart_6029108 := by decide
  rcases family_descends (prefixWord ++ tailWord_6029108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6029118 : List Nat := [4, 2, 1, 2, 2, 2, 1, 1, 1, 1, 6]
def baseStart_6029118 : Nat := 118140960795 + 6029118 * 2 ^ 59
def prefixEnd_6029118 : Nat := 4983230072969 + 3 ^ 40 * 6029118 * 2
def baseEnd_6029118 : Nat := 3095835456674247281797597

theorem tailTrace_6029118 : CollatzResearch.WordTrace tailWord_6029118 prefixEnd_6029118 3095835456674247281797597 := by
  unfold tailWord_6029118
  simp only [CollatzResearch.WordTrace]
  refine ⟨27487499871442831527699001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 146599999314361768147728005 27487499871442831527699001)
  ·
    refine ⟨20615624903582123645774251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27487499871442831527699001 20615624903582123645774251)
    ·
      refine ⟨30923437355373185468661377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20615624903582123645774251 30923437355373185468661377)
      ·
        refine ⟨23192578016529889101496033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30923437355373185468661377 23192578016529889101496033)
        ·
          refine ⟨17394433512397416826122025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23192578016529889101496033 17394433512397416826122025)
          ·
            refine ⟨13045825134298062619591519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17394433512397416826122025 13045825134298062619591519)
            ·
              refine ⟨19568737701447093929387279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13045825134298062619591519 19568737701447093929387279)
              ·
                refine ⟨29353106552170640894080919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19568737701447093929387279 29353106552170640894080919)
                ·
                  refine ⟨44029659828255961341121379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29353106552170640894080919 44029659828255961341121379)
                  ·
                    refine ⟨66044489742383942011682069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 44029659828255961341121379 66044489742383942011682069)
                    ·
                      refine ⟨3095835456674247281797597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 66044489742383942011682069 3095835456674247281797597)
                      ·
                        rfl

theorem cell23_6029118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 1, 1, 1, 1, 6].length) (baseStart_6029118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6029118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6029118 prefixEnd_6029118 := by exact prefixLift 6029118
  have htrace : WordTrace (prefixWord ++ tailWord_6029118) baseStart_6029118 baseEnd_6029118 := by
    simpa [prefixWord, tailWord_6029118, baseEnd_6029118] using wordTrace_append hprefix tailTrace_6029118
  have hstable : (prefixWord ++ tailWord_6029118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6029118).length < 2 ^ (prefixWord ++ tailWord_6029118).sum := by decide
  have hdescent : baseEnd_6029118 < baseStart_6029118 := by decide
  rcases family_descends (prefixWord ++ tailWord_6029118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6029128 : List Nat := [2, 1, 3, 1, 1, 6, 2, 7]
def baseStart_6029128 : Nat := 118140960795 + 6029128 * 2 ^ 59
def prefixEnd_6029128 : Nat := 4983230072969 + 3 ^ 40 * 6029128 * 2
def baseEnd_6029128 : Nat := 114660762647436749728613

theorem tailTrace_6029128 : CollatzResearch.WordTrace tailWord_6029128 prefixEnd_6029128 114660762647436749728613 := by
  unfold tailWord_6029128
  simp only [CollatzResearch.WordTrace]
  refine ⟨109950181850753211964728019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146600242467670949286304025 109950181850753211964728019)
  ·
    refine ⟨164925272776129817947092029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109950181850753211964728019 164925272776129817947092029)
    ·
      refine ⟨61846977291048681730159511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 164925272776129817947092029 61846977291048681730159511)
      ·
        refine ⟨92770465936573022595239267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61846977291048681730159511 92770465936573022595239267)
        ·
          refine ⟨139155698904859533892858901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92770465936573022595239267 139155698904859533892858901)
          ·
            refine ⟨6522923386165290651227761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 139155698904859533892858901 6522923386165290651227761)
            ·
              refine ⟨4892192539623967988420821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6522923386165290651227761 4892192539623967988420821)
              ·
                refine ⟨114660762647436749728613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4892192539623967988420821 114660762647436749728613)
                ·
                  rfl

theorem cell23_6029128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 2, 7].length) (baseStart_6029128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6029128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6029128 prefixEnd_6029128 := by exact prefixLift 6029128
  have htrace : WordTrace (prefixWord ++ tailWord_6029128) baseStart_6029128 baseEnd_6029128 := by
    simpa [prefixWord, tailWord_6029128, baseEnd_6029128] using wordTrace_append hprefix tailTrace_6029128
  have hstable : (prefixWord ++ tailWord_6029128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6029128).length < 2 ^ (prefixWord ++ tailWord_6029128).sum := by decide
  have hdescent : baseEnd_6029128 < baseStart_6029128 := by decide
  rcases family_descends (prefixWord ++ tailWord_6029128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6029156 : List Nat := [2, 3, 1, 1, 5, 1, 3, 2, 1, 2, 2]
def baseStart_6029156 : Nat := 118140960795 + 6029156 * 2 ^ 59
def prefixEnd_6029156 : Nat := 4983230072969 + 3 ^ 40 * 6029156 * 2
def baseEnd_6029156 : Nat := 3095854968939118133122423

theorem tailTrace_6029156 : CollatzResearch.WordTrace tailWord_6029156 prefixEnd_6029156 3095854968939118133122423 := by
  unfold tailWord_6029156
  simp only [CollatzResearch.WordTrace]
  refine ⟨109950692472702492355737661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146600923296936656474316881 109950692472702492355737661)
  ·
    refine ⟨41231509677263434633401623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109950692472702492355737661 41231509677263434633401623)
    ·
      refine ⟨61847264515895151950102435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41231509677263434633401623 61847264515895151950102435)
      ·
        refine ⟨92770896773842727925153653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61847264515895151950102435 92770896773842727925153653)
        ·
          refine ⟨8697271572547755742983155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 92770896773842727925153653 8697271572547755742983155)
          ·
            refine ⟨13045907358821633614474733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8697271572547755742983155 13045907358821633614474733)
            ·
              refine ⟨4892215259558112605428025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13045907358821633614474733 4892215259558112605428025)
              ·
                refine ⟨3669161444668584454071019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4892215259558112605428025 3669161444668584454071019)
                ·
                  refine ⟨5503742167002876681106529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3669161444668584454071019 5503742167002876681106529)
                  ·
                    refine ⟨4127806625252157510829897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5503742167002876681106529 4127806625252157510829897)
                    ·
                      refine ⟨3095854968939118133122423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4127806625252157510829897 3095854968939118133122423)
                      ·
                        rfl

theorem cell23_6029156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 3, 2, 1, 2, 2].length) (baseStart_6029156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6029156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6029156 prefixEnd_6029156 := by exact prefixLift 6029156
  have htrace : WordTrace (prefixWord ++ tailWord_6029156) baseStart_6029156 baseEnd_6029156 := by
    simpa [prefixWord, tailWord_6029156, baseEnd_6029156] using wordTrace_append hprefix tailTrace_6029156
  have hstable : (prefixWord ++ tailWord_6029156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6029156).length < 2 ^ (prefixWord ++ tailWord_6029156).sum := by decide
  have hdescent : baseEnd_6029156 < baseStart_6029156 := by decide
  rcases family_descends (prefixWord ++ tailWord_6029156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6029231 : List Nat := [1, 1, 2, 1, 2, 2, 4, 2, 1, 7]
def baseStart_6029231 : Nat := 118140960795 + 6029231 * 2 ^ 59
def prefixEnd_6029231 : Nat := 4983230072969 + 3 ^ 40 * 6029231 * 2
def baseEnd_6029231 : Nat := 1031964493329401779894859

theorem tailTrace_6029231 : CollatzResearch.WordTrace tailWord_6029231 prefixEnd_6029231 1031964493329401779894859 := by
  unfold tailWord_6029231
  simp only [CollatzResearch.WordTrace]
  refine ⟨219904120420133272520455547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146602746946755515013637031 219904120420133272520455547)
  ·
    refine ⟨329856180630199908780683321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219904120420133272520455547 329856180630199908780683321)
    ·
      refine ⟨247392135472649931585512491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 329856180630199908780683321 247392135472649931585512491)
      ·
        refine ⟨371088203208974897378268737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 247392135472649931585512491 371088203208974897378268737)
        ·
          refine ⟨278316152406731173033701553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 371088203208974897378268737 278316152406731173033701553)
          ·
            refine ⟨208737114305048379775276165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 278316152406731173033701553 208737114305048379775276165)
            ·
              refine ⟨39138208932196571207864281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 208737114305048379775276165 39138208932196571207864281)
              ·
                refine ⟨29353656699147428405898211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39138208932196571207864281 29353656699147428405898211)
                ·
                  refine ⟨44030485048721142608847317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29353656699147428405898211 44030485048721142608847317)
                  ·
                    refine ⟨1031964493329401779894859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44030485048721142608847317 1031964493329401779894859)
                    ·
                      rfl

theorem cell23_6029231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 2, 1, 7].length) (baseStart_6029231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6029231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6029231 prefixEnd_6029231 := by exact prefixLift 6029231
  have htrace : WordTrace (prefixWord ++ tailWord_6029231) baseStart_6029231 baseEnd_6029231 := by
    simpa [prefixWord, tailWord_6029231, baseEnd_6029231] using wordTrace_append hprefix tailTrace_6029231
  have hstable : (prefixWord ++ tailWord_6029231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6029231).length < 2 ^ (prefixWord ++ tailWord_6029231).sum := by decide
  have hdescent : baseEnd_6029231 < baseStart_6029231 := by decide
  rcases family_descends (prefixWord ++ tailWord_6029231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6029322 : List Nat := [3, 1, 2, 2, 4, 1, 1, 2, 2, 2, 3]
def baseStart_6029322 : Nat := 118140960795 + 6029322 * 2 ^ 59
def prefixEnd_6029322 : Nat := 4983230072969 + 3 ^ 40 * 6029322 * 2
def baseEnd_6029322 : Nat := 3095940206727764483646659

theorem tailTrace_6029322 : CollatzResearch.WordTrace tailWord_6029322 prefixEnd_6029322 3095940206727764483646659 := by
  unfold tailWord_6029322
  simp only [CollatzResearch.WordTrace]
  refine ⟨54976859865700898765504555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146604959641869063374678813 54976859865700898765504555)
  ·
    refine ⟨82465289798551348148256833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54976859865700898765504555 82465289798551348148256833)
    ·
      refine ⟨61848967348913511111192625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82465289798551348148256833 61848967348913511111192625)
      ·
        refine ⟨46386725511685133333394469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61848967348913511111192625 46386725511685133333394469)
        ·
          refine ⟨8697511033440962500011463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46386725511685133333394469 8697511033440962500011463)
          ·
            refine ⟨13046266550161443750017195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8697511033440962500011463 13046266550161443750017195)
            ·
              refine ⟨19569399825242165625025793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13046266550161443750017195 19569399825242165625025793)
              ·
                refine ⟨14677049868931624218769345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19569399825242165625025793 14677049868931624218769345)
                ·
                  refine ⟨11007787401698718164077009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14677049868931624218769345 11007787401698718164077009)
                  ·
                    refine ⟨8255840551274038623057757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11007787401698718164077009 8255840551274038623057757)
                    ·
                      refine ⟨3095940206727764483646659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8255840551274038623057757 3095940206727764483646659)
                      ·
                        rfl

theorem cell23_6029322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 1, 2, 2, 2, 3].length) (baseStart_6029322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6029322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6029322 prefixEnd_6029322 := by exact prefixLift 6029322
  have htrace : WordTrace (prefixWord ++ tailWord_6029322) baseStart_6029322 baseEnd_6029322 := by
    simpa [prefixWord, tailWord_6029322, baseEnd_6029322] using wordTrace_append hprefix tailTrace_6029322
  have hstable : (prefixWord ++ tailWord_6029322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6029322).length < 2 ^ (prefixWord ++ tailWord_6029322).sum := by decide
  have hdescent : baseEnd_6029322 < baseStart_6029322 := by decide
  rcases family_descends (prefixWord ++ tailWord_6029322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6029362 : List Nat := [3, 2, 1, 1, 2, 3, 1, 3, 2, 3, 2]
def baseStart_6029362 : Nat := 118140960795 + 6029362 * 2 ^ 59
def prefixEnd_6029362 : Nat := 4983230072969 + 3 ^ 40 * 6029362 * 2
def baseEnd_6029362 : Nat := 3095960745953944327146475

theorem tailTrace_6029362 : CollatzResearch.WordTrace tailWord_6029362 prefixEnd_6029362 3095960745953944327146475 := by
  unfold tailWord_6029362
  simp only [CollatzResearch.WordTrace]
  refine ⟨54977224595664670473368585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146605932255105787928982893 54977224595664670473368585)
  ·
    refine ⟨41232918446748502855026439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54977224595664670473368585 41232918446748502855026439)
    ·
      refine ⟨61849377670122754282539659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41232918446748502855026439 61849377670122754282539659)
      ·
        refine ⟨92774066505184131423809489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61849377670122754282539659 92774066505184131423809489)
        ·
          refine ⟨69580549878888098567857117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92774066505184131423809489 69580549878888098567857117)
          ·
            refine ⟨26092706204583036962946419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69580549878888098567857117 26092706204583036962946419)
            ·
              refine ⟨39139059306874555444419629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26092706204583036962946419 39139059306874555444419629)
              ·
                refine ⟨14677147240077958291657361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39139059306874555444419629 14677147240077958291657361)
                ·
                  refine ⟨11007860430058468718743021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14677147240077958291657361 11007860430058468718743021)
                  ·
                    refine ⟨4127947661271925769528633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11007860430058468718743021 4127947661271925769528633)
                    ·
                      refine ⟨3095960745953944327146475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4127947661271925769528633 3095960745953944327146475)
                      ·
                        rfl

theorem cell23_6029362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 3, 2, 3, 2].length) (baseStart_6029362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6029362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6029362 prefixEnd_6029362 := by exact prefixLift 6029362
  have htrace : WordTrace (prefixWord ++ tailWord_6029362) baseStart_6029362 baseEnd_6029362 := by
    simpa [prefixWord, tailWord_6029362, baseEnd_6029362] using wordTrace_append hprefix tailTrace_6029362
  have hstable : (prefixWord ++ tailWord_6029362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6029362).length < 2 ^ (prefixWord ++ tailWord_6029362).sum := by decide
  have hdescent : baseEnd_6029362 < baseStart_6029362 := by decide
  rcases family_descends (prefixWord ++ tailWord_6029362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6029372 : List Nat := [2, 2, 2, 2, 2, 1, 5, 1, 1, 5]
def baseStart_6029372 : Nat := 118140960795 + 6029372 * 2 ^ 59
def prefixEnd_6029372 : Nat := 4983230072969 + 3 ^ 40 * 6029372 * 2
def baseEnd_6029372 : Nat := 1031988626920163096007143

theorem tailTrace_6029372 : CollatzResearch.WordTrace tailWord_6029372 prefixEnd_6029372 1031988626920163096007143 := by
  unfold tailWord_6029372
  simp only [CollatzResearch.WordTrace]
  refine ⟨109954631556311226800669185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146606175408414969067558913 109954631556311226800669185)
  ·
    refine ⟨82465973667233420100501889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109954631556311226800669185 82465973667233420100501889)
    ·
      refine ⟨61849480250425065075376417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82465973667233420100501889 61849480250425065075376417)
      ·
        refine ⟨46387110187818798806532313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61849480250425065075376417 46387110187818798806532313)
        ·
          refine ⟨34790332640864099104899235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46387110187818798806532313 34790332640864099104899235)
          ·
            refine ⟨52185498961296148657348853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34790332640864099104899235 52185498961296148657348853)
            ·
              refine ⟨4892390527621513936626455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 52185498961296148657348853 4892390527621513936626455)
              ·
                refine ⟨7338585791432270904939683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4892390527621513936626455 7338585791432270904939683)
                ·
                  refine ⟨11007878687148406357409525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7338585791432270904939683 11007878687148406357409525)
                  ·
                    refine ⟨1031988626920163096007143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11007878687148406357409525 1031988626920163096007143)
                    ·
                      rfl

theorem cell23_6029372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 5, 1, 1, 5].length) (baseStart_6029372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6029372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6029372 prefixEnd_6029372 := by exact prefixLift 6029372
  have htrace : WordTrace (prefixWord ++ tailWord_6029372) baseStart_6029372 baseEnd_6029372 := by
    simpa [prefixWord, tailWord_6029372, baseEnd_6029372] using wordTrace_append hprefix tailTrace_6029372
  have hstable : (prefixWord ++ tailWord_6029372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6029372).length < 2 ^ (prefixWord ++ tailWord_6029372).sum := by decide
  have hdescent : baseEnd_6029372 < baseStart_6029372 := by decide
  rcases family_descends (prefixWord ++ tailWord_6029372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6029375 : List Nat := [1, 1, 2, 2, 3, 1, 2, 5, 1, 1, 4]
def baseStart_6029375 : Nat := 118140960795 + 6029375 * 2 ^ 59
def prefixEnd_6029375 : Nat := 4983230072969 + 3 ^ 40 * 6029375 * 2
def baseEnd_6029375 : Nat := 3095967421202452776283915

theorem tailTrace_6029375 : CollatzResearch.WordTrace tailWord_6029375 prefixEnd_6029375 3095967421202452776283915 := by
  unfold tailWord_6029375
  simp only [CollatzResearch.WordTrace]
  refine ⟨219909372531611585113697579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146606248354407723409131719 219909372531611585113697579)
  ·
    refine ⟨329864058797417377670546369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219909372531611585113697579 329864058797417377670546369)
    ·
      refine ⟨247398044098063033252909777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 329864058797417377670546369 247398044098063033252909777)
      ·
        refine ⟨185548533073547274939682333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 247398044098063033252909777 185548533073547274939682333)
        ·
          refine ⟨69580699902580228102380875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 185548533073547274939682333 69580699902580228102380875)
          ·
            refine ⟨104371049853870342153571313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69580699902580228102380875 104371049853870342153571313)
            ·
              refine ⟨78278287390402756615178485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104371049853870342153571313 78278287390402756615178485)
              ·
                refine ⟨7338589442850258432672983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 78278287390402756615178485 7338589442850258432672983)
                ·
                  refine ⟨11007884164275387649009475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7338589442850258432672983 11007884164275387649009475)
                  ·
                    refine ⟨16511826246413081473514213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11007884164275387649009475 16511826246413081473514213)
                    ·
                      refine ⟨3095967421202452776283915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16511826246413081473514213 3095967421202452776283915)
                      ·
                        rfl

theorem cell23_6029375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 5, 1, 1, 4].length) (baseStart_6029375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6029375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6029375 prefixEnd_6029375 := by exact prefixLift 6029375
  have htrace : WordTrace (prefixWord ++ tailWord_6029375) baseStart_6029375 baseEnd_6029375 := by
    simpa [prefixWord, tailWord_6029375, baseEnd_6029375] using wordTrace_append hprefix tailTrace_6029375
  have hstable : (prefixWord ++ tailWord_6029375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6029375).length < 2 ^ (prefixWord ++ tailWord_6029375).sum := by decide
  have hdescent : baseEnd_6029375 < baseStart_6029375 := by decide
  rcases family_descends (prefixWord ++ tailWord_6029375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6029388 : List Nat := [2, 2, 1, 3, 1, 1, 2, 1, 3, 1, 6]
def baseStart_6029388 : Nat := 118140960795 + 6029388 * 2 ^ 59
def prefixEnd_6029388 : Nat := 4983230072969 + 3 ^ 40 * 6029388 * 2
def baseEnd_6029388 : Nat := 3095974096450961225421355

theorem tailTrace_6029388 : CollatzResearch.WordTrace tailWord_6029388 prefixEnd_6029388 3095974096450961225421355 := by
  unfold tailWord_6029388
  simp only [CollatzResearch.WordTrace]
  refine ⟨109954923340282244166960409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146606564453709658889280545 109954923340282244166960409)
  ·
    refine ⟨82466192505211683125220307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109954923340282244166960409 82466192505211683125220307)
    ·
      refine ⟨123699288757817524687830461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82466192505211683125220307 123699288757817524687830461)
      ·
        refine ⟨46387233284181571757936423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123699288757817524687830461 46387233284181571757936423)
        ·
          refine ⟨69580849926272357636904635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46387233284181571757936423 69580849926272357636904635)
          ·
            refine ⟨104371274889408536455356953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69580849926272357636904635 104371274889408536455356953)
            ·
              refine ⟨78278456167056402341517715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104371274889408536455356953 78278456167056402341517715)
              ·
                refine ⟨117417684250584603512276573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78278456167056402341517715 117417684250584603512276573)
                ·
                  refine ⟨44031631593969226317103715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 117417684250584603512276573 44031631593969226317103715)
                  ·
                    refine ⟨66047447390953839475655573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 44031631593969226317103715 66047447390953839475655573)
                    ·
                      refine ⟨3095974096450961225421355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 66047447390953839475655573 3095974096450961225421355)
                      ·
                        rfl

theorem cell23_6029388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 1, 3, 1, 6].length) (baseStart_6029388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6029388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6029388 prefixEnd_6029388 := by exact prefixLift 6029388
  have htrace : WordTrace (prefixWord ++ tailWord_6029388) baseStart_6029388 baseEnd_6029388 := by
    simpa [prefixWord, tailWord_6029388, baseEnd_6029388] using wordTrace_append hprefix tailTrace_6029388
  have hstable : (prefixWord ++ tailWord_6029388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6029388).length < 2 ^ (prefixWord ++ tailWord_6029388).sum := by decide
  have hdescent : baseEnd_6029388 < baseStart_6029388 := by decide
  rcases family_descends (prefixWord ++ tailWord_6029388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6029415 : List Nat := [1, 1, 5, 1, 1, 2, 5, 7]
def baseStart_6029415 : Nat := 118140960795 + 6029415 * 2 ^ 59
def prefixEnd_6029415 : Nat := 4983230072969 + 3 ^ 40 * 6029415 * 2
def baseEnd_6029415 : Nat := 114666220756616022954953

theorem tailTrace_6029415 : CollatzResearch.WordTrace tailWord_6029415 prefixEnd_6029415 114666220756616022954953 := by
  unfold tailWord_6029415
  simp only [CollatzResearch.WordTrace]
  refine ⟨219910831451466671945153699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146607220967644447963435799 219910831451466671945153699)
  ·
    refine ⟨329866247177200007917730549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219910831451466671945153699 329866247177200007917730549)
    ·
      refine ⟨30924960672862500742287239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 329866247177200007917730549 30924960672862500742287239)
      ·
        refine ⟨46387441009293751113430859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30924960672862500742287239 46387441009293751113430859)
        ·
          refine ⟨69581161513940626670146289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46387441009293751113430859 69581161513940626670146289)
          ·
            refine ⟨52185871135455470002609717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69581161513940626670146289 52185871135455470002609717)
            ·
              refine ⟨4892425418948950312744661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 52185871135455470002609717 4892425418948950312744661)
              ·
                refine ⟨114666220756616022954953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4892425418948950312744661 114666220756616022954953)
                ·
                  rfl

theorem cell23_6029415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 5, 7].length) (baseStart_6029415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6029415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6029415 prefixEnd_6029415 := by exact prefixLift 6029415
  have htrace : WordTrace (prefixWord ++ tailWord_6029415) baseStart_6029415 baseEnd_6029415 := by
    simpa [prefixWord, tailWord_6029415, baseEnd_6029415] using wordTrace_append hprefix tailTrace_6029415
  have hstable : (prefixWord ++ tailWord_6029415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6029415).length < 2 ^ (prefixWord ++ tailWord_6029415).sum := by decide
  have hdescent : baseEnd_6029415 < baseStart_6029415 := by decide
  rcases family_descends (prefixWord ++ tailWord_6029415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6029425 : List Nat := [1, 2, 2, 2, 1, 1, 3, 4, 1, 3, 3]
def baseStart_6029425 : Nat := 118140960795 + 6029425 * 2 ^ 59
def prefixEnd_6029425 : Nat := 4983230072969 + 3 ^ 40 * 6029425 * 2
def baseEnd_6029425 : Nat := 3095993095235177580658685

theorem tailTrace_6029425 : CollatzResearch.WordTrace tailWord_6029425 prefixEnd_6029425 3095993095235177580658685 := by
  unfold tailWord_6029425
  simp only [CollatzResearch.WordTrace]
  refine ⟨219911196181430443653017729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146607464120953629102011819 219911196181430443653017729)
  ·
    refine ⟨164933397136072832739763297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219911196181430443653017729 164933397136072832739763297)
    ·
      refine ⟨123700047852054624554822473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164933397136072832739763297 123700047852054624554822473)
      ·
        refine ⟨92775035889040968416116855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123700047852054624554822473 92775035889040968416116855)
        ·
          refine ⟨139162553833561452624175283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92775035889040968416116855 139162553833561452624175283)
          ·
            refine ⟨208743830750342178936262925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139162553833561452624175283 208743830750342178936262925)
            ·
              refine ⟨78278936531378317101098597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 208743830750342178936262925 78278936531378317101098597)
              ·
                refine ⟨14677300599633434456455987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 78278936531378317101098597 14677300599633434456455987)
                ·
                  refine ⟨22015950899450151684683981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14677300599633434456455987 22015950899450151684683981)
                  ·
                    refine ⟨8255981587293806881756493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22015950899450151684683981 8255981587293806881756493)
                    ·
                      refine ⟨3095993095235177580658685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8255981587293806881756493 3095993095235177580658685)
                      ·
                        rfl

theorem cell23_6029425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 4, 1, 3, 3].length) (baseStart_6029425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6029425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6029425 prefixEnd_6029425 := by exact prefixLift 6029425
  have htrace : WordTrace (prefixWord ++ tailWord_6029425) baseStart_6029425 baseEnd_6029425 := by
    simpa [prefixWord, tailWord_6029425, baseEnd_6029425] using wordTrace_append hprefix tailTrace_6029425
  have hstable : (prefixWord ++ tailWord_6029425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6029425).length < 2 ^ (prefixWord ++ tailWord_6029425).sum := by decide
  have hdescent : baseEnd_6029425 < baseStart_6029425 := by decide
  rcases family_descends (prefixWord ++ tailWord_6029425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6029426 : List Nat := [3, 2, 1, 2, 2, 2, 1, 5, 1, 2, 2]
def baseStart_6029426 : Nat := 118140960795 + 6029426 * 2 ^ 59
def prefixEnd_6029426 : Nat := 4983230072969 + 3 ^ 40 * 6029426 * 2
def baseEnd_6029426 : Nat := 3095993608715832076746181

theorem tailTrace_6029426 : CollatzResearch.WordTrace tailWord_6029426 prefixEnd_6029426 3095993608715832076746181 := by
  unfold tailWord_6029426
  simp only [CollatzResearch.WordTrace]
  refine ⟨54977808163606705205951033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146607488436284547215869421 54977808163606705205951033)
  ·
    refine ⟨41233356122705028904463275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54977808163606705205951033 41233356122705028904463275)
    ·
      refine ⟨61850034184057543356694913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41233356122705028904463275 61850034184057543356694913)
      ·
        refine ⟨46387525638043157517521185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61850034184057543356694913 46387525638043157517521185)
        ·
          refine ⟨34790644228532368138140889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46387525638043157517521185 34790644228532368138140889)
          ·
            refine ⟨26092983171399276103605667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34790644228532368138140889 26092983171399276103605667)
            ·
              refine ⟨39139474757098914155408501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26092983171399276103605667 39139474757098914155408501)
              ·
                refine ⟨3669325758478023202069547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39139474757098914155408501 3669325758478023202069547)
                ·
                  refine ⟨5503988637717034803104321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3669325758478023202069547 5503988637717034803104321)
                  ·
                    refine ⟨4127991478287776102328241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5503988637717034803104321 4127991478287776102328241)
                    ·
                      refine ⟨3095993608715832076746181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4127991478287776102328241 3095993608715832076746181)
                      ·
                        rfl

theorem cell23_6029426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 5, 1, 2, 2].length) (baseStart_6029426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6029426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6029426 prefixEnd_6029426 := by exact prefixLift 6029426
  have htrace : WordTrace (prefixWord ++ tailWord_6029426) baseStart_6029426 baseEnd_6029426 := by
    simpa [prefixWord, tailWord_6029426, baseEnd_6029426] using wordTrace_append hprefix tailTrace_6029426
  have hstable : (prefixWord ++ tailWord_6029426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6029426).length < 2 ^ (prefixWord ++ tailWord_6029426).sum := by decide
  have hdescent : baseEnd_6029426 < baseStart_6029426 := by decide
  rcases family_descends (prefixWord ++ tailWord_6029426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6029469 : List Nat := [1, 4, 2, 1, 1, 3, 1, 4, 1, 3, 2]
def baseStart_6029469 : Nat := 118140960795 + 6029469 * 2 ^ 59
def prefixEnd_6029469 : Nat := 4983230072969 + 3 ^ 40 * 6029469 * 2
def baseEnd_6029469 : Nat := 3096015688383975408508483

theorem tailTrace_6029469 : CollatzResearch.WordTrace tailWord_6029469 prefixEnd_6029469 3096015688383975408508483 := by
  unfold tailWord_6029469
  simp only [CollatzResearch.WordTrace]
  refine ⟨219912800993271039167619461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146608533995514026111746307 219912800993271039167619461)
  ·
    refine ⟨41233650186238319843928649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 219912800993271039167619461 41233650186238319843928649)
    ·
      refine ⟨30925237639678739882946487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41233650186238319843928649 30925237639678739882946487)
      ·
        refine ⟨46387856459518109824419731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30925237639678739882946487 46387856459518109824419731)
        ·
          refine ⟨69581784689277164736629597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46387856459518109824419731 69581784689277164736629597)
          ·
            refine ⟨26093169258478936776236099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69581784689277164736629597 26093169258478936776236099)
            ·
              refine ⟨39139753887718405164354149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26093169258478936776236099 39139753887718405164354149)
              ·
                refine ⟨7338703853947200968316403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39139753887718405164354149 7338703853947200968316403)
                ·
                  refine ⟨11008055780920801452474605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7338703853947200968316403 11008055780920801452474605)
                  ·
                    refine ⟨4128020917845300544677977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11008055780920801452474605 4128020917845300544677977)
                    ·
                      refine ⟨3096015688383975408508483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4128020917845300544677977 3096015688383975408508483)
                      ·
                        rfl

theorem cell23_6029469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 4, 1, 3, 2].length) (baseStart_6029469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6029469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6029469 prefixEnd_6029469 := by exact prefixLift 6029469
  have htrace : WordTrace (prefixWord ++ tailWord_6029469) baseStart_6029469 baseEnd_6029469 := by
    simpa [prefixWord, tailWord_6029469, baseEnd_6029469] using wordTrace_append hprefix tailTrace_6029469
  have hstable : (prefixWord ++ tailWord_6029469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6029469).length < 2 ^ (prefixWord ++ tailWord_6029469).sum := by decide
  have hdescent : baseEnd_6029469 < baseStart_6029469 := by decide
  rcases family_descends (prefixWord ++ tailWord_6029469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6029499 : List Nat := [1, 1, 1, 1, 1, 2, 6, 4, 2, 2, 2]
def baseStart_6029499 : Nat := 118140960795 + 6029499 * 2 ^ 59
def prefixEnd_6029499 : Nat := 4983230072969 + 3 ^ 40 * 6029499 * 2
def baseEnd_6029499 : Nat := 3096031092803610291133345

theorem tailTrace_6029499 : CollatzResearch.WordTrace tailWord_6029499 prefixEnd_6029499 3096031092803610291133345 := by
  unfold tailWord_6029499
  simp only [CollatzResearch.WordTrace]
  refine ⟨219913895183162354291211551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146609263455441569527474367 219913895183162354291211551)
  ·
    refine ⟨329870842774743531436817327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219913895183162354291211551 329870842774743531436817327)
    ·
      refine ⟨494806264162115297155225991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 329870842774743531436817327 494806264162115297155225991)
      ·
        refine ⟨742209396243172945732838987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 494806264162115297155225991 742209396243172945732838987)
        ·
          refine ⟨1113314094364759418599258481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 742209396243172945732838987 1113314094364759418599258481)
          ·
            refine ⟨834985570773569563949443861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1113314094364759418599258481 834985570773569563949443861)
            ·
              refine ⟨39139948630011073310130181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 834985570773569563949443861 39139948630011073310130181)
              ·
                refine ⟨7338740368127076245649409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39139948630011073310130181 7338740368127076245649409)
                ·
                  refine ⟨5504055276095307184237057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7338740368127076245649409 5504055276095307184237057)
                  ·
                    refine ⟨4128041457071480388177793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5504055276095307184237057 4128041457071480388177793)
                    ·
                      refine ⟨3096031092803610291133345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4128041457071480388177793 3096031092803610291133345)
                      ·
                        rfl

theorem cell23_6029499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 4, 2, 2, 2].length) (baseStart_6029499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6029499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6029499 prefixEnd_6029499 := by exact prefixLift 6029499
  have htrace : WordTrace (prefixWord ++ tailWord_6029499) baseStart_6029499 baseEnd_6029499 := by
    simpa [prefixWord, tailWord_6029499, baseEnd_6029499] using wordTrace_append hprefix tailTrace_6029499
  have hstable : (prefixWord ++ tailWord_6029499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6029499).length < 2 ^ (prefixWord ++ tailWord_6029499).sum := by decide
  have hdescent : baseEnd_6029499 < baseStart_6029499 := by decide
  rcases family_descends (prefixWord ++ tailWord_6029499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6029515 : List Nat := [1, 1, 1, 1, 3, 2, 4, 1, 1, 5, 3]
def baseStart_6029515 : Nat := 118140960795 + 6029515 * 2 ^ 59
def prefixEnd_6029515 : Nat := 4983230072969 + 3 ^ 40 * 6029515 * 2
def baseEnd_6029515 : Nat := 3096039308494082228533271

theorem tailTrace_6029515 : CollatzResearch.WordTrace tailWord_6029515 prefixEnd_6029515 3096039308494082228533271 := by
  unfold tailWord_6029515
  simp only [CollatzResearch.WordTrace]
  refine ⟨219914478751104389023793999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146609652500736259349195999 219914478751104389023793999)
  ·
    refine ⟨329871718126656583535690999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219914478751104389023793999 329871718126656583535690999)
    ·
      refine ⟨494807577189984875303536499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 329871718126656583535690999 494807577189984875303536499)
      ·
        refine ⟨742211365784977312955304749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 494807577189984875303536499 742211365784977312955304749)
        ·
          refine ⟨278329262169366492358239281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 742211365784977312955304749 278329262169366492358239281)
          ·
            refine ⟨208746946627024869268679461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 278329262169366492358239281 208746946627024869268679461)
            ·
              refine ⟨39140052492567162987877399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 208746946627024869268679461 39140052492567162987877399)
              ·
                refine ⟨58710078738850744481816099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39140052492567162987877399 58710078738850744481816099)
                ·
                  refine ⟨88065118108276116722724149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58710078738850744481816099 88065118108276116722724149)
                  ·
                    refine ⟨8256104822650885942755389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 88065118108276116722724149 8256104822650885942755389)
                    ·
                      refine ⟨3096039308494082228533271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8256104822650885942755389 3096039308494082228533271)
                      ·
                        rfl

theorem cell23_6029515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 1, 1, 5, 3].length) (baseStart_6029515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6029515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6029515 prefixEnd_6029515 := by exact prefixLift 6029515
  have htrace : WordTrace (prefixWord ++ tailWord_6029515) baseStart_6029515 baseEnd_6029515 := by
    simpa [prefixWord, tailWord_6029515, baseEnd_6029515] using wordTrace_append hprefix tailTrace_6029515
  have hstable : (prefixWord ++ tailWord_6029515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6029515).length < 2 ^ (prefixWord ++ tailWord_6029515).sum := by decide
  have hdescent : baseEnd_6029515 < baseStart_6029515 := by decide
  rcases family_descends (prefixWord ++ tailWord_6029515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6029592 : List Nat := [2, 1, 2, 3, 1, 2, 3, 1, 1, 4, 3]
def baseStart_6029592 : Nat := 118140960795 + 6029592 * 2 ^ 59
def prefixEnd_6029592 : Nat := 4983230072969 + 3 ^ 40 * 6029592 * 2
def baseEnd_6029592 : Nat := 3096078846504478427270417

theorem tailTrace_6029592 : CollatzResearch.WordTrace tailWord_6029592 prefixEnd_6029592 3096078846504478427270417 := by
  unfold tailWord_6029592
  simp only [CollatzResearch.WordTrace]
  refine ⟨109958643585912715587173515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146611524781216954116231353 109958643585912715587173515)
  ·
    refine ⟨164937965378869073380760273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109958643585912715587173515 164937965378869073380760273)
    ·
      refine ⟨123703474034151805035570205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164937965378869073380760273 123703474034151805035570205)
      ·
        refine ⟨46388802762806926888338827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123703474034151805035570205 46388802762806926888338827)
        ·
          refine ⟨69583204144210390332508241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46388802762806926888338827 69583204144210390332508241)
          ·
            refine ⟨52187403108157792749381181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69583204144210390332508241 52187403108157792749381181)
            ·
              refine ⟨19570276165559172281017943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52187403108157792749381181 19570276165559172281017943)
              ·
                refine ⟨29355414248338758421526915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19570276165559172281017943 29355414248338758421526915)
                ·
                  refine ⟨44033121372508137632290373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29355414248338758421526915 44033121372508137632290373)
                  ·
                    refine ⟨8256210257345275806054445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 44033121372508137632290373 8256210257345275806054445)
                    ·
                      refine ⟨3096078846504478427270417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8256210257345275806054445 3096078846504478427270417)
                      ·
                        rfl

theorem cell23_6029592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 1, 1, 4, 3].length) (baseStart_6029592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6029592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6029592 prefixEnd_6029592 := by exact prefixLift 6029592
  have htrace : WordTrace (prefixWord ++ tailWord_6029592) baseStart_6029592 baseEnd_6029592 := by
    simpa [prefixWord, tailWord_6029592, baseEnd_6029592] using wordTrace_append hprefix tailTrace_6029592
  have hstable : (prefixWord ++ tailWord_6029592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6029592).length < 2 ^ (prefixWord ++ tailWord_6029592).sum := by decide
  have hdescent : baseEnd_6029592 < baseStart_6029592 := by decide
  rcases family_descends (prefixWord ++ tailWord_6029592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6029602 : List Nat := [3, 3, 1, 1, 3, 1, 1, 1, 2, 1, 6]
def baseStart_6029602 : Nat := 118140960795 + 6029602 * 2 ^ 59
def prefixEnd_6029602 : Nat := 4983230072969 + 3 ^ 40 * 6029602 * 2
def baseEnd_6029602 : Nat := 3096083981311023388145371

theorem tailTrace_6029602 : CollatzResearch.WordTrace tailWord_6029602 prefixEnd_6029602 3096083981311023388145371 := by
  unfold tailWord_6029602
  simp only [CollatzResearch.WordTrace]
  refine ⟨54979412975447300720552765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146611767934526135254807373 54979412975447300720552765)
  ·
    refine ⟨20617279865792737770207287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54979412975447300720552765 20617279865792737770207287)
    ·
      refine ⟨30925919798689106655310931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20617279865792737770207287 30925919798689106655310931)
      ·
        refine ⟨46388879698033659982966397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30925919798689106655310931 46388879698033659982966397)
        ·
          refine ⟨17395829886762622493612399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46388879698033659982966397 17395829886762622493612399)
          ·
            refine ⟨26093744830143933740418599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17395829886762622493612399 26093744830143933740418599)
            ·
              refine ⟨39140617245215900610627899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26093744830143933740418599 39140617245215900610627899)
              ·
                refine ⟨58710925867823850915941849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39140617245215900610627899 58710925867823850915941849)
                ·
                  refine ⟨44033194400867888186956387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58710925867823850915941849 44033194400867888186956387)
                  ·
                    refine ⟨66049791601301832280434581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 44033194400867888186956387 66049791601301832280434581)
                    ·
                      refine ⟨3096083981311023388145371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 66049791601301832280434581 3096083981311023388145371)
                      ·
                        rfl

theorem cell23_6029602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 1, 2, 1, 6].length) (baseStart_6029602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6029602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6029602 prefixEnd_6029602 := by exact prefixLift 6029602
  have htrace : WordTrace (prefixWord ++ tailWord_6029602) baseStart_6029602 baseEnd_6029602 := by
    simpa [prefixWord, tailWord_6029602, baseEnd_6029602] using wordTrace_append hprefix tailTrace_6029602
  have hstable : (prefixWord ++ tailWord_6029602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6029602).length < 2 ^ (prefixWord ++ tailWord_6029602).sum := by decide
  have hdescent : baseEnd_6029602 < baseStart_6029602 := by decide
  rcases family_descends (prefixWord ++ tailWord_6029602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6029612 : List Nat := [2, 2, 1, 1, 1, 3, 5, 2, 6]
def baseStart_6029612 : Nat := 118140960795 + 6029612 * 2 ^ 59
def prefixEnd_6029612 : Nat := 4983230072969 + 3 ^ 40 * 6029612 * 2
def baseEnd_6029612 : Nat := 344009901790840927668925

theorem tailTrace_6029612 : CollatzResearch.WordTrace tailWord_6029612 prefixEnd_6029612 344009901790840927668925 := by
  unfold tailWord_6029612
  simp only [CollatzResearch.WordTrace]
  refine ⟨109959008315876487295037545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146612011087835316393383393 109959008315876487295037545)
  ·
    refine ⟨82469256236907365471278159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109959008315876487295037545 82469256236907365471278159)
    ·
      refine ⟨123703884355361048206917239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82469256236907365471278159 123703884355361048206917239)
      ·
        refine ⟨185555826533041572310375859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123703884355361048206917239 185555826533041572310375859)
        ·
          refine ⟨278333739799562358465563789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185555826533041572310375859 278333739799562358465563789)
          ·
            refine ⟨104375152424835884424586421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 278333739799562358465563789 104375152424835884424586421)
            ·
              refine ⟨9785170539828364164804977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 104375152424835884424586421 9785170539828364164804977)
              ·
                refine ⟨7338877904871273123603733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9785170539828364164804977 7338877904871273123603733)
                ·
                  refine ⟨344009901790840927668925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7338877904871273123603733 344009901790840927668925)
                  ·
                    rfl

theorem cell23_6029612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 6].length) (baseStart_6029612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6029612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6029612 prefixEnd_6029612 := by exact prefixLift 6029612
  have htrace : WordTrace (prefixWord ++ tailWord_6029612) baseStart_6029612 baseEnd_6029612 := by
    simpa [prefixWord, tailWord_6029612, baseEnd_6029612] using wordTrace_append hprefix tailTrace_6029612
  have hstable : (prefixWord ++ tailWord_6029612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6029612).length < 2 ^ (prefixWord ++ tailWord_6029612).sum := by decide
  have hdescent : baseEnd_6029612 < baseStart_6029612 := by decide
  rcases family_descends (prefixWord ++ tailWord_6029612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6029615 : List Nat := [1, 1, 2, 1, 2, 1, 5, 1, 1, 2, 6]
def baseStart_6029615 : Nat := 118140960795 + 6029615 * 2 ^ 59
def prefixEnd_6029615 : Nat := 4983230072969 + 3 ^ 40 * 6029615 * 2
def baseEnd_6029615 : Nat := 3096090656559531837282811

theorem tailTrace_6029615 : CollatzResearch.WordTrace tailWord_6029615 prefixEnd_6029615 3096090656559531837282811 := by
  unfold tailWord_6029615
  simp only [CollatzResearch.WordTrace]
  refine ⟨219918126050742106102434299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146612084033828070734956199 219918126050742106102434299)
  ·
    refine ⟨329877189076113159153651449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219918126050742106102434299 329877189076113159153651449)
    ·
      refine ⟨247407891807084869365238587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 329877189076113159153651449 247407891807084869365238587)
      ·
        refine ⟨371111837710627304047857881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 247407891807084869365238587 371111837710627304047857881)
        ·
          refine ⟨278333878282970478035893411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 371111837710627304047857881 278333878282970478035893411)
          ·
            refine ⟨417500817424455717053840117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 278333878282970478035893411 417500817424455717053840117)
            ·
              refine ⟨39140701633542723473797511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 417500817424455717053840117 39140701633542723473797511)
              ·
                refine ⟨58711052450314085210696267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39140701633542723473797511 58711052450314085210696267)
                ·
                  refine ⟨88066578675471127816044401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58711052450314085210696267 88066578675471127816044401)
                  ·
                    refine ⟨66049934006603345862033301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 88066578675471127816044401 66049934006603345862033301)
                    ·
                      refine ⟨3096090656559531837282811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 66049934006603345862033301 3096090656559531837282811)
                      ·
                        rfl

theorem cell23_6029615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 1, 1, 2, 6].length) (baseStart_6029615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6029615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6029615 prefixEnd_6029615 := by exact prefixLift 6029615
  have htrace : WordTrace (prefixWord ++ tailWord_6029615) baseStart_6029615 baseEnd_6029615 := by
    simpa [prefixWord, tailWord_6029615, baseEnd_6029615] using wordTrace_append hprefix tailTrace_6029615
  have hstable : (prefixWord ++ tailWord_6029615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6029615).length < 2 ^ (prefixWord ++ tailWord_6029615).sum := by decide
  have hdescent : baseEnd_6029615 < baseStart_6029615 := by decide
  rcases family_descends (prefixWord ++ tailWord_6029615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6029635 : List Nat := [1, 1, 1, 3, 1, 3, 2, 1, 2, 1, 7]
def baseStart_6029635 : Nat := 118140960795 + 6029635 * 2 ^ 59
def prefixEnd_6029635 : Nat := 4983230072969 + 3 ^ 40 * 6029635 * 2
def baseEnd_6029635 : Nat := 3096100926172621759032719

theorem tailTrace_6029635 : CollatzResearch.WordTrace tailWord_6029635 prefixEnd_6029635 3096100926172621759032719 := by
  unfold tailWord_6029635
  simp only [CollatzResearch.WordTrace]
  refine ⟨219918855510669649518162359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146612570340446433012108239 219918855510669649518162359)
  ·
    refine ⟨329878283266004474277243539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219918855510669649518162359 329878283266004474277243539)
    ·
      refine ⟨494817424899006711415865309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 329878283266004474277243539 494817424899006711415865309)
      ·
        refine ⟨185556534337127516780949491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 494817424899006711415865309 185556534337127516780949491)
        ·
          refine ⟨278334801505691275171424237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185556534337127516780949491 278334801505691275171424237)
          ·
            refine ⟨104375550564634228189284089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 278334801505691275171424237 104375550564634228189284089)
            ·
              refine ⟨78281662923475671141963067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104375550564634228189284089 78281662923475671141963067)
              ·
                refine ⟨117422494385213506712944601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78281662923475671141963067 117422494385213506712944601)
                ·
                  refine ⟨88066870788910130034708451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 117422494385213506712944601 88066870788910130034708451)
                  ·
                    refine ⟨132100306183365195052062677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 88066870788910130034708451 132100306183365195052062677)
                    ·
                      refine ⟨3096100926172621759032719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 132100306183365195052062677 3096100926172621759032719)
                      ·
                        rfl

theorem cell23_6029635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 1, 2, 1, 7].length) (baseStart_6029635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6029635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6029635 prefixEnd_6029635 := by exact prefixLift 6029635
  have htrace : WordTrace (prefixWord ++ tailWord_6029635) baseStart_6029635 baseEnd_6029635 := by
    simpa [prefixWord, tailWord_6029635, baseEnd_6029635] using wordTrace_append hprefix tailTrace_6029635
  have hstable : (prefixWord ++ tailWord_6029635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6029635).length < 2 ^ (prefixWord ++ tailWord_6029635).sum := by decide
  have hdescent : baseEnd_6029635 < baseStart_6029635 := by decide
  rcases family_descends (prefixWord ++ tailWord_6029635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6029639 : List Nat := [1, 1, 4, 1, 2, 2, 1, 4, 3, 1, 3]
def baseStart_6029639 : Nat := 118140960795 + 6029639 * 2 ^ 59
def prefixEnd_6029639 : Nat := 4983230072969 + 3 ^ 40 * 6029639 * 2
def baseEnd_6029639 : Nat := 3096102980095239743382701

theorem tailTrace_6029639 : CollatzResearch.WordTrace tailWord_6029639 prefixEnd_6029639 3096102980095239743382701 := by
  unfold tailWord_6029639
  simp only [CollatzResearch.WordTrace]
  refine ⟨219919001402655158201307971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146612667601770105467538647 219919001402655158201307971)
  ·
    refine ⟨329878502103982737301961957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219919001402655158201307971 329878502103982737301961957)
    ·
      refine ⟨61852219144496763244117867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 329878502103982737301961957 61852219144496763244117867)
      ·
        refine ⟨92778328716745144866176801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61852219144496763244117867 92778328716745144866176801)
        ·
          refine ⟨69583746537558858649632601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92778328716745144866176801 69583746537558858649632601)
          ·
            refine ⟨52187809903169143987224451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69583746537558858649632601 52187809903169143987224451)
            ·
              refine ⟨78281714854753715980836677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52187809903169143987224451 78281714854753715980836677)
              ·
                refine ⟨14677821535266321746406877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 78281714854753715980836677 14677821535266321746406877)
                ·
                  refine ⟨5504183075724870654902579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14677821535266321746406877 5504183075724870654902579)
                  ·
                    refine ⟨8256274613587305982353869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5504183075724870654902579 8256274613587305982353869)
                    ·
                      refine ⟨3096102980095239743382701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8256274613587305982353869 3096102980095239743382701)
                      ·
                        rfl

theorem cell23_6029639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 4, 3, 1, 3].length) (baseStart_6029639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6029639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6029639 prefixEnd_6029639 := by exact prefixLift 6029639
  have htrace : WordTrace (prefixWord ++ tailWord_6029639) baseStart_6029639 baseEnd_6029639 := by
    simpa [prefixWord, tailWord_6029639, baseEnd_6029639] using wordTrace_append hprefix tailTrace_6029639
  have hstable : (prefixWord ++ tailWord_6029639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6029639).length < 2 ^ (prefixWord ++ tailWord_6029639).sum := by decide
  have hdescent : baseEnd_6029639 < baseStart_6029639 := by decide
  rcases family_descends (prefixWord ++ tailWord_6029639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6029649 : List Nat := [1, 2, 2, 1, 4, 2, 2, 1, 1, 5, 2]
def baseStart_6029649 : Nat := 118140960795 + 6029649 * 2 ^ 59
def prefixEnd_6029649 : Nat := 4983230072969 + 3 ^ 40 * 6029649 * 2
def baseEnd_6029649 : Nat := 3096108114901784704257655

theorem tailTrace_6029649 : CollatzResearch.WordTrace tailWord_6029649 prefixEnd_6029649 3096108114901784704257655 := by
  unfold tailWord_6029649
  simp only [CollatzResearch.WordTrace]
  refine ⟨219919366132618929909172001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146612910755079286606114667 219919366132618929909172001)
  ·
    refine ⟨164939524599464197431879001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219919366132618929909172001 164939524599464197431879001)
    ·
      refine ⟨123704643449598148073909251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164939524599464197431879001 123704643449598148073909251)
      ·
        refine ⟨185556965174397222110863877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123704643449598148073909251 185556965174397222110863877)
        ·
          refine ⟨34791930970199479145786977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 185556965174397222110863877 34791930970199479145786977)
          ·
            refine ⟨26093948227649609359340233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34791930970199479145786977 26093948227649609359340233)
            ·
              refine ⟨19570461170737207019505175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26093948227649609359340233 19570461170737207019505175)
              ·
                refine ⟨29355691756105810529257763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19570461170737207019505175 29355691756105810529257763)
                ·
                  refine ⟨44033537634158715793886645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29355691756105810529257763 44033537634158715793886645)
                  ·
                    refine ⟨4128144153202379605676873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 44033537634158715793886645 4128144153202379605676873)
                    ·
                      refine ⟨3096108114901784704257655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4128144153202379605676873 3096108114901784704257655)
                      ·
                        rfl

theorem cell23_6029649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 2, 1, 1, 5, 2].length) (baseStart_6029649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6029649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6029649 prefixEnd_6029649 := by exact prefixLift 6029649
  have htrace : WordTrace (prefixWord ++ tailWord_6029649) baseStart_6029649 baseEnd_6029649 := by
    simpa [prefixWord, tailWord_6029649, baseEnd_6029649] using wordTrace_append hprefix tailTrace_6029649
  have hstable : (prefixWord ++ tailWord_6029649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6029649).length < 2 ^ (prefixWord ++ tailWord_6029649).sum := by decide
  have hdescent : baseEnd_6029649 < baseStart_6029649 := by decide
  rcases family_descends (prefixWord ++ tailWord_6029649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6029656 : List Nat := [2, 1, 2, 2, 1, 1, 2, 7, 1, 1, 3]
def baseStart_6029656 : Nat := 118140960795 + 6029656 * 2 ^ 59
def prefixEnd_6029656 : Nat := 4983230072969 + 3 ^ 40 * 6029656 * 2
def baseEnd_6029656 : Nat := 3096111709266366176870123

theorem tailTrace_6029656 : CollatzResearch.WordTrace tailWord_6029656 prefixEnd_6029656 3096111709266366176870123 := by
  unfold tailWord_6029656
  simp only [CollatzResearch.WordTrace]
  refine ⟨109959810721796785052338411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146613080962395713403117881 109959810721796785052338411)
  ·
    refine ⟨164939716082695177578507617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109959810721796785052338411 164939716082695177578507617)
    ·
      refine ⟨123704787062021383183880713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164939716082695177578507617 123704787062021383183880713)
      ·
        refine ⟨92778590296516037387910535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123704787062021383183880713 92778590296516037387910535)
        ·
          refine ⟨139167885444774056081865803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92778590296516037387910535 139167885444774056081865803)
          ·
            refine ⟨208751828167161084122798705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139167885444774056081865803 208751828167161084122798705)
            ·
              refine ⟨156563871125370813092099029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 208751828167161084122798705 156563871125370813092099029)
              ·
                refine ⟨3669465729500878431846071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 156563871125370813092099029 3669465729500878431846071)
                ·
                  refine ⟨5504198594251317647769107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3669465729500878431846071 5504198594251317647769107)
                  ·
                    refine ⟨8256297891376976471653661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5504198594251317647769107 8256297891376976471653661)
                    ·
                      refine ⟨3096111709266366176870123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8256297891376976471653661 3096111709266366176870123)
                      ·
                        rfl

theorem cell23_6029656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 7, 1, 1, 3].length) (baseStart_6029656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6029656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6029656 prefixEnd_6029656 := by exact prefixLift 6029656
  have htrace : WordTrace (prefixWord ++ tailWord_6029656) baseStart_6029656 baseEnd_6029656 := by
    simpa [prefixWord, tailWord_6029656, baseEnd_6029656] using wordTrace_append hprefix tailTrace_6029656
  have hstable : (prefixWord ++ tailWord_6029656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6029656).length < 2 ^ (prefixWord ++ tailWord_6029656).sum := by decide
  have hdescent : baseEnd_6029656 < baseStart_6029656 := by decide
  rcases family_descends (prefixWord ++ tailWord_6029656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6029666 : List Nat := [3, 3, 2, 1, 1, 2, 1, 1, 4, 3, 2]
def baseStart_6029666 : Nat := 118140960795 + 6029666 * 2 ^ 59
def prefixEnd_6029666 : Nat := 4983230072969 + 3 ^ 40 * 6029666 * 2
def baseEnd_6029666 : Nat := 3096116844072911137745077

theorem tailTrace_6029666 : CollatzResearch.WordTrace tailWord_6029666 prefixEnd_6029666 3096116844072911137745077 := by
  unfold tailWord_6029666
  simp only [CollatzResearch.WordTrace]
  refine ⟨54979996543389335453135213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146613324115704894541693901 54979996543389335453135213)
  ·
    refine ⟨20617498703771000794925705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54979996543389335453135213 20617498703771000794925705)
    ·
      refine ⟨15463124027828250596194279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20617498703771000794925705 15463124027828250596194279)
      ·
        refine ⟨23194686041742375894291419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15463124027828250596194279 23194686041742375894291419)
        ·
          refine ⟨34792029062613563841437129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23194686041742375894291419 34792029062613563841437129)
          ·
            refine ⟨26094021796960172881077847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34792029062613563841437129 26094021796960172881077847)
            ·
              refine ⟨39141032695440259321616771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26094021796960172881077847 39141032695440259321616771)
              ·
                refine ⟨58711549043160388982425157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39141032695440259321616771 58711549043160388982425157)
                ·
                  refine ⟨11008415445592572934204717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 58711549043160388982425157 11008415445592572934204717)
                  ·
                    refine ⟨4128155792097214850326769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11008415445592572934204717 4128155792097214850326769)
                    ·
                      refine ⟨3096116844072911137745077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4128155792097214850326769 3096116844072911137745077)
                      ·
                        rfl

theorem cell23_6029666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 1, 4, 3, 2].length) (baseStart_6029666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6029666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6029666 prefixEnd_6029666 := by exact prefixLift 6029666
  have htrace : WordTrace (prefixWord ++ tailWord_6029666) baseStart_6029666 baseEnd_6029666 := by
    simpa [prefixWord, tailWord_6029666, baseEnd_6029666] using wordTrace_append hprefix tailTrace_6029666
  have hstable : (prefixWord ++ tailWord_6029666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6029666).length < 2 ^ (prefixWord ++ tailWord_6029666).sum := by decide
  have hdescent : baseEnd_6029666 < baseStart_6029666 := by decide
  rcases family_descends (prefixWord ++ tailWord_6029666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6029673 : List Nat := [1, 2, 1, 1, 1, 3, 7, 2, 1, 1, 3]
def baseStart_6029673 : Nat := 118140960795 + 6029673 * 2 ^ 59
def prefixEnd_6029673 : Nat := 4983230072969 + 3 ^ 40 * 6029673 * 2
def baseEnd_6029673 : Nat := 3096120438437492610357545

theorem tailTrace_6029673 : CollatzResearch.WordTrace tailWord_6029673 prefixEnd_6029673 3096120438437492610357545 := by
  unfold tailWord_6029673
  simp only [CollatzResearch.WordTrace]
  refine ⟨219920241484531982008045673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146613494323021321338697115 219920241484531982008045673)
  ·
    refine ⟨164940181113398986506034255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219920241484531982008045673 164940181113398986506034255)
    ·
      refine ⟨247410271670098479759051383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164940181113398986506034255 247410271670098479759051383)
      ·
        refine ⟨371115407505147719638577075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 247410271670098479759051383 371115407505147719638577075)
        ·
          refine ⟨556673111257721579457865613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 371115407505147719638577075 556673111257721579457865613)
          ·
            refine ⟨208752416721645592296699605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 556673111257721579457865613 208752416721645592296699605)
            ·
              refine ⟨4892634766913568569453897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 208752416721645592296699605 4892634766913568569453897)
              ·
                refine ⟨3669476075185176427090423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4892634766913568569453897 3669476075185176427090423)
                ·
                  refine ⟨5504214112777764640635635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3669476075185176427090423 5504214112777764640635635)
                  ·
                    refine ⟨8256321169166646960953453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5504214112777764640635635 8256321169166646960953453)
                    ·
                      refine ⟨3096120438437492610357545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8256321169166646960953453 3096120438437492610357545)
                      ·
                        rfl

theorem cell23_6029673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 7, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 7, 2, 1, 1, 3].length) (baseStart_6029673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6029673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6029673 prefixEnd_6029673 := by exact prefixLift 6029673
  have htrace : WordTrace (prefixWord ++ tailWord_6029673) baseStart_6029673 baseEnd_6029673 := by
    simpa [prefixWord, tailWord_6029673, baseEnd_6029673] using wordTrace_append hprefix tailTrace_6029673
  have hstable : (prefixWord ++ tailWord_6029673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6029673).length < 2 ^ (prefixWord ++ tailWord_6029673).sum := by decide
  have hdescent : baseEnd_6029673 < baseStart_6029673 := by decide
  rcases family_descends (prefixWord ++ tailWord_6029673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6029706 : List Nat := [3, 1, 2, 5, 1, 1, 1, 2, 1, 6]
def baseStart_6029706 : Nat := 118140960795 + 6029706 * 2 ^ 59
def prefixEnd_6029706 : Nat := 4983230072969 + 3 ^ 40 * 6029706 * 2
def baseEnd_6029706 : Nat := 1032045794433030327081631

theorem tailTrace_6029706 : CollatzResearch.WordTrace tailWord_6029706 prefixEnd_6029706 1032045794433030327081631 := by
  unfold tailWord_6029706
  simp only [CollatzResearch.WordTrace]
  refine ⟨54980361273353107160999243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146614296728941619095997981 54980361273353107160999243)
  ·
    refine ⟨82470541910029660741498865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54980361273353107160999243 82470541910029660741498865)
    ·
      refine ⟨61852906432522245556124149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82470541910029660741498865 61852906432522245556124149)
      ·
        refine ⟨5798709978048960520886639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 61852906432522245556124149 5798709978048960520886639)
        ·
          refine ⟨8698064967073440781329959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5798709978048960520886639 8698064967073440781329959)
          ·
            refine ⟨13047097450610161171994939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8698064967073440781329959 13047097450610161171994939)
            ·
              refine ⟨19570646175915241757992409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13047097450610161171994939 19570646175915241757992409)
              ·
                refine ⟨14677984631936431318494307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19570646175915241757992409 14677984631936431318494307)
                ·
                  refine ⟨22016976947904646977741461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14677984631936431318494307 22016976947904646977741461)
                  ·
                    refine ⟨1032045794433030327081631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22016976947904646977741461 1032045794433030327081631)
                    ·
                      rfl

theorem cell23_6029706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 1, 2, 1, 6].length) (baseStart_6029706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6029706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6029706 prefixEnd_6029706 := by exact prefixLift 6029706
  have htrace : WordTrace (prefixWord ++ tailWord_6029706) baseStart_6029706 baseEnd_6029706 := by
    simpa [prefixWord, tailWord_6029706, baseEnd_6029706] using wordTrace_append hprefix tailTrace_6029706
  have hstable : (prefixWord ++ tailWord_6029706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6029706).length < 2 ^ (prefixWord ++ tailWord_6029706).sum := by decide
  have hdescent : baseEnd_6029706 < baseStart_6029706 := by decide
  rcases family_descends (prefixWord ++ tailWord_6029706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6029730 : List Nat := [3, 3, 1, 2, 1, 1, 3, 4, 1, 2, 2]
def baseStart_6029730 : Nat := 118140960795 + 6029730 * 2 ^ 59
def prefixEnd_6029730 : Nat := 4983230072969 + 3 ^ 40 * 6029730 * 2
def baseEnd_6029730 : Nat := 3096149706834798887344783

theorem tailTrace_6029730 : CollatzResearch.WordTrace tailWord_6029730 prefixEnd_6029730 3096149706834798887344783 := by
  unfold tailWord_6029730
  simp only [CollatzResearch.WordTrace]
  refine ⟨54980580111331370185717661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146614880296883653828580429 54980580111331370185717661)
  ·
    refine ⟨20617717541749263819644123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54980580111331370185717661 20617717541749263819644123)
    ·
      refine ⟨30926576312623895729466185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20617717541749263819644123 30926576312623895729466185)
      ·
        refine ⟨23194932234467921797099639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30926576312623895729466185 23194932234467921797099639)
        ·
          refine ⟨34792398351701882695649459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23194932234467921797099639 34792398351701882695649459)
          ·
            refine ⟨52188597527552824043474189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34792398351701882695649459 52188597527552824043474189)
            ·
              refine ⟨19570724072832309016302821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52188597527552824043474189 19570724072832309016302821)
              ·
                refine ⟨3669510763656057940556779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19570724072832309016302821 3669510763656057940556779)
                ·
                  refine ⟨5504266145484086910835169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3669510763656057940556779 5504266145484086910835169)
                  ·
                    refine ⟨4128199609113065183126377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5504266145484086910835169 4128199609113065183126377)
                    ·
                      refine ⟨3096149706834798887344783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4128199609113065183126377 3096149706834798887344783)
                      ·
                        rfl

theorem cell23_6029730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 3, 4, 1, 2, 2].length) (baseStart_6029730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6029730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6029730 prefixEnd_6029730 := by exact prefixLift 6029730
  have htrace : WordTrace (prefixWord ++ tailWord_6029730) baseStart_6029730 baseEnd_6029730 := by
    simpa [prefixWord, tailWord_6029730, baseEnd_6029730] using wordTrace_append hprefix tailTrace_6029730
  have hstable : (prefixWord ++ tailWord_6029730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6029730).length < 2 ^ (prefixWord ++ tailWord_6029730).sum := by decide
  have hdescent : baseEnd_6029730 < baseStart_6029730 := by decide
  rcases family_descends (prefixWord ++ tailWord_6029730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6029732 : List Nat := [2, 3, 1, 2, 1, 1, 3, 1, 2, 7]
def baseStart_6029732 : Nat := 118140960795 + 6029732 * 2 ^ 59
def prefixEnd_6029732 : Nat := 4983230072969 + 3 ^ 40 * 6029732 * 2
def baseEnd_6029732 : Nat := 1032050244598702626506591

theorem tailTrace_6029732 : CollatzResearch.WordTrace tailWord_6029732 prefixEnd_6029732 1032050244598702626506591 := by
  unfold tailWord_6029732
  simp only [CollatzResearch.WordTrace]
  refine ⟨109961196695659117542221725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146614928927545490056295633 109961196695659117542221725)
  ·
    refine ⟨41235448760872169078333147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109961196695659117542221725 41235448760872169078333147)
    ·
      refine ⟨61853173141308253617499721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41235448760872169078333147 61853173141308253617499721)
      ·
        refine ⟨46389879855981190213124791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61853173141308253617499721 46389879855981190213124791)
        ·
          refine ⟨69584819783971785319687187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46389879855981190213124791 69584819783971785319687187)
          ·
            refine ⟨104377229675957677979530781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69584819783971785319687187 104377229675957677979530781)
            ·
              refine ⟨39141461128484129242324043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 104377229675957677979530781 39141461128484129242324043)
              ·
                refine ⟨58712191692726193863486065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39141461128484129242324043 58712191692726193863486065)
                ·
                  refine ⟨44034143769544645397614549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58712191692726193863486065 44034143769544645397614549)
                  ·
                    refine ⟨1032050244598702626506591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44034143769544645397614549 1032050244598702626506591)
                    ·
                      rfl

theorem cell23_6029732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 1, 2, 7].length) (baseStart_6029732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6029732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6029732 prefixEnd_6029732 := by exact prefixLift 6029732
  have htrace : WordTrace (prefixWord ++ tailWord_6029732) baseStart_6029732 baseEnd_6029732 := by
    simpa [prefixWord, tailWord_6029732, baseEnd_6029732] using wordTrace_append hprefix tailTrace_6029732
  have hstable : (prefixWord ++ tailWord_6029732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6029732).length < 2 ^ (prefixWord ++ tailWord_6029732).sum := by decide
  have hdescent : baseEnd_6029732 < baseStart_6029732 := by decide
  rcases family_descends (prefixWord ++ tailWord_6029732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6029736 : List Nat := [2, 1, 6, 1, 1, 3, 1, 8]
def baseStart_6029736 : Nat := 118140960795 + 6029736 * 2 ^ 59
def prefixEnd_6029736 : Nat := 4983230072969 + 3 ^ 40 * 6029736 * 2
def baseEnd_6029736 : Nat := 114672325471063920884065

theorem tailTrace_6029736 : CollatzResearch.WordTrace tailWord_6029736 prefixEnd_6029736 114672325471063920884065 := by
  unfold tailWord_6029736
  simp only [CollatzResearch.WordTrace]
  refine ⟨109961269641651871883794531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146615026188869162511726041 109961269641651871883794531)
  ·
    refine ⟨164941904462477807825691797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109961269641651871883794531 164941904462477807825691797)
    ·
      refine ⟨7731651771678647241829303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 164941904462477807825691797 7731651771678647241829303)
      ·
        refine ⟨11597477657517970862743955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7731651771678647241829303 11597477657517970862743955)
        ·
          refine ⟨17396216486276956294115933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11597477657517970862743955 17396216486276956294115933)
          ·
            refine ⟨6523581182353858610293475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17396216486276956294115933 6523581182353858610293475)
            ·
              refine ⟨9785371773530787915440213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6523581182353858610293475 9785371773530787915440213)
              ·
                refine ⟨114672325471063920884065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9785371773530787915440213 114672325471063920884065)
                ·
                  rfl

theorem cell23_6029736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 1, 8].length) (baseStart_6029736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6029736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6029736 prefixEnd_6029736 := by exact prefixLift 6029736
  have htrace : WordTrace (prefixWord ++ tailWord_6029736) baseStart_6029736 baseEnd_6029736 := by
    simpa [prefixWord, tailWord_6029736, baseEnd_6029736] using wordTrace_append hprefix tailTrace_6029736
  have hstable : (prefixWord ++ tailWord_6029736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6029736).length < 2 ^ (prefixWord ++ tailWord_6029736).sum := by decide
  have hdescent : baseEnd_6029736 < baseStart_6029736 := by decide
  rcases family_descends (prefixWord ++ tailWord_6029736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6029746 : List Nat := [3, 2, 1, 1, 1, 1, 3, 5, 2, 1, 3]
def baseStart_6029746 : Nat := 118140960795 + 6029746 * 2 ^ 59
def prefixEnd_6029746 : Nat := 4983230072969 + 3 ^ 40 * 6029746 * 2
def baseEnd_6029746 : Nat := 3096157922525270824744709

theorem tailTrace_6029746 : CollatzResearch.WordTrace tailWord_6029746 prefixEnd_6029746 3096157922525270824744709 := by
  unfold tailWord_6029746
  simp only [CollatzResearch.WordTrace]
  refine ⟨54980726003316878868863273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146615269342178343650302061 54980726003316878868863273)
  ·
    refine ⟨41235544502487659151647455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54980726003316878868863273 41235544502487659151647455)
    ·
      refine ⟨61853316753731488727471183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41235544502487659151647455 61853316753731488727471183)
      ·
        refine ⟨92779975130597233091206775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61853316753731488727471183 92779975130597233091206775)
        ·
          refine ⟨139169962695895849636810163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92779975130597233091206775 139169962695895849636810163)
          ·
            refine ⟨208754944043843774455215245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139169962695895849636810163 208754944043843774455215245)
            ·
              refine ⟨78283104016441415420705717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 208754944043843774455215245 78283104016441415420705717)
              ·
                refine ⟨7339041001541382695691161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 78283104016441415420705717 7339041001541382695691161)
                ·
                  refine ⟨5504280751156037021768371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7339041001541382695691161 5504280751156037021768371)
                  ·
                    refine ⟨8256421126734055532652557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5504280751156037021768371 8256421126734055532652557)
                    ·
                      refine ⟨3096157922525270824744709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8256421126734055532652557 3096157922525270824744709)
                      ·
                        rfl

theorem cell23_6029746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 5, 2, 1, 3].length) (baseStart_6029746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6029746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6029746 prefixEnd_6029746 := by exact prefixLift 6029746
  have htrace : WordTrace (prefixWord ++ tailWord_6029746) baseStart_6029746 baseEnd_6029746 := by
    simpa [prefixWord, tailWord_6029746, baseEnd_6029746] using wordTrace_append hprefix tailTrace_6029746
  have hstable : (prefixWord ++ tailWord_6029746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6029746).length < 2 ^ (prefixWord ++ tailWord_6029746).sum := by decide
  have hdescent : baseEnd_6029746 < baseStart_6029746 := by decide
  rcases family_descends (prefixWord ++ tailWord_6029746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6029752 : List Nat := [2, 1, 2, 1, 2, 2, 1, 1, 4, 3, 4]
def baseStart_6029752 : Nat := 118140960795 + 6029752 * 2 ^ 59
def prefixEnd_6029752 : Nat := 4983230072969 + 3 ^ 40 * 6029752 * 2
def baseEnd_6029752 : Nat := 3096161003409197801269681

theorem tailTrace_6029752 : CollatzResearch.WordTrace tailWord_6029752 prefixEnd_6029752 3096161003409197801269681 := by
  unfold tailWord_6029752
  simp only [CollatzResearch.WordTrace]
  refine ⟨109961561425622889250085755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146615415234163852333447673 109961561425622889250085755)
  ·
    refine ⟨164942342138434333875128633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109961561425622889250085755 164942342138434333875128633)
    ·
      refine ⟨123706756603825750406346475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164942342138434333875128633 123706756603825750406346475)
      ·
        refine ⟨185560134905738625609519713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123706756603825750406346475 185560134905738625609519713)
        ·
          refine ⟨139170101179303969207139785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 185560134905738625609519713 139170101179303969207139785)
          ·
            refine ⟨104377575884477976905354839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 139170101179303969207139785 104377575884477976905354839)
            ·
              refine ⟨156566363826716965358032259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104377575884477976905354839 156566363826716965358032259)
              ·
                refine ⟨234849545740075448037048389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 156566363826716965358032259 234849545740075448037048389)
                ·
                  refine ⟨44034289826264146506946573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 234849545740075448037048389 44034289826264146506946573)
                  ·
                    refine ⟨16512858684849054940104965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 44034289826264146506946573 16512858684849054940104965)
                    ·
                      refine ⟨3096161003409197801269681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16512858684849054940104965 3096161003409197801269681)
                      ·
                        rfl

theorem cell23_6029752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 4, 3, 4].length) (baseStart_6029752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6029752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6029752 prefixEnd_6029752 := by exact prefixLift 6029752
  have htrace : WordTrace (prefixWord ++ tailWord_6029752) baseStart_6029752 baseEnd_6029752 := by
    simpa [prefixWord, tailWord_6029752, baseEnd_6029752] using wordTrace_append hprefix tailTrace_6029752
  have hstable : (prefixWord ++ tailWord_6029752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6029752).length < 2 ^ (prefixWord ++ tailWord_6029752).sum := by decide
  have hdescent : baseEnd_6029752 < baseStart_6029752 := by decide
  rcases family_descends (prefixWord ++ tailWord_6029752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6029780 : List Nat := [2, 4, 1, 2, 2, 3, 1, 2, 2, 1, 3]
def baseStart_6029780 : Nat := 118140960795 + 6029780 * 2 ^ 59
def prefixEnd_6029780 : Nat := 4983230072969 + 3 ^ 40 * 6029780 * 2
def baseEnd_6029780 : Nat := 3096175380867523691719553

theorem tailTrace_6029780 : CollatzResearch.WordTrace tailWord_6029780 prefixEnd_6029780 3096175380867523691719553 := by
  unfold tailWord_6029780
  simp only [CollatzResearch.WordTrace]
  refine ⟨109962072047572169641095397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146616096063429559521460529 109962072047572169641095397)
  ·
    refine ⟨20617888508919781807705387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 109962072047572169641095397 20617888508919781807705387)
    ·
      refine ⟨30926832763379672711558081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20617888508919781807705387 30926832763379672711558081)
      ·
        refine ⟨23195124572534754533668561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30926832763379672711558081 23195124572534754533668561)
        ·
          refine ⟨17396343429401065900251421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23195124572534754533668561 17396343429401065900251421)
          ·
            refine ⟨6523628786025399712594283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17396343429401065900251421 6523628786025399712594283)
            ·
              refine ⟨9785443179038099568891425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6523628786025399712594283 9785443179038099568891425)
              ·
                refine ⟨7339082384278574676668569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9785443179038099568891425 7339082384278574676668569)
                ·
                  refine ⟨5504311788208931007501427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7339082384278574676668569 5504311788208931007501427)
                  ·
                    refine ⟨8256467682313396511252141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5504311788208931007501427 8256467682313396511252141)
                    ·
                      refine ⟨3096175380867523691719553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8256467682313396511252141 3096175380867523691719553)
                      ·
                        rfl

theorem cell23_6029780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 1, 2, 2, 1, 3].length) (baseStart_6029780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6029780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6029780 prefixEnd_6029780 := by exact prefixLift 6029780
  have htrace : WordTrace (prefixWord ++ tailWord_6029780) baseStart_6029780 baseEnd_6029780 := by
    simpa [prefixWord, tailWord_6029780, baseEnd_6029780] using wordTrace_append hprefix tailTrace_6029780
  have hstable : (prefixWord ++ tailWord_6029780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6029780).length < 2 ^ (prefixWord ++ tailWord_6029780).sum := by decide
  have hdescent : baseEnd_6029780 < baseStart_6029780 := by decide
  rcases family_descends (prefixWord ++ tailWord_6029780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6029799 : List Nat := [1, 1, 5, 2, 1, 1, 1, 3, 2, 2, 4]
def baseStart_6029799 : Nat := 118140960795 + 6029799 * 2 ^ 59
def prefixEnd_6029799 : Nat := 4983230072969 + 3 ^ 40 * 6029799 * 2
def baseEnd_6029799 : Nat := 3096185136999959117381965

theorem tailTrace_6029799 : CollatzResearch.WordTrace tailWord_6029799 prefixEnd_6029799 3096185136999959117381965 := by
  unfold tailWord_6029799
  simp only [CollatzResearch.WordTrace]
  refine ⟨219924837082075505527132451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146616558054717003684754967 219924837082075505527132451)
  ·
    refine ⟨329887255623113258290698677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219924837082075505527132451 329887255623113258290698677)
    ·
      refine ⟨30926930214666867964753001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 329887255623113258290698677 30926930214666867964753001)
      ·
        refine ⟨23195197661000150973564751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30926930214666867964753001 23195197661000150973564751)
        ·
          refine ⟨34792796491500226460347127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23195197661000150973564751 34792796491500226460347127)
          ·
            refine ⟨52189194737250339690520691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34792796491500226460347127 52189194737250339690520691)
            ·
              refine ⟨78283792105875509535781037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52189194737250339690520691 78283792105875509535781037)
              ·
                refine ⟨29356422039703316075917889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78283792105875509535781037 29356422039703316075917889)
                ·
                  refine ⟨22017316529777487056938417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29356422039703316075917889 22017316529777487056938417)
                  ·
                    refine ⟨16512987397333115292703813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22017316529777487056938417 16512987397333115292703813)
                    ·
                      refine ⟨3096185136999959117381965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16512987397333115292703813 3096185136999959117381965)
                      ·
                        rfl

theorem cell23_6029799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 3, 2, 2, 4].length) (baseStart_6029799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6029799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6029799 prefixEnd_6029799 := by exact prefixLift 6029799
  have htrace : WordTrace (prefixWord ++ tailWord_6029799) baseStart_6029799 baseEnd_6029799 := by
    simpa [prefixWord, tailWord_6029799, baseEnd_6029799] using wordTrace_append hprefix tailTrace_6029799
  have hstable : (prefixWord ++ tailWord_6029799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6029799).length < 2 ^ (prefixWord ++ tailWord_6029799).sum := by decide
  have hdescent : baseEnd_6029799 < baseStart_6029799 := by decide
  rcases family_descends (prefixWord ++ tailWord_6029799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6029837 : List Nat := [1, 7, 1, 1, 1, 1, 2, 1, 4, 2, 2]
def baseStart_6029837 : Nat := 118140960795 + 6029837 * 2 ^ 59
def prefixEnd_6029837 : Nat := 4983230072969 + 3 ^ 40 * 6029837 * 2
def baseEnd_6029837 : Nat := 3096204649264829968706791

theorem tailTrace_6029837 : CollatzResearch.WordTrace tailWord_6029837 prefixEnd_6029837 3096204649264829968706791 := by
  unfold tailWord_6029837
  simp only [CollatzResearch.WordTrace]
  refine ⟨219926223055937838017015765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146617482037291892011343843 219926223055937838017015765)
  ·
    refine ⟨5154520852873543078523807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 219926223055937838017015765 5154520852873543078523807)
    ·
      refine ⟨7731781279310314617785711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5154520852873543078523807 7731781279310314617785711)
      ·
        refine ⟨11597671918965471926678567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7731781279310314617785711 11597671918965471926678567)
        ·
          refine ⟨17396507878448207890017851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11597671918965471926678567 17396507878448207890017851)
          ·
            refine ⟨26094761817672311835026777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17396507878448207890017851 26094761817672311835026777)
            ·
              refine ⟨19571071363254233876270083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26094761817672311835026777 19571071363254233876270083)
              ·
                refine ⟨29356607044881350814405125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19571071363254233876270083 29356607044881350814405125)
                ·
                  refine ⟨5504363820915253277700961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29356607044881350814405125 5504363820915253277700961)
                  ·
                    refine ⟨4128272865686439958275721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5504363820915253277700961 4128272865686439958275721)
                    ·
                      refine ⟨3096204649264829968706791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4128272865686439958275721 3096204649264829968706791)
                      ·
                        rfl

theorem cell23_6029837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 2, 1, 4, 2, 2].length) (baseStart_6029837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6029837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6029837 prefixEnd_6029837 := by exact prefixLift 6029837
  have htrace : WordTrace (prefixWord ++ tailWord_6029837) baseStart_6029837 baseEnd_6029837 := by
    simpa [prefixWord, tailWord_6029837, baseEnd_6029837] using wordTrace_append hprefix tailTrace_6029837
  have hstable : (prefixWord ++ tailWord_6029837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6029837).length < 2 ^ (prefixWord ++ tailWord_6029837).sum := by decide
  have hdescent : baseEnd_6029837 < baseStart_6029837 := by decide
  rcases family_descends (prefixWord ++ tailWord_6029837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6029899 : List Nat := [1, 1, 1, 1, 3, 1, 5, 4, 6]
def baseStart_6029899 : Nat := 118140960795 + 6029899 * 2 ^ 59
def prefixEnd_6029899 : Nat := 4983230072969 + 3 ^ 40 * 6029899 * 2
def baseEnd_6029899 : Nat := 344026276118378747347945

theorem tailTrace_6029899 : CollatzResearch.WordTrace tailWord_6029899 prefixEnd_6029899 344026276118378747347945 := by
  unfold tailWord_6029899
  simp only [CollatzResearch.WordTrace]
  refine ⟨219928484381713222605772751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146618989587808815070515167 219928484381713222605772751)
  ·
    refine ⟨329892726572569833908659127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219928484381713222605772751 329892726572569833908659127)
    ·
      refine ⟨494839089858854750862988691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 329892726572569833908659127 494839089858854750862988691)
      ·
        refine ⟨742258634788282126294483037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 494839089858854750862988691 742258634788282126294483037)
        ·
          refine ⟨278346988045605797360431139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 742258634788282126294483037 278346988045605797360431139)
          ·
            refine ⟨417520482068408696040646709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 278346988045605797360431139 417520482068408696040646709)
            ·
              refine ⟨39142545193913315253810629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 417520482068408696040646709 39142545193913315253810629)
              ·
                refine ⟨7339227223858746610089493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39142545193913315253810629 7339227223858746610089493)
                ·
                  refine ⟨344026276118378747347945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7339227223858746610089493 344026276118378747347945)
                  ·
                    rfl

theorem cell23_6029899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 4, 6].length) (baseStart_6029899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6029899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6029899 prefixEnd_6029899 := by exact prefixLift 6029899
  have htrace : WordTrace (prefixWord ++ tailWord_6029899) baseStart_6029899 baseEnd_6029899 := by
    simpa [prefixWord, tailWord_6029899, baseEnd_6029899] using wordTrace_append hprefix tailTrace_6029899
  have hstable : (prefixWord ++ tailWord_6029899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6029899).length < 2 ^ (prefixWord ++ tailWord_6029899).sum := by decide
  have hdescent : baseEnd_6029899 < baseStart_6029899 := by decide
  rcases family_descends (prefixWord ++ tailWord_6029899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6029953 : List Nat := [1, 2, 4, 2, 1, 1, 2, 1, 4, 3, 2]
def baseStart_6029953 : Nat := 118140960795 + 6029953 * 2 ^ 59
def prefixEnd_6029953 : Nat := 4983230072969 + 3 ^ 40 * 6029953 * 2
def baseEnd_6029953 : Nat := 3096264213020751514856257

theorem tailTrace_6029953 : CollatzResearch.WordTrace tailWord_6029953 prefixEnd_6029953 3096264213020751514856257 := by
  unfold tailWord_6029953
  simp only [CollatzResearch.WordTrace]
  refine ⟨219930453923517589828238513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146620302615678393218825675 219930453923517589828238513)
  ·
    refine ⟨164947840442638192371178885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219930453923517589828238513 164947840442638192371178885)
    ·
      refine ⟨30927720082994661069596041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 164947840442638192371178885 30927720082994661069596041)
      ·
        refine ⟨23195790062245995802197031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30927720082994661069596041 23195790062245995802197031)
        ·
          refine ⟨34793685093368993703295547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23195790062245995802197031 34793685093368993703295547)
          ·
            refine ⟨52190527640053490554943321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34793685093368993703295547 52190527640053490554943321)
            ·
              refine ⟨39142895730040117916207491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52190527640053490554943321 39142895730040117916207491)
              ·
                refine ⟨58714343595060176874311237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39142895730040117916207491 58714343595060176874311237)
                ·
                  refine ⟨11008939424073783163933357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 58714343595060176874311237 11008939424073783163933357)
                  ·
                    refine ⟨4128352284027668686475009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11008939424073783163933357 4128352284027668686475009)
                    ·
                      refine ⟨3096264213020751514856257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4128352284027668686475009 3096264213020751514856257)
                      ·
                        rfl

theorem cell23_6029953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 1, 4, 3, 2].length) (baseStart_6029953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6029953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6029953 prefixEnd_6029953 := by exact prefixLift 6029953
  have htrace : WordTrace (prefixWord ++ tailWord_6029953) baseStart_6029953 baseEnd_6029953 := by
    simpa [prefixWord, tailWord_6029953, baseEnd_6029953] using wordTrace_append hprefix tailTrace_6029953
  have hstable : (prefixWord ++ tailWord_6029953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6029953).length < 2 ^ (prefixWord ++ tailWord_6029953).sum := by decide
  have hdescent : baseEnd_6029953 < baseStart_6029953 := by decide
  rcases family_descends (prefixWord ++ tailWord_6029953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6029954 : List Nat := [3, 4, 3, 1, 1, 1, 2, 1, 3, 4]
def baseStart_6029954 : Nat := 118140960795 + 6029954 * 2 ^ 59
def prefixEnd_6029954 : Nat := 4983230072969 + 3 ^ 40 * 6029954 * 2
def baseEnd_6029954 : Nat := 1032088242167135336981251

theorem tailTrace_6029954 : CollatzResearch.WordTrace tailWord_6029954 prefixEnd_6029954 1032088242167135336981251 := by
  unfold tailWord_6029954
  simp only [CollatzResearch.WordTrace]
  refine ⟨54982622599128491749756229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146620326931009311332683277 54982622599128491749756229)
  ·
    refine ⟨10309241737336592203079293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54982622599128491749756229 10309241737336592203079293)
    ·
      refine ⟨3865965651501222076154735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10309241737336592203079293 3865965651501222076154735)
      ·
        refine ⟨5798948477251833114232103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3865965651501222076154735 5798948477251833114232103)
        ·
          refine ⟨8698422715877749671348155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5798948477251833114232103 8698422715877749671348155)
          ·
            refine ⟨13047634073816624507022233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8698422715877749671348155 13047634073816624507022233)
            ·
              refine ⟨9785725555362468380266675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13047634073816624507022233 9785725555362468380266675)
              ·
                refine ⟨14678588333043702570400013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9785725555362468380266675 14678588333043702570400013)
                ·
                  refine ⟨5504470624891388463900005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14678588333043702570400013 5504470624891388463900005)
                  ·
                    refine ⟨1032088242167135336981251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5504470624891388463900005 1032088242167135336981251)
                    ·
                      rfl

theorem cell23_6029954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_6029954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6029954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6029954 prefixEnd_6029954 := by exact prefixLift 6029954
  have htrace : WordTrace (prefixWord ++ tailWord_6029954) baseStart_6029954 baseEnd_6029954 := by
    simpa [prefixWord, tailWord_6029954, baseEnd_6029954] using wordTrace_append hprefix tailTrace_6029954
  have hstable : (prefixWord ++ tailWord_6029954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6029954).length < 2 ^ (prefixWord ++ tailWord_6029954).sum := by decide
  have hdescent : baseEnd_6029954 < baseStart_6029954 := by decide
  rcases family_descends (prefixWord ++ tailWord_6029954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6030003 : List Nat := [1, 1, 1, 2, 3, 4, 2, 3, 1, 2, 3]
def baseStart_6030003 : Nat := 118140960795 + 6030003 * 2 ^ 59
def prefixEnd_6030003 : Nat := 4983230072969 + 3 ^ 40 * 6030003 * 2
def baseEnd_6030003 : Nat := 3096289887053476319231027

theorem tailTrace_6030003 : CollatzResearch.WordTrace tailWord_6030003 prefixEnd_6030003 3096289887053476319231027 := by
  unfold tailWord_6030003
  simp only [CollatzResearch.WordTrace]
  refine ⟨219932277573336448367558663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146621518382224298911705775 219932277573336448367558663)
  ·
    refine ⟨329898416360004672551337995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219932277573336448367558663 329898416360004672551337995)
    ·
      refine ⟨494847624540007008827006993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 329898416360004672551337995 494847624540007008827006993)
      ·
        refine ⟨371135718405005256620255245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 494847624540007008827006993 371135718405005256620255245)
        ·
          refine ⟨139175894401876971232595717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 371135718405005256620255245 139175894401876971232595717)
          ·
            refine ⟨26095480200351932106111697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 139175894401876971232595717 26095480200351932106111697)
            ·
              refine ⟨19571610150263949079583773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26095480200351932106111697 19571610150263949079583773)
              ·
                refine ⟨7339353806348980904843915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19571610150263949079583773 7339353806348980904843915)
                ·
                  refine ⟨11009030709523471357265873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7339353806348980904843915 11009030709523471357265873)
                  ·
                    refine ⟨8256773032142603517949405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11009030709523471357265873 8256773032142603517949405)
                    ·
                      refine ⟨3096289887053476319231027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8256773032142603517949405 3096289887053476319231027)
                      ·
                        rfl

theorem cell23_6030003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 2, 3, 1, 2, 3].length) (baseStart_6030003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6030003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6030003 prefixEnd_6030003 := by exact prefixLift 6030003
  have htrace : WordTrace (prefixWord ++ tailWord_6030003) baseStart_6030003 baseEnd_6030003 := by
    simpa [prefixWord, tailWord_6030003, baseEnd_6030003] using wordTrace_append hprefix tailTrace_6030003
  have hstable : (prefixWord ++ tailWord_6030003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6030003).length < 2 ^ (prefixWord ++ tailWord_6030003).sum := by decide
  have hdescent : baseEnd_6030003 < baseStart_6030003 := by decide
  rcases family_descends (prefixWord ++ tailWord_6030003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6030068 : List Nat := [2, 6, 1, 1, 2, 1, 1, 4, 1, 2, 2]
def baseStart_6030068 : Nat := 118140960795 + 6030068 * 2 ^ 59
def prefixEnd_6030068 : Nat := 4983230072969 + 3 ^ 40 * 6030068 * 2
def baseEnd_6030068 : Nat := 3096323263296018564918229

theorem tailTrace_6030068 : CollatzResearch.WordTrace tailWord_6030068 prefixEnd_6030068 3096323263296018564918229 := by
  unfold tailWord_6030068
  simp only [CollatzResearch.WordTrace]
  refine ⟨109967324159050482234337429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146623098878733976312449905 109967324159050482234337429)
  ·
    refine ⟨5154718319955491354734567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 109967324159050482234337429 5154718319955491354734567)
    ·
      refine ⟨7732077479933237032101851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5154718319955491354734567 7732077479933237032101851)
      ·
        refine ⟨11598116219899855548152777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7732077479933237032101851 11598116219899855548152777)
        ·
          refine ⟨8698587164924891661114583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11598116219899855548152777 8698587164924891661114583)
          ·
            refine ⟨13047880747387337491671875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8698587164924891661114583 13047880747387337491671875)
            ·
              refine ⟨19571821121081006237507813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13047880747387337491671875 19571821121081006237507813)
              ·
                refine ⟨3669716460202688669532715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19571821121081006237507813 3669716460202688669532715)
                ·
                  refine ⟨5504574690304033004299073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3669716460202688669532715 5504574690304033004299073)
                  ·
                    refine ⟨4128431017728024753224305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5504574690304033004299073 4128431017728024753224305)
                    ·
                      refine ⟨3096323263296018564918229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4128431017728024753224305 3096323263296018564918229)
                      ·
                        rfl

theorem cell23_6030068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 1, 4, 1, 2, 2].length) (baseStart_6030068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6030068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6030068 prefixEnd_6030068 := by exact prefixLift 6030068
  have htrace : WordTrace (prefixWord ++ tailWord_6030068) baseStart_6030068 baseEnd_6030068 := by
    simpa [prefixWord, tailWord_6030068, baseEnd_6030068] using wordTrace_append hprefix tailTrace_6030068
  have hstable : (prefixWord ++ tailWord_6030068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6030068).length < 2 ^ (prefixWord ++ tailWord_6030068).sum := by decide
  have hdescent : baseEnd_6030068 < baseStart_6030068 := by decide
  rcases family_descends (prefixWord ++ tailWord_6030068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6030090 : List Nat := [3, 1, 2, 2, 1, 2, 4, 1, 1, 4, 2]
def baseStart_6030090 : Nat := 118140960795 + 6030090 * 2 ^ 59
def prefixEnd_6030090 : Nat := 4983230072969 + 3 ^ 40 * 6030090 * 2
def baseEnd_6030090 : Nat := 3096334559870417478843127

theorem tailTrace_6030090 : CollatzResearch.WordTrace tailWord_6030090 prefixEnd_6030090 3096334559870417478843127 := by
  unfold tailWord_6030090
  simp only [CollatzResearch.WordTrace]
  refine ⟨54983862681005315556493931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146623633816014174817317149 54983862681005315556493931)
  ·
    refine ⟨82475794021507973334740897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54983862681005315556493931 82475794021507973334740897)
    ·
      refine ⟨61856845516130980001055673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82475794021507973334740897 61856845516130980001055673)
      ·
        refine ⟨46392634137098235000791755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61856845516130980001055673 46392634137098235000791755)
        ·
          refine ⟨69588951205647352501187633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46392634137098235000791755 69588951205647352501187633)
          ·
            refine ⟨52191713404235514375890725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69588951205647352501187633 52191713404235514375890725)
            ·
              refine ⟨9785946263294158945479511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52191713404235514375890725 9785946263294158945479511)
              ·
                refine ⟨14678919394941238418219267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9785946263294158945479511 14678919394941238418219267)
                ·
                  refine ⟨22018379092411857627328901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14678919394941238418219267 22018379092411857627328901)
                  ·
                    refine ⟨4128446079827223305124169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22018379092411857627328901 4128446079827223305124169)
                    ·
                      refine ⟨3096334559870417478843127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4128446079827223305124169 3096334559870417478843127)
                      ·
                        rfl

theorem cell23_6030090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 4, 1, 1, 4, 2].length) (baseStart_6030090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6030090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6030090 prefixEnd_6030090 := by exact prefixLift 6030090
  have htrace : WordTrace (prefixWord ++ tailWord_6030090) baseStart_6030090 baseEnd_6030090 := by
    simpa [prefixWord, tailWord_6030090, baseEnd_6030090] using wordTrace_append hprefix tailTrace_6030090
  have hstable : (prefixWord ++ tailWord_6030090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6030090).length < 2 ^ (prefixWord ++ tailWord_6030090).sum := by decide
  have hdescent : baseEnd_6030090 < baseStart_6030090 := by decide
  rcases family_descends (prefixWord ++ tailWord_6030090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6030136 : List Nat := [2, 1, 2, 1, 3, 2, 2, 1, 1, 1, 7]
def baseStart_6030136 : Nat := 118140960795 + 6030136 * 2 ^ 59
def prefixEnd_6030136 : Nat := 4983230072969 + 3 ^ 40 * 6030136 * 2
def baseEnd_6030136 : Nat := 3096358179980524298867915

theorem tailTrace_6030136 : CollatzResearch.WordTrace tailWord_6030136 prefixEnd_6030136 3096358179980524298867915 := by
  unfold tailWord_6030136
  simp only [CollatzResearch.WordTrace]
  refine ⟨109968564240927306041075131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146624752321236408054766841 109968564240927306041075131)
  ·
    refine ⟨164952846361390959061612697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109968564240927306041075131 164952846361390959061612697)
    ·
      refine ⟨123714634771043219296209523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164952846361390959061612697 123714634771043219296209523)
      ·
        refine ⟨185571952156564828944314285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123714634771043219296209523 185571952156564828944314285)
        ·
          refine ⟨69589482058711810854117857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 185571952156564828944314285 69589482058711810854117857)
          ·
            refine ⟨52192111544033858140588393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69589482058711810854117857 52192111544033858140588393)
            ·
              refine ⟨39144083658025393605441295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52192111544033858140588393 39144083658025393605441295)
              ·
                refine ⟨58716125487038090408161943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39144083658025393605441295 58716125487038090408161943)
                ·
                  refine ⟨88074188230557135612242915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58716125487038090408161943 88074188230557135612242915)
                  ·
                    refine ⟨132111282345835703418364373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 88074188230557135612242915 132111282345835703418364373)
                    ·
                      refine ⟨3096358179980524298867915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 132111282345835703418364373 3096358179980524298867915)
                      ·
                        rfl

theorem cell23_6030136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 1, 1, 1, 7].length) (baseStart_6030136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6030136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6030136 prefixEnd_6030136 := by exact prefixLift 6030136
  have htrace : WordTrace (prefixWord ++ tailWord_6030136) baseStart_6030136 baseEnd_6030136 := by
    simpa [prefixWord, tailWord_6030136, baseEnd_6030136] using wordTrace_append hprefix tailTrace_6030136
  have hstable : (prefixWord ++ tailWord_6030136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6030136).length < 2 ^ (prefixWord ++ tailWord_6030136).sum := by decide
  have hdescent : baseEnd_6030136 < baseStart_6030136 := by decide
  rcases family_descends (prefixWord ++ tailWord_6030136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6030141 : List Nat := [1, 4, 1, 4, 2, 1, 3, 1, 2, 2, 2]
def baseStart_6030141 : Nat := 118140960795 + 6030141 * 2 ^ 59
def prefixEnd_6030141 : Nat := 4983230072969 + 3 ^ 40 * 6030141 * 2
def baseEnd_6030141 : Nat := 3096360747383796779305393

theorem tailTrace_6030141 : CollatzResearch.WordTrace tailWord_6030141 prefixEnd_6030141 3096360747383796779305393 := by
  unfold tailWord_6030141
  simp only [CollatzResearch.WordTrace]
  refine ⟨219937310846836497936082277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146624873897890998624054851 219937310846836497936082277)
  ·
    refine ⟨41238245783781843363015427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 219937310846836497936082277 41238245783781843363015427)
    ·
      refine ⟨61857368675672765044523141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41238245783781843363015427 61857368675672765044523141)
      ·
        refine ⟨11598256626688643445848089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61857368675672765044523141 11598256626688643445848089)
        ·
          refine ⟨8698692470016482584386067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11598256626688643445848089 8698692470016482584386067)
          ·
            refine ⟨13048038705024723876579101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8698692470016482584386067 13048038705024723876579101)
            ·
              refine ⟨4893014514384271453717163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13048038705024723876579101 4893014514384271453717163)
              ·
                refine ⟨7339521771576407180575745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4893014514384271453717163 7339521771576407180575745)
                ·
                  refine ⟨5504641328682305385431809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7339521771576407180575745 5504641328682305385431809)
                  ·
                    refine ⟨4128480996511729039073857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5504641328682305385431809 4128480996511729039073857)
                    ·
                      refine ⟨3096360747383796779305393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4128480996511729039073857 3096360747383796779305393)
                      ·
                        rfl

theorem cell23_6030141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 3, 1, 2, 2, 2].length) (baseStart_6030141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6030141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6030141 prefixEnd_6030141 := by exact prefixLift 6030141
  have htrace : WordTrace (prefixWord ++ tailWord_6030141) baseStart_6030141 baseEnd_6030141 := by
    simpa [prefixWord, tailWord_6030141, baseEnd_6030141] using wordTrace_append hprefix tailTrace_6030141
  have hstable : (prefixWord ++ tailWord_6030141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6030141).length < 2 ^ (prefixWord ++ tailWord_6030141).sum := by decide
  have hdescent : baseEnd_6030141 < baseStart_6030141 := by decide
  rcases family_descends (prefixWord ++ tailWord_6030141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6030163 : List Nat := [1, 1, 1, 2, 1, 1, 3, 4, 1, 6, 2]
def baseStart_6030163 : Nat := 118140960795 + 6030163 * 2 ^ 59
def prefixEnd_6030163 : Nat := 4983230072969 + 3 ^ 40 * 6030163 * 2
def baseEnd_6030163 : Nat := 3096372043958195693230291

theorem tailTrace_6030163 : CollatzResearch.WordTrace tailWord_6030163 prefixEnd_6030163 3096372043958195693230291 := by
  unfold tailWord_6030163
  simp only [CollatzResearch.WordTrace]
  refine ⟨219938113252756795693383143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146625408835171197128922095 219938113252756795693383143)
  ·
    refine ⟨329907169879135193540074715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219938113252756795693383143 329907169879135193540074715)
    ·
      refine ⟨494860754818702790310112073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 329907169879135193540074715 494860754818702790310112073)
      ·
        refine ⟨371145566114027092732584055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 494860754818702790310112073 371145566114027092732584055)
        ·
          refine ⟨556718349171040639098876083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 371145566114027092732584055 556718349171040639098876083)
          ·
            refine ⟨835077523756560958648314125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 556718349171040639098876083 835077523756560958648314125)
            ·
              refine ⟨313154071408710359493117797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 835077523756560958648314125 313154071408710359493117797)
              ·
                refine ⟨58716388389133192404959587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 313154071408710359493117797 58716388389133192404959587)
                ·
                  refine ⟨88074582583699788607439381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58716388389133192404959587 88074582583699788607439381)
                  ·
                    refine ⟨4128496058610927590973721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 88074582583699788607439381 4128496058610927590973721)
                    ·
                      refine ⟨3096372043958195693230291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4128496058610927590973721 3096372043958195693230291)
                      ·
                        rfl

theorem cell23_6030163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 4, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 4, 1, 6, 2].length) (baseStart_6030163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6030163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6030163 prefixEnd_6030163 := by exact prefixLift 6030163
  have htrace : WordTrace (prefixWord ++ tailWord_6030163) baseStart_6030163 baseEnd_6030163 := by
    simpa [prefixWord, tailWord_6030163, baseEnd_6030163] using wordTrace_append hprefix tailTrace_6030163
  have hstable : (prefixWord ++ tailWord_6030163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6030163).length < 2 ^ (prefixWord ++ tailWord_6030163).sum := by decide
  have hdescent : baseEnd_6030163 < baseStart_6030163 := by decide
  rcases family_descends (prefixWord ++ tailWord_6030163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6030164 : List Nat := [2, 4, 1, 1, 5, 1, 1, 3, 5]
def baseStart_6030164 : Nat := 118140960795 + 6030164 * 2 ^ 59
def prefixEnd_6030164 : Nat := 4983230072969 + 3 ^ 40 * 6030164 * 2
def baseEnd_6030164 : Nat := 344041395270983354368643

theorem tailTrace_6030164 : CollatzResearch.WordTrace tailWord_6030164 prefixEnd_6030164 344041395270983354368643 := by
  unfold tailWord_6030164
  simp only [CollatzResearch.WordTrace]
  refine ⟨109969074862876586432084773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146625433150502115242779697 109969074862876586432084773)
  ·
    refine ⟨20619201536789359956015895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 109969074862876586432084773 20619201536789359956015895)
    ·
      refine ⟨30928802305184039934023843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20619201536789359956015895 30928802305184039934023843)
      ·
        refine ⟨46393203457776059901035765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30928802305184039934023843 46393203457776059901035765)
        ·
          refine ⟨4349362824166505615722103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 46393203457776059901035765 4349362824166505615722103)
          ·
            refine ⟨6524044236249758423583155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4349362824166505615722103 6524044236249758423583155)
            ·
              refine ⟨9786066354374637635374733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6524044236249758423583155 9786066354374637635374733)
              ·
                refine ⟨3669774882890489113265525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9786066354374637635374733 3669774882890489113265525)
                ·
                  refine ⟨344041395270983354368643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3669774882890489113265525 344041395270983354368643)
                  ·
                    rfl

theorem cell23_6030164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 1, 3, 5].length) (baseStart_6030164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6030164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6030164 prefixEnd_6030164 := by exact prefixLift 6030164
  have htrace : WordTrace (prefixWord ++ tailWord_6030164) baseStart_6030164 baseEnd_6030164 := by
    simpa [prefixWord, tailWord_6030164, baseEnd_6030164] using wordTrace_append hprefix tailTrace_6030164
  have hstable : (prefixWord ++ tailWord_6030164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6030164).length < 2 ^ (prefixWord ++ tailWord_6030164).sum := by decide
  have hdescent : baseEnd_6030164 < baseStart_6030164 := by decide
  rcases family_descends (prefixWord ++ tailWord_6030164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6030180 : List Nat := [2, 3, 1, 1, 4, 2, 1, 2, 2, 1, 4]
def baseStart_6030180 : Nat := 118140960795 + 6030180 * 2 ^ 59
def prefixEnd_6030180 : Nat := 4983230072969 + 3 ^ 40 * 6030180 * 2
def baseEnd_6030180 : Nat := 3096380773129322126717713

theorem tailTrace_6030180 : CollatzResearch.WordTrace tailWord_6030180 prefixEnd_6030180 3096380773129322126717713 := by
  unfold tailWord_6030180
  simp only [CollatzResearch.WordTrace]
  refine ⟨109969366646847603798375997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146625822195796805064501329 109969366646847603798375997)
  ·
    refine ⟨41238512492567851424390999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109969366646847603798375997 41238512492567851424390999)
    ·
      refine ⟨61857768738851777136586499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41238512492567851424390999 61857768738851777136586499)
      ·
        refine ⟨92786653108277665704879749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61857768738851777136586499 92786653108277665704879749)
        ·
          refine ⟨17397497457802062319664953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 92786653108277665704879749 17397497457802062319664953)
          ·
            refine ⟨13048123093351546739748715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17397497457802062319664953 13048123093351546739748715)
            ·
              refine ⟨19572184640027320109623073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13048123093351546739748715 19572184640027320109623073)
              ·
                refine ⟨14679138480020490082217305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19572184640027320109623073 14679138480020490082217305)
                ·
                  refine ⟨11009353860015367561662979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14679138480020490082217305 11009353860015367561662979)
                  ·
                    refine ⟨16514030790023051342494469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11009353860015367561662979 16514030790023051342494469)
                    ·
                      refine ⟨3096380773129322126717713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16514030790023051342494469 3096380773129322126717713)
                      ·
                        rfl

theorem cell23_6030180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 1, 2, 2, 1, 4].length) (baseStart_6030180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6030180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6030180 prefixEnd_6030180 := by exact prefixLift 6030180
  have htrace : WordTrace (prefixWord ++ tailWord_6030180) baseStart_6030180 baseEnd_6030180 := by
    simpa [prefixWord, tailWord_6030180, baseEnd_6030180] using wordTrace_append hprefix tailTrace_6030180
  have hstable : (prefixWord ++ tailWord_6030180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6030180).length < 2 ^ (prefixWord ++ tailWord_6030180).sum := by decide
  have hdescent : baseEnd_6030180 < baseStart_6030180 := by decide
  rcases family_descends (prefixWord ++ tailWord_6030180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6030241 : List Nat := [1, 2, 3, 4, 1, 3, 2, 2, 1, 4]
def baseStart_6030241 : Nat := 118140960795 + 6030241 * 2 ^ 59
def prefixEnd_6030241 : Nat := 4983230072969 + 3 ^ 40 * 6030241 * 2
def baseEnd_6030241 : Nat := 1032137365149748796018311

theorem tailTrace_6030241 : CollatzResearch.WordTrace tailWord_6030241 prefixEnd_6030241 1032137365149748796018311 := by
  unfold tailWord_6030241
  simp only [CollatzResearch.WordTrace]
  refine ⟨219940958146474215014722577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146627305430982810009815051 219940958146474215014722577)
  ·
    refine ⟨164955718609855661261041933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219940958146474215014722577 164955718609855661261041933)
    ·
      refine ⟨61858394478695872972890725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 164955718609855661261041933 61858394478695872972890725)
      ·
        refine ⟨11598448964755476182417011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61858394478695872972890725 11598448964755476182417011)
        ·
          refine ⟨17397673447133214273625517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11598448964755476182417011 17397673447133214273625517)
          ·
            refine ⟨6524127542674955352609569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17397673447133214273625517 6524127542674955352609569)
            ·
              refine ⟨4893095657006216514457177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6524127542674955352609569 4893095657006216514457177)
              ·
                refine ⟨3669821742754662385842883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4893095657006216514457177 3669821742754662385842883)
                ·
                  refine ⟨5504732614131993578764325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3669821742754662385842883 5504732614131993578764325)
                  ·
                    refine ⟨1032137365149748796018311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5504732614131993578764325 1032137365149748796018311)
                    ·
                      rfl

theorem cell23_6030241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 2, 2, 1, 4].length) (baseStart_6030241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6030241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6030241 prefixEnd_6030241 := by exact prefixLift 6030241
  have htrace : WordTrace (prefixWord ++ tailWord_6030241) baseStart_6030241 baseEnd_6030241 := by
    simpa [prefixWord, tailWord_6030241, baseEnd_6030241] using wordTrace_append hprefix tailTrace_6030241
  have hstable : (prefixWord ++ tailWord_6030241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6030241).length < 2 ^ (prefixWord ++ tailWord_6030241).sum := by decide
  have hdescent : baseEnd_6030241 < baseStart_6030241 := by decide
  rcases family_descends (prefixWord ++ tailWord_6030241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6030263 : List Nat := [1, 1, 3, 1, 3, 1, 3, 3, 1, 6]
def baseStart_6030263 : Nat := 118140960795 + 6030263 * 2 ^ 59
def prefixEnd_6030263 : Nat := 4983230072969 + 3 ^ 40 * 6030263 * 2
def baseEnd_6030263 : Nat := 1032141130674548433993277

theorem tailTrace_6030263 : CollatzResearch.WordTrace tailWord_6030263 prefixEnd_6030263 1032141130674548433993277 := by
  unfold tailWord_6030263
  simp only [CollatzResearch.WordTrace]
  refine ⟨219941760552394512772023443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146627840368263008514682295 219941760552394512772023443)
  ·
    refine ⟨329912640828591769158035165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219941760552394512772023443 329912640828591769158035165)
    ·
      refine ⟨123717240310721913434263187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 329912640828591769158035165 123717240310721913434263187)
      ·
        refine ⟨185575860466082870151394781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123717240310721913434263187 185575860466082870151394781)
        ·
          refine ⟨69590947674781076306773043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 185575860466082870151394781 69590947674781076306773043)
          ·
            refine ⟨104386421512171614460159565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69590947674781076306773043 104386421512171614460159565)
            ·
              refine ⟨39144908067064355422559837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 104386421512171614460159565 39144908067064355422559837)
              ·
                refine ⟨14679340525149133283459939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39144908067064355422559837 14679340525149133283459939)
                ·
                  refine ⟨22019010787723699925189909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14679340525149133283459939 22019010787723699925189909)
                  ·
                    refine ⟨1032141130674548433993277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22019010787723699925189909 1032141130674548433993277)
                    ·
                      rfl

theorem cell23_6030263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 3, 1, 6].length) (baseStart_6030263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6030263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6030263 prefixEnd_6030263 := by exact prefixLift 6030263
  have htrace : WordTrace (prefixWord ++ tailWord_6030263) baseStart_6030263 baseEnd_6030263 := by
    simpa [prefixWord, tailWord_6030263, baseEnd_6030263] using wordTrace_append hprefix tailTrace_6030263
  have hstable : (prefixWord ++ tailWord_6030263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6030263).length < 2 ^ (prefixWord ++ tailWord_6030263).sum := by decide
  have hdescent : baseEnd_6030263 < baseStart_6030263 := by decide
  rcases family_descends (prefixWord ++ tailWord_6030263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6030270 : List Nat := [4, 2, 1, 1, 1, 2, 1, 3, 3, 1, 4]
def baseStart_6030270 : Nat := 118140960795 + 6030270 * 2 ^ 59
def prefixEnd_6030270 : Nat := 4983230072969 + 3 ^ 40 * 6030270 * 2
def baseEnd_6030270 : Nat := 3096426986388226774592299

theorem tailTrace_6030270 : CollatzResearch.WordTrace tailWord_6030270 prefixEnd_6030270 3096426986388226774592299 := by
  unfold tailWord_6030270
  simp only [CollatzResearch.WordTrace]
  refine ⟨27492751982921144120941033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 146628010575579435311685509 27492751982921144120941033)
  ·
    refine ⟨20619563987190858090705775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27492751982921144120941033 20619563987190858090705775)
    ·
      refine ⟨30929345980786287136058663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20619563987190858090705775 30929345980786287136058663)
      ·
        refine ⟨46394018971179430704087995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30929345980786287136058663 46394018971179430704087995)
        ·
          refine ⟨69591028456769146056131993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46394018971179430704087995 69591028456769146056131993)
          ·
            refine ⟨52193271342576859542098995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69591028456769146056131993 52193271342576859542098995)
            ·
              refine ⟨78289907013865289313148493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52193271342576859542098995 78289907013865289313148493)
              ·
                refine ⟨29358715130199483492430685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78289907013865289313148493 29358715130199483492430685)
                ·
                  refine ⟨11009518173824806309661507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29358715130199483492430685 11009518173824806309661507)
                  ·
                    refine ⟨16514277260737209464492261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11009518173824806309661507 16514277260737209464492261)
                    ·
                      refine ⟨3096426986388226774592299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16514277260737209464492261 3096426986388226774592299)
                      ·
                        rfl

theorem cell23_6030270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 3, 3, 1, 4].length) (baseStart_6030270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6030270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6030270 prefixEnd_6030270 := by exact prefixLift 6030270
  have htrace : WordTrace (prefixWord ++ tailWord_6030270) baseStart_6030270 baseEnd_6030270 := by
    simpa [prefixWord, tailWord_6030270, baseEnd_6030270] using wordTrace_append hprefix tailTrace_6030270
  have hstable : (prefixWord ++ tailWord_6030270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6030270).length < 2 ^ (prefixWord ++ tailWord_6030270).sum := by decide
  have hdescent : baseEnd_6030270 < baseStart_6030270 := by decide
  rcases family_descends (prefixWord ++ tailWord_6030270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6030287 : List Nat := [1, 1, 2, 1, 1, 6, 4, 1, 1, 1, 4]
def baseStart_6030287 : Nat := 118140960795 + 6030287 * 2 ^ 59
def prefixEnd_6030287 : Nat := 4983230072969 + 3 ^ 40 * 6030287 * 2
def baseEnd_6030287 : Nat := 3096435715559353208079721

theorem tailTrace_6030287 : CollatzResearch.WordTrace tailWord_6030287 prefixEnd_6030287 3096435715559353208079721 := by
  unfold tailWord_6030287
  simp only [CollatzResearch.WordTrace]
  refine ⟨219942635904307564870897115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146628423936205043247264743 219942635904307564870897115)
  ·
    refine ⟨329913953856461347306345673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219942635904307564870897115 329913953856461347306345673)
    ·
      refine ⟨247435465392346010479759255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 329913953856461347306345673 247435465392346010479759255)
      ·
        refine ⟨371153198088519015719638883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 247435465392346010479759255 371153198088519015719638883)
        ·
          refine ⟨556729797132778523579458325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 371153198088519015719638883 556729797132778523579458325)
          ·
            refine ⟨26096709240598993292787109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 556729797132778523579458325 26096709240598993292787109)
            ·
              refine ⟨4893132982612311242397583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26096709240598993292787109 4893132982612311242397583)
              ·
                refine ⟨7339699473918466863596375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4893132982612311242397583 7339699473918466863596375)
                ·
                  refine ⟨11009549210877700295394563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7339699473918466863596375 11009549210877700295394563)
                  ·
                    refine ⟨16514323816316550443091845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11009549210877700295394563 16514323816316550443091845)
                    ·
                      refine ⟨3096435715559353208079721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16514323816316550443091845 3096435715559353208079721)
                      ·
                        rfl

theorem cell23_6030287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 4, 1, 1, 1, 4].length) (baseStart_6030287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6030287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6030287 prefixEnd_6030287 := by exact prefixLift 6030287
  have htrace : WordTrace (prefixWord ++ tailWord_6030287) baseStart_6030287 baseEnd_6030287 := by
    simpa [prefixWord, tailWord_6030287, baseEnd_6030287] using wordTrace_append hprefix tailTrace_6030287
  have hstable : (prefixWord ++ tailWord_6030287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6030287).length < 2 ^ (prefixWord ++ tailWord_6030287).sum := by decide
  have hdescent : baseEnd_6030287 < baseStart_6030287 := by decide
  rcases family_descends (prefixWord ++ tailWord_6030287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6030297 : List Nat := [1, 2, 1, 2, 5, 1, 3, 2, 2, 4]
def baseStart_6030297 : Nat := 118140960795 + 6030297 * 2 ^ 59
def prefixEnd_6030297 : Nat := 4983230072969 + 3 ^ 40 * 6030297 * 2
def baseEnd_6030297 : Nat := 1032146950121966056318225

theorem tailTrace_6030297 : CollatzResearch.WordTrace tailWord_6030297 prefixEnd_6030297 1032146950121966056318225 := by
  unfold tailWord_6030297
  simp only [CollatzResearch.WordTrace]
  refine ⟨219943000634271336578761145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146628667089514224385840763 219943000634271336578761145)
  ·
    refine ⟨164957250475703502434070859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219943000634271336578761145 164957250475703502434070859)
    ·
      refine ⟨247435875713555253651106289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164957250475703502434070859 247435875713555253651106289)
      ·
        refine ⟨185576906785166440238329717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 247435875713555253651106289 185576906785166440238329717)
        ·
          refine ⟨17397835011109353772343411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 185576906785166440238329717 17397835011109353772343411)
          ·
            refine ⟨26096752516664030658515117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17397835011109353772343411 26096752516664030658515117)
            ·
              refine ⟨9786282193749011496943169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26096752516664030658515117 9786282193749011496943169)
              ·
                refine ⟨7339711645311758622707377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9786282193749011496943169 7339711645311758622707377)
                ·
                  refine ⟨5504783733983818967030533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7339711645311758622707377 5504783733983818967030533)
                  ·
                    refine ⟨1032146950121966056318225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5504783733983818967030533 1032146950121966056318225)
                    ·
                      rfl

theorem cell23_6030297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 3, 2, 2, 4].length) (baseStart_6030297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6030297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6030297 prefixEnd_6030297 := by exact prefixLift 6030297
  have htrace : WordTrace (prefixWord ++ tailWord_6030297) baseStart_6030297 baseEnd_6030297 := by
    simpa [prefixWord, tailWord_6030297, baseEnd_6030297] using wordTrace_append hprefix tailTrace_6030297
  have hstable : (prefixWord ++ tailWord_6030297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6030297).length < 2 ^ (prefixWord ++ tailWord_6030297).sum := by decide
  have hdescent : baseEnd_6030297 < baseStart_6030297 := by decide
  rcases family_descends (prefixWord ++ tailWord_6030297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6030314 : List Nat := [3, 1, 3, 1, 2, 3, 3, 1, 2, 4]
def baseStart_6030314 : Nat := 118140960795 + 6030314 * 2 ^ 59
def prefixEnd_6030314 : Nat := 4983230072969 + 3 ^ 40 * 6030314 * 2
def baseEnd_6030314 : Nat := 1032149859845674867480699

theorem tailTrace_6030314 : CollatzResearch.WordTrace tailWord_6030314 prefixEnd_6030314 1032149859845674867480699 := by
  unfold tailWord_6030314
  simp only [CollatzResearch.WordTrace]
  refine ⟨54985905168802437120532499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146629080450139832321419997 54985905168802437120532499)
  ·
    refine ⟨82478857753203655680798749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54985905168802437120532499 82478857753203655680798749)
    ·
      refine ⟨30929571657451370880299531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82478857753203655680798749 30929571657451370880299531)
      ·
        refine ⟨46394357486177056320449297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30929571657451370880299531 46394357486177056320449297)
        ·
          refine ⟨34795768114632792240336973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46394357486177056320449297 34795768114632792240336973)
          ·
            refine ⟨13048413042987297090126365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34795768114632792240336973 13048413042987297090126365)
            ·
              refine ⟨4893154891120236408797387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13048413042987297090126365 4893154891120236408797387)
              ·
                refine ⟨7339732336680354613196081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4893154891120236408797387 7339732336680354613196081)
                ·
                  refine ⟨5504799252510265959897061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7339732336680354613196081 5504799252510265959897061)
                  ·
                    refine ⟨1032149859845674867480699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5504799252510265959897061 1032149859845674867480699)
                    ·
                      rfl

theorem cell23_6030314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 3, 1, 2, 4].length) (baseStart_6030314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6030314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6030314 prefixEnd_6030314 := by exact prefixLift 6030314
  have htrace : WordTrace (prefixWord ++ tailWord_6030314) baseStart_6030314 baseEnd_6030314 := by
    simpa [prefixWord, tailWord_6030314, baseEnd_6030314] using wordTrace_append hprefix tailTrace_6030314
  have hstable : (prefixWord ++ tailWord_6030314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6030314).length < 2 ^ (prefixWord ++ tailWord_6030314).sum := by decide
  have hdescent : baseEnd_6030314 < baseStart_6030314 := by decide
  rcases family_descends (prefixWord ++ tailWord_6030314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6030330 : List Nat := [3, 1, 1, 1, 1, 2, 1, 2, 2, 7, 2]
def baseStart_6030330 : Nat := 118140960795 + 6030330 * 2 ^ 59
def prefixEnd_6030330 : Nat := 4983230072969 + 3 ^ 40 * 6030330 * 2
def baseEnd_6030330 : Nat := 3096457795227496539842023

theorem tailTrace_6030330 : CollatzResearch.WordTrace tailWord_6030330 prefixEnd_6030330 3096457795227496539842023 := by
  unfold tailWord_6030330
  simp only [CollatzResearch.WordTrace]
  refine ⟨54986051060787945803678111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146629469495434522143141629 54986051060787945803678111)
  ·
    refine ⟨82479076591181918705517167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54986051060787945803678111 82479076591181918705517167)
    ·
      refine ⟨123718614886772878058275751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82479076591181918705517167 123718614886772878058275751)
      ·
        refine ⟨185577922330159317087413627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123718614886772878058275751 185577922330159317087413627)
        ·
          refine ⟨278366883495238975631120441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185577922330159317087413627 278366883495238975631120441)
          ·
            refine ⟨208775162621429231723340331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 278366883495238975631120441 208775162621429231723340331)
            ·
              refine ⟨313162743932143847585010497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 208775162621429231723340331 313162743932143847585010497)
              ·
                refine ⟨234872057949107885688757873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 313162743932143847585010497 234872057949107885688757873)
                ·
                  refine ⟨176154043461830914266568405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 234872057949107885688757873 176154043461830914266568405)
                  ·
                    refine ⟨4128610393636662053122697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 176154043461830914266568405 4128610393636662053122697)
                    ·
                      refine ⟨3096457795227496539842023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4128610393636662053122697 3096457795227496539842023)
                      ·
                        rfl

theorem cell23_6030330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 2, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 2, 2, 7, 2].length) (baseStart_6030330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6030330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6030330 prefixEnd_6030330 := by exact prefixLift 6030330
  have htrace : WordTrace (prefixWord ++ tailWord_6030330) baseStart_6030330 baseEnd_6030330 := by
    simpa [prefixWord, tailWord_6030330, baseEnd_6030330] using wordTrace_append hprefix tailTrace_6030330
  have hstable : (prefixWord ++ tailWord_6030330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6030330).length < 2 ^ (prefixWord ++ tailWord_6030330).sum := by decide
  have hdescent : baseEnd_6030330 < baseStart_6030330 := by decide
  rcases family_descends (prefixWord ++ tailWord_6030330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6030337 : List Nat := [1, 2, 4, 1, 2, 2, 1, 2, 4, 1, 3]
def baseStart_6030337 : Nat := 118140960795 + 6030337 * 2 ^ 59
def prefixEnd_6030337 : Nat := 4983230072969 + 3 ^ 40 * 6030337 * 2
def baseEnd_6030337 : Nat := 3096461389592078012454491

theorem tailTrace_6030337 : CollatzResearch.WordTrace tailWord_6030337 prefixEnd_6030337 3096461389592078012454491 := by
  unfold tailWord_6030337
  simp only [CollatzResearch.WordTrace]
  refine ⟨219944459554126423410217265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146629639702750948940144843 219944459554126423410217265)
  ·
    refine ⟨164958344665594817557662949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219944459554126423410217265 164958344665594817557662949)
    ·
      refine ⟨30929689624799028292061803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 164958344665594817557662949 30929689624799028292061803)
      ·
        refine ⟨46394534437198542438092705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30929689624799028292061803 46394534437198542438092705)
        ·
          refine ⟨34795900827898906828569529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46394534437198542438092705 34795900827898906828569529)
          ·
            refine ⟨26096925620924180121427147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34795900827898906828569529 26096925620924180121427147)
            ·
              refine ⟨39145388431386270182140721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26096925620924180121427147 39145388431386270182140721)
              ·
                refine ⟨29359041323539702636605541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39145388431386270182140721 29359041323539702636605541)
                ·
                  refine ⟨5504820248163694244363539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29359041323539702636605541 5504820248163694244363539)
                  ·
                    refine ⟨8257230372245541366545309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5504820248163694244363539 8257230372245541366545309)
                    ·
                      refine ⟨3096461389592078012454491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8257230372245541366545309 3096461389592078012454491)
                      ·
                        rfl

theorem cell23_6030337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 2, 4, 1, 3].length) (baseStart_6030337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6030337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6030337 prefixEnd_6030337 := by exact prefixLift 6030337
  have htrace : WordTrace (prefixWord ++ tailWord_6030337) baseStart_6030337 baseEnd_6030337 := by
    simpa [prefixWord, tailWord_6030337, baseEnd_6030337] using wordTrace_append hprefix tailTrace_6030337
  have hstable : (prefixWord ++ tailWord_6030337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6030337).length < 2 ^ (prefixWord ++ tailWord_6030337).sum := by decide
  have hdescent : baseEnd_6030337 < baseStart_6030337 := by decide
  rcases family_descends (prefixWord ++ tailWord_6030337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6030353 : List Nat := [1, 2, 2, 1, 1, 2, 1, 3, 4, 6]
def baseStart_6030353 : Nat := 118140960795 + 6030353 * 2 ^ 59
def prefixEnd_6030353 : Nat := 4983230072969 + 3 ^ 40 * 6030353 * 2
def baseEnd_6030353 : Nat := 1032156535094183316618139

theorem tailTrace_6030353 : CollatzResearch.WordTrace tailWord_6030353 prefixEnd_6030353 1032156535094183316618139 := by
  unfold tailWord_6030353
  simp only [CollatzResearch.WordTrace]
  refine ⟨219945043122068458142799713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146630028748045638761866475 219945043122068458142799713)
  ·
    refine ⟨164958782341551343607099785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219945043122068458142799713 164958782341551343607099785)
    ·
      refine ⟨123719086756163507705324839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164958782341551343607099785 123719086756163507705324839)
      ·
        refine ⟨185578630134245261557987259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123719086756163507705324839 185578630134245261557987259)
        ·
          refine ⟨278367945201367892336980889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185578630134245261557987259 278367945201367892336980889)
          ·
            refine ⟨208775958901025919252735667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 278367945201367892336980889 208775958901025919252735667)
            ·
              refine ⟨313163938351538878879103501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 208775958901025919252735667 313163938351538878879103501)
              ·
                refine ⟨117436476881827079579663813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 313163938351538878879103501 117436476881827079579663813)
                ·
                  refine ⟨22019339415342577421186965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 117436476881827079579663813 22019339415342577421186965)
                  ·
                    refine ⟨1032156535094183316618139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22019339415342577421186965 1032156535094183316618139)
                    ·
                      rfl

theorem cell23_6030353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 6].length) (baseStart_6030353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6030353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6030353 prefixEnd_6030353 := by exact prefixLift 6030353
  have htrace : WordTrace (prefixWord ++ tailWord_6030353) baseStart_6030353 baseEnd_6030353 := by
    simpa [prefixWord, tailWord_6030353, baseEnd_6030353] using wordTrace_append hprefix tailTrace_6030353
  have hstable : (prefixWord ++ tailWord_6030353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6030353).length < 2 ^ (prefixWord ++ tailWord_6030353).sum := by decide
  have hdescent : baseEnd_6030353 < baseStart_6030353 := by decide
  rcases family_descends (prefixWord ++ tailWord_6030353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6030371 : List Nat := [1, 1, 1, 4, 3, 4, 2, 1, 2, 1, 3]
def baseStart_6030371 : Nat := 118140960795 + 6030371 * 2 ^ 59
def prefixEnd_6030371 : Nat := 4983230072969 + 3 ^ 40 * 6030371 * 2
def baseEnd_6030371 : Nat := 3096478847934330879429335

theorem tailTrace_6030371 : CollatzResearch.WordTrace tailWord_6030371 prefixEnd_6030371 3096478847934330879429335 := by
  unfold tailWord_6030371
  simp only [CollatzResearch.WordTrace]
  refine ⟨219945699636003247216954967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146630466424002164811303311 219945699636003247216954967)
  ·
    refine ⟨329918549454004870825432451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219945699636003247216954967 329918549454004870825432451)
    ·
      refine ⟨494877824181007306238148677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 329918549454004870825432451 494877824181007306238148677)
      ·
        refine ⟨92789592033938869919652877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 494877824181007306238148677 92789592033938869919652877)
        ·
          refine ⟨34796097012727076219869829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92789592033938869919652877 34796097012727076219869829)
          ·
            refine ⟨6524268189886326791225593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34796097012727076219869829 6524268189886326791225593)
            ·
              refine ⟨4893201142414745093419195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6524268189886326791225593 4893201142414745093419195)
              ·
                refine ⟨7339801713622117640128793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4893201142414745093419195 7339801713622117640128793)
                ·
                  refine ⟨5504851285216588230096595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7339801713622117640128793 5504851285216588230096595)
                  ·
                    refine ⟨8257276927824882345144893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5504851285216588230096595 8257276927824882345144893)
                    ·
                      refine ⟨3096478847934330879429335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8257276927824882345144893 3096478847934330879429335)
                      ·
                        rfl

theorem cell23_6030371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 2, 1, 2, 1, 3].length) (baseStart_6030371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6030371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6030371 prefixEnd_6030371 := by exact prefixLift 6030371
  have htrace : WordTrace (prefixWord ++ tailWord_6030371) baseStart_6030371 baseEnd_6030371 := by
    simpa [prefixWord, tailWord_6030371, baseEnd_6030371] using wordTrace_append hprefix tailTrace_6030371
  have hstable : (prefixWord ++ tailWord_6030371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6030371).length < 2 ^ (prefixWord ++ tailWord_6030371).sum := by decide
  have hdescent : baseEnd_6030371 < baseStart_6030371 := by decide
  rcases family_descends (prefixWord ++ tailWord_6030371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6030398 : List Nat := [4, 2, 1, 3, 1, 2, 3, 1, 1, 3, 2]
def baseStart_6030398 : Nat := 118140960795 + 6030398 * 2 ^ 59
def prefixEnd_6030398 : Nat := 4983230072969 + 3 ^ 40 * 6030398 * 2
def baseEnd_6030398 : Nat := 3096492711912002273791711

theorem tailTrace_6030398 : CollatzResearch.WordTrace tailWord_6030398 prefixEnd_6030398 3096492711912002273791711 := by
  unfold tailWord_6030398
  simp only [CollatzResearch.WordTrace]
  refine ⟨27493335550863178853523481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 146631122937936953885458565 27493335550863178853523481)
  ·
    refine ⟨20620001663147384140142611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27493335550863178853523481 20620001663147384140142611)
    ·
      refine ⟨30930002494721076210213917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20620001663147384140142611 30930002494721076210213917)
      ·
        refine ⟨11598750935520403578830219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30930002494721076210213917 11598750935520403578830219)
        ·
          refine ⟨17398126403280605368245329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11598750935520403578830219 17398126403280605368245329)
          ·
            refine ⟨13048594802460454026183997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17398126403280605368245329 13048594802460454026183997)
            ·
              refine ⟨4893223050922670259818999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13048594802460454026183997 4893223050922670259818999)
              ·
                refine ⟨7339834576384005389728499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4893223050922670259818999 7339834576384005389728499)
                ·
                  refine ⟨11009751864576008084592749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7339834576384005389728499 11009751864576008084592749)
                  ·
                    refine ⟨4128656949216003031722281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11009751864576008084592749 4128656949216003031722281)
                    ·
                      refine ⟨3096492711912002273791711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4128656949216003031722281 3096492711912002273791711)
                      ·
                        rfl

theorem cell23_6030398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 3, 1, 1, 3, 2].length) (baseStart_6030398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6030398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6030398 prefixEnd_6030398 := by exact prefixLift 6030398
  have htrace : WordTrace (prefixWord ++ tailWord_6030398) baseStart_6030398 baseEnd_6030398 := by
    simpa [prefixWord, tailWord_6030398, baseEnd_6030398] using wordTrace_append hprefix tailTrace_6030398
  have hstable : (prefixWord ++ tailWord_6030398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6030398).length < 2 ^ (prefixWord ++ tailWord_6030398).sum := by decide
  have hdescent : baseEnd_6030398 < baseStart_6030398 := by decide
  rcases family_descends (prefixWord ++ tailWord_6030398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6030437 : List Nat := [1, 3, 1, 3, 2, 1, 1, 2, 2, 5, 2]
def baseStart_6030437 : Nat := 118140960795 + 6030437 * 2 ^ 59
def prefixEnd_6030437 : Nat := 4983230072969 + 3 ^ 40 * 6030437 * 2
def baseEnd_6030437 : Nat := 3096512737657527621204031

theorem tailTrace_6030437 : CollatzResearch.WordTrace tailWord_6030437 prefixEnd_6030437 3096512737657527621204031 := by
  unfold tailWord_6030437
  simp only [CollatzResearch.WordTrace]
  refine ⟨219948106853764140488857565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146632071235842760325905043 219948106853764140488857565)
  ·
    refine ⟨82480540070161552683321587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 219948106853764140488857565 82480540070161552683321587)
    ·
      refine ⟨123720810105242329024982381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82480540070161552683321587 123720810105242329024982381)
      ·
        refine ⟨46395303789465873384368393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123720810105242329024982381 46395303789465873384368393)
        ·
          refine ⟨34796477842099405038276295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46395303789465873384368393 34796477842099405038276295)
          ·
            refine ⟨52194716763149107557414443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34796477842099405038276295 52194716763149107557414443)
            ·
              refine ⟨78292075144723661336121665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52194716763149107557414443 78292075144723661336121665)
              ·
                refine ⟨58719056358542746002091249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78292075144723661336121665 58719056358542746002091249)
                ·
                  refine ⟨44039292268907059501568437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58719056358542746002091249 44039292268907059501568437)
                  ·
                    refine ⟨4128683650210036828272041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 44039292268907059501568437 4128683650210036828272041)
                    ·
                      refine ⟨3096512737657527621204031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4128683650210036828272041 3096512737657527621204031)
                      ·
                        rfl

theorem cell23_6030437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 2, 2, 5, 2].length) (baseStart_6030437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6030437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6030437 prefixEnd_6030437 := by exact prefixLift 6030437
  have htrace : WordTrace (prefixWord ++ tailWord_6030437) baseStart_6030437 baseEnd_6030437 := by
    simpa [prefixWord, tailWord_6030437, baseEnd_6030437] using wordTrace_append hprefix tailTrace_6030437
  have hstable : (prefixWord ++ tailWord_6030437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6030437).length < 2 ^ (prefixWord ++ tailWord_6030437).sum := by decide
  have hdescent : baseEnd_6030437 < baseStart_6030437 := by decide
  rcases family_descends (prefixWord ++ tailWord_6030437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6030467 : List Nat := [1, 1, 1, 3, 3, 2, 1, 1, 4, 4, 2]
def baseStart_6030467 : Nat := 118140960795 + 6030467 * 2 ^ 59
def prefixEnd_6030467 : Nat := 4983230072969 + 3 ^ 40 * 6030467 * 2
def baseEnd_6030467 : Nat := 3096528142077162503828893

theorem tailTrace_6030467 : CollatzResearch.WordTrace tailWord_6030467 prefixEnd_6030467 3096528142077162503828893 := by
  unfold tailWord_6030467
  simp only [CollatzResearch.WordTrace]
  refine ⟨219949201043655455612449655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146632800695770303741633103 219949201043655455612449655)
  ·
    refine ⟨329923801565483183418674483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219949201043655455612449655 329923801565483183418674483)
    ·
      refine ⟨494885702348224775128011725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 329923801565483183418674483 494885702348224775128011725)
      ·
        refine ⟨185582138380584290673004397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 494885702348224775128011725 185582138380584290673004397)
        ·
          refine ⟨69593301892719109002376649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 185582138380584290673004397 69593301892719109002376649)
          ·
            refine ⟨52194976419539331751782487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69593301892719109002376649 52194976419539331751782487)
            ·
              refine ⟨78292464629308997627673731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52194976419539331751782487 78292464629308997627673731)
              ·
                refine ⟨117438696943963496441510597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78292464629308997627673731 117438696943963496441510597)
                ·
                  refine ⟨22019755676993155582783237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 117438696943963496441510597 22019755676993155582783237)
                  ·
                    refine ⟨4128704189436216671771857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22019755676993155582783237 4128704189436216671771857)
                    ·
                      refine ⟨3096528142077162503828893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4128704189436216671771857 3096528142077162503828893)
                      ·
                        rfl

theorem cell23_6030467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 1, 4, 4, 2].length) (baseStart_6030467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6030467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6030467 prefixEnd_6030467 := by exact prefixLift 6030467
  have htrace : WordTrace (prefixWord ++ tailWord_6030467) baseStart_6030467 baseEnd_6030467 := by
    simpa [prefixWord, tailWord_6030467, baseEnd_6030467] using wordTrace_append hprefix tailTrace_6030467
  have hstable : (prefixWord ++ tailWord_6030467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6030467).length < 2 ^ (prefixWord ++ tailWord_6030467).sum := by decide
  have hdescent : baseEnd_6030467 < baseStart_6030467 := by decide
  rcases family_descends (prefixWord ++ tailWord_6030467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6030487 : List Nat := [1, 1, 3, 3, 3, 1, 1, 2, 1, 4, 3]
def baseStart_6030487 : Nat := 118140960795 + 6030487 * 2 ^ 59
def prefixEnd_6030487 : Nat := 4983230072969 + 3 ^ 40 * 6030487 * 2
def baseEnd_6030487 : Nat := 3096538411690252425578801

theorem tailTrace_6030487 : CollatzResearch.WordTrace tailWord_6030487 prefixEnd_6030487 3096538411690252425578801 := by
  unfold tailWord_6030487
  simp only [CollatzResearch.WordTrace]
  refine ⟨219949930503582999028177715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146633287002388666018785143 219949930503582999028177715)
  ·
    refine ⟨329924895755374498542266573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219949930503582999028177715 329924895755374498542266573)
    ·
      refine ⟨123721835908265436953349965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 329924895755374498542266573 123721835908265436953349965)
      ·
        refine ⟨46395688465599538857506237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123721835908265436953349965 46395688465599538857506237)
        ·
          refine ⟨17398383174599827071564839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46395688465599538857506237 17398383174599827071564839)
          ·
            refine ⟨26097574761899740607347259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17398383174599827071564839 26097574761899740607347259)
            ·
              refine ⟨39146362142849610911020889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26097574761899740607347259 39146362142849610911020889)
              ·
                refine ⟨29359771607137208183265667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39146362142849610911020889 29359771607137208183265667)
                ·
                  refine ⟨44039657410705812274898501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29359771607137208183265667 44039657410705812274898501)
                  ·
                    refine ⟨8257435764507339801543469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 44039657410705812274898501 8257435764507339801543469)
                    ·
                      refine ⟨3096538411690252425578801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8257435764507339801543469 3096538411690252425578801)
                      ·
                        rfl

theorem cell23_6030487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 2, 1, 4, 3].length) (baseStart_6030487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6030487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6030487 prefixEnd_6030487 := by exact prefixLift 6030487
  have htrace : WordTrace (prefixWord ++ tailWord_6030487) baseStart_6030487 baseEnd_6030487 := by
    simpa [prefixWord, tailWord_6030487, baseEnd_6030487] using wordTrace_append hprefix tailTrace_6030487
  have hstable : (prefixWord ++ tailWord_6030487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6030487).length < 2 ^ (prefixWord ++ tailWord_6030487).sum := by decide
  have hdescent : baseEnd_6030487 < baseStart_6030487 := by decide
  rcases family_descends (prefixWord ++ tailWord_6030487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6030518 : List Nat := [5, 1, 3, 2, 1, 1, 1, 2, 2, 1, 4]
def baseStart_6030518 : Nat := 118140960795 + 6030518 * 2 ^ 59
def prefixEnd_6030518 : Nat := 4983230072969 + 3 ^ 40 * 6030518 * 2
def baseEnd_6030518 : Nat := 3096554329590541804291159

theorem tailTrace_6030518 : CollatzResearch.WordTrace tailWord_6030518 prefixEnd_6030518 3096554329590541804291159 := by
  unfold tailWord_6030518
  simp only [CollatzResearch.WordTrace]
  refine ⟨13746941322904418207659763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 146634040777647127548370805 13746941322904418207659763)
  ·
    refine ⟨20620411984356627311489645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13746941322904418207659763 20620411984356627311489645)
    ·
      refine ⟨7732654494133735241808617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20620411984356627311489645 7732654494133735241808617)
      ·
        refine ⟨5799490870600301431356463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7732654494133735241808617 5799490870600301431356463)
        ·
          refine ⟨8699236305900452147034695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5799490870600301431356463 8699236305900452147034695)
          ·
            refine ⟨13048854458850678220552043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8699236305900452147034695 13048854458850678220552043)
            ·
              refine ⟨19573281688276017330828065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13048854458850678220552043 19573281688276017330828065)
              ·
                refine ⟨14679961266207012998121049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19573281688276017330828065 14679961266207012998121049)
                ·
                  refine ⟨11009970949655259748590787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14679961266207012998121049 11009970949655259748590787)
                  ·
                    refine ⟨16514956424482889622886181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11009970949655259748590787 16514956424482889622886181)
                    ·
                      refine ⟨3096554329590541804291159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16514956424482889622886181 3096554329590541804291159)
                      ·
                        rfl

theorem cell23_6030518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 1, 2, 2, 1, 4].length) (baseStart_6030518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6030518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6030518 prefixEnd_6030518 := by exact prefixLift 6030518
  have htrace : WordTrace (prefixWord ++ tailWord_6030518) baseStart_6030518 baseEnd_6030518 := by
    simpa [prefixWord, tailWord_6030518, baseEnd_6030518] using wordTrace_append hprefix tailTrace_6030518
  have hstable : (prefixWord ++ tailWord_6030518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6030518).length < 2 ^ (prefixWord ++ tailWord_6030518).sum := by decide
  have hdescent : baseEnd_6030518 < baseStart_6030518 := by decide
  rcases family_descends (prefixWord ++ tailWord_6030518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6030528 : List Nat := [2, 1, 1, 2, 6, 1, 3, 2, 1, 4]
def baseStart_6030528 : Nat := 118140960795 + 6030528 * 2 ^ 59
def prefixEnd_6030528 : Nat := 4983230072969 + 3 ^ 40 * 6030528 * 2
def baseEnd_6030528 : Nat := 1032186488132362255055371

theorem tailTrace_6030528 : CollatzResearch.WordTrace tailWord_6030528 prefixEnd_6030528 1032186488132362255055371 := by
  unfold tailWord_6030528
  simp only [CollatzResearch.WordTrace]
  refine ⟨109975712948217231515210119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146634283930956308686946825 109975712948217231515210119)
  ·
    refine ⟨164963569422325847272815179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109975712948217231515210119 164963569422325847272815179)
    ·
      refine ⟨247445354133488770909222769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164963569422325847272815179 247445354133488770909222769)
      ·
        refine ⟨185584015600116578181917077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 247445354133488770909222769 185584015600116578181917077)
        ·
          refine ⟨8699250731255464602277363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 185584015600116578181917077 8699250731255464602277363)
          ·
            refine ⟨13048876096883196903416045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8699250731255464602277363 13048876096883196903416045)
            ·
              refine ⟨4893328536331198838781017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13048876096883196903416045 4893328536331198838781017)
              ·
                refine ⟨3669996402248399129085763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4893328536331198838781017 3669996402248399129085763)
                ·
                  refine ⟨5504994603372598693628645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3669996402248399129085763 5504994603372598693628645)
                  ·
                    refine ⟨1032186488132362255055371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5504994603372598693628645 1032186488132362255055371)
                    ·
                      rfl

theorem cell23_6030528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 3, 2, 1, 4].length) (baseStart_6030528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6030528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6030528 prefixEnd_6030528 := by exact prefixLift 6030528
  have htrace : WordTrace (prefixWord ++ tailWord_6030528) baseStart_6030528 baseEnd_6030528 := by
    simpa [prefixWord, tailWord_6030528, baseEnd_6030528] using wordTrace_append hprefix tailTrace_6030528
  have hstable : (prefixWord ++ tailWord_6030528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6030528).length < 2 ^ (prefixWord ++ tailWord_6030528).sum := by decide
  have hdescent : baseEnd_6030528 < baseStart_6030528 := by decide
  rcases family_descends (prefixWord ++ tailWord_6030528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6030561 : List Nat := [1, 2, 3, 1, 3, 3, 2, 1, 2, 3, 2]
def baseStart_6030561 : Nat := 118140960795 + 6030561 * 2 ^ 59
def prefixEnd_6030561 : Nat := 4983230072969 + 3 ^ 40 * 6030561 * 2
def baseEnd_6030561 : Nat := 3096576409258685136053461

theorem tailTrace_6030561 : CollatzResearch.WordTrace tailWord_6030561 prefixEnd_6030561 3096576409258685136053461 := by
  unfold tailWord_6030561
  simp only [CollatzResearch.WordTrace]
  refine ⟨219952629505314909666371537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146635086336876606444247691 219952629505314909666371537)
  ·
    refine ⟨164964472128986182249778653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219952629505314909666371537 164964472128986182249778653)
    ·
      refine ⟨61861677048369818343666995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 164964472128986182249778653 61861677048369818343666995)
      ·
        refine ⟨92792515572554727515500493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61861677048369818343666995 92792515572554727515500493)
        ·
          refine ⟨34797193339708022818312685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92792515572554727515500493 34797193339708022818312685)
          ·
            refine ⟨13048947502390508556867257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34797193339708022818312685 13048947502390508556867257)
            ·
              refine ⟨9786710626792881417650443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13048947502390508556867257 9786710626792881417650443)
              ·
                refine ⟨14680065940189322126475665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9786710626792881417650443 14680065940189322126475665)
                ·
                  refine ⟨11010049455141991594856749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14680065940189322126475665 11010049455141991594856749)
                  ·
                    refine ⟨4128768545678246848071281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11010049455141991594856749 4128768545678246848071281)
                    ·
                      refine ⟨3096576409258685136053461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4128768545678246848071281 3096576409258685136053461)
                      ·
                        rfl

theorem cell23_6030561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 2, 1, 2, 3, 2].length) (baseStart_6030561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6030561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6030561 prefixEnd_6030561 := by exact prefixLift 6030561
  have htrace : WordTrace (prefixWord ++ tailWord_6030561) baseStart_6030561 baseEnd_6030561 := by
    simpa [prefixWord, tailWord_6030561, baseEnd_6030561] using wordTrace_append hprefix tailTrace_6030561
  have hstable : (prefixWord ++ tailWord_6030561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6030561).length < 2 ^ (prefixWord ++ tailWord_6030561).sum := by decide
  have hdescent : baseEnd_6030561 < baseStart_6030561 := by decide
  rcases family_descends (prefixWord ++ tailWord_6030561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6030574 : List Nat := [4, 1, 2, 1, 1, 1, 2, 5, 1, 1, 4]
def baseStart_6030574 : Nat := 118140960795 + 6030574 * 2 ^ 59
def prefixEnd_6030574 : Nat := 4983230072969 + 3 ^ 40 * 6030574 * 2
def baseEnd_6030574 : Nat := 3096583084507193585190901

theorem tailTrace_6030574 : CollatzResearch.WordTrace tailWord_6030574 prefixEnd_6030574 3096583084507193585190901 := by
  unfold tailWord_6030574
  simp only [CollatzResearch.WordTrace]
  refine ⟨27494137956783476610824347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 146635402436178541924396517 27494137956783476610824347)
  ·
    refine ⟨41241206935175214916236521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27494137956783476610824347 41241206935175214916236521)
    ·
      refine ⟨30930905201381411187177391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41241206935175214916236521 30930905201381411187177391)
      ·
        refine ⟨46396357802072116780766087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30930905201381411187177391 46396357802072116780766087)
        ·
          refine ⟨69594536703108175171149131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46396357802072116780766087 69594536703108175171149131)
          ·
            refine ⟨104391805054662262756723697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69594536703108175171149131 104391805054662262756723697)
            ·
              refine ⟨78293853790996697067542773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104391805054662262756723697 78293853790996697067542773)
              ·
                refine ⟨7340048792905940350082135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 78293853790996697067542773 7340048792905940350082135)
                ·
                  refine ⟨11010073189358910525123203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7340048792905940350082135 11010073189358910525123203)
                  ·
                    refine ⟨16515109784038365787684805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11010073189358910525123203 16515109784038365787684805)
                    ·
                      refine ⟨3096583084507193585190901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16515109784038365787684805 3096583084507193585190901)
                      ·
                        rfl

theorem cell23_6030574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 5, 1, 1, 4].length) (baseStart_6030574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6030574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6030574 prefixEnd_6030574 := by exact prefixLift 6030574
  have htrace : WordTrace (prefixWord ++ tailWord_6030574) baseStart_6030574 baseEnd_6030574 := by
    simpa [prefixWord, tailWord_6030574, baseEnd_6030574] using wordTrace_append hprefix tailTrace_6030574
  have hstable : (prefixWord ++ tailWord_6030574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6030574).length < 2 ^ (prefixWord ++ tailWord_6030574).sum := by decide
  have hdescent : baseEnd_6030574 < baseStart_6030574 := by decide
  rcases family_descends (prefixWord ++ tailWord_6030574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6030604 : List Nat := [2, 2, 1, 2, 2, 4, 2, 1, 1, 2, 4]
def baseStart_6030604 : Nat := 118140960795 + 6030604 * 2 ^ 59
def prefixEnd_6030604 : Nat := 4983230072969 + 3 ^ 40 * 6030604 * 2
def baseEnd_6030604 : Nat := 3096598488926828467815763

theorem tailTrace_6030604 : CollatzResearch.WordTrace tailWord_6030604 prefixEnd_6030604 3096598488926828467815763 := by
  unfold tailWord_6030604
  simp only [CollatzResearch.WordTrace]
  refine ⟨109977098922079564005093433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146636131896106085340124577 109977098922079564005093433)
  ·
    refine ⟨82482824191559673003820075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109977098922079564005093433 82482824191559673003820075)
    ·
      refine ⟨123724236287339509505730113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82482824191559673003820075 123724236287339509505730113)
      ·
        refine ⟨92793177215504632129297585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123724236287339509505730113 92793177215504632129297585)
        ·
          refine ⟨69594882911628474096973189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92793177215504632129297585 69594882911628474096973189)
          ·
            refine ⟨13049040545930338893182473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 69594882911628474096973189 13049040545930338893182473)
            ·
              refine ⟨9786780409447754169886855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13049040545930338893182473 9786780409447754169886855)
              ·
                refine ⟨14680170614171631254830283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9786780409447754169886855 14680170614171631254830283)
                ·
                  refine ⟨22020255921257446882245425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14680170614171631254830283 22020255921257446882245425)
                  ·
                    refine ⟨16515191940943085161684069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22020255921257446882245425 16515191940943085161684069)
                    ·
                      refine ⟨3096598488926828467815763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16515191940943085161684069 3096598488926828467815763)
                      ·
                        rfl

theorem cell23_6030604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 2, 1, 1, 2, 4].length) (baseStart_6030604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6030604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6030604 prefixEnd_6030604 := by exact prefixLift 6030604
  have htrace : WordTrace (prefixWord ++ tailWord_6030604) baseStart_6030604 baseEnd_6030604 := by
    simpa [prefixWord, tailWord_6030604, baseEnd_6030604] using wordTrace_append hprefix tailTrace_6030604
  have hstable : (prefixWord ++ tailWord_6030604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6030604).length < 2 ^ (prefixWord ++ tailWord_6030604).sum := by decide
  have hdescent : baseEnd_6030604 < baseStart_6030604 := by decide
  rcases family_descends (prefixWord ++ tailWord_6030604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6030622 : List Nat := [4, 3, 2, 1, 3, 1, 2, 1, 1, 5]
def baseStart_6030622 : Nat := 118140960795 + 6030622 * 2 ^ 59
def prefixEnd_6030622 : Nat := 4983230072969 + 3 ^ 40 * 6030622 * 2
def baseEnd_6030622 : Nat := 1032202577192869799130227

theorem tailTrace_6030622 : CollatzResearch.WordTrace tailWord_6030622 prefixEnd_6030622 1032202577192869799130227 := by
  unfold tailWord_6030622
  simp only [CollatzResearch.WordTrace]
  refine ⟨27494356794761739635542765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 146636569572062611389561413 27494356794761739635542765)
  ·
    refine ⟨10310383798035652363328537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27494356794761739635542765 10310383798035652363328537)
    ·
      refine ⟨7732787848526739272496403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10310383798035652363328537 7732787848526739272496403)
      ·
        refine ⟨11599181772790108908744605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7732787848526739272496403 11599181772790108908744605)
        ·
          refine ⟨4349693164796290840779227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11599181772790108908744605 4349693164796290840779227)
          ·
            refine ⟨6524539747194436261168841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4349693164796290840779227 6524539747194436261168841)
            ·
              refine ⟨4893404810395827195876631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6524539747194436261168841 4893404810395827195876631)
              ·
                refine ⟨7340107215593740793814947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4893404810395827195876631 7340107215593740793814947)
                ·
                  refine ⟨11010160823390611190722421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7340107215593740793814947 11010160823390611190722421)
                  ·
                    refine ⟨1032202577192869799130227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11010160823390611190722421 1032202577192869799130227)
                    ·
                      rfl

theorem cell23_6030622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 2, 1, 1, 5].length) (baseStart_6030622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6030622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6030622 prefixEnd_6030622 := by exact prefixLift 6030622
  have htrace : WordTrace (prefixWord ++ tailWord_6030622) baseStart_6030622 baseEnd_6030622 := by
    simpa [prefixWord, tailWord_6030622, baseEnd_6030622] using wordTrace_append hprefix tailTrace_6030622
  have hstable : (prefixWord ++ tailWord_6030622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6030622).length < 2 ^ (prefixWord ++ tailWord_6030622).sum := by decide
  have hdescent : baseEnd_6030622 < baseStart_6030622 := by decide
  rcases family_descends (prefixWord ++ tailWord_6030622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6030641 : List Nat := [1, 2, 2, 3, 3, 2, 1, 1, 4, 1, 3]
def baseStart_6030641 : Nat := 118140960795 + 6030641 * 2 ^ 59
def prefixEnd_6030641 : Nat := 4983230072969 + 3 ^ 40 * 6030641 * 2
def baseEnd_6030641 : Nat := 3096617487711044823053093

theorem tailTrace_6030641 : CollatzResearch.WordTrace tailWord_6030641 prefixEnd_6030641 3096617487711044823053093 := by
  unfold tailWord_6030641
  simp only [CollatzResearch.WordTrace]
  refine ⟨219955547345025083329283777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146637031563350055552855851 219955547345025083329283777)
  ·
    refine ⟨164966660508768812496962833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219955547345025083329283777 164966660508768812496962833)
    ·
      refine ⟨123724995381576609372722125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164966660508768812496962833 123724995381576609372722125)
      ·
        refine ⟨46396873268091228514770797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123724995381576609372722125 46396873268091228514770797)
        ·
          refine ⟨17398827475534210693039049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46396873268091228514770797 17398827475534210693039049)
          ·
            refine ⟨13049120606650658019779287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17398827475534210693039049 13049120606650658019779287)
            ·
              refine ⟨19573680909975987029668931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13049120606650658019779287 19573680909975987029668931)
              ·
                refine ⟨29360521364963980544503397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19573680909975987029668931 29360521364963980544503397)
                ·
                  refine ⟨5505097755930746352094387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29360521364963980544503397 5505097755930746352094387)
                  ·
                    refine ⟨8257646633896119528141581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5505097755930746352094387 8257646633896119528141581)
                    ·
                      refine ⟨3096617487711044823053093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8257646633896119528141581 3096617487711044823053093)
                      ·
                        rfl

theorem cell23_6030641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 1, 1, 4, 1, 3].length) (baseStart_6030641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6030641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6030641 prefixEnd_6030641 := by exact prefixLift 6030641
  have htrace : WordTrace (prefixWord ++ tailWord_6030641) baseStart_6030641 baseEnd_6030641 := by
    simpa [prefixWord, tailWord_6030641, baseEnd_6030641] using wordTrace_append hprefix tailTrace_6030641
  have hstable : (prefixWord ++ tailWord_6030641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6030641).length < 2 ^ (prefixWord ++ tailWord_6030641).sum := by decide
  have hdescent : baseEnd_6030641 < baseStart_6030641 := by decide
  rcases family_descends (prefixWord ++ tailWord_6030641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6030662 : List Nat := [6, 1, 1, 3, 1, 1, 2, 2, 1, 2, 3]
def baseStart_6030662 : Nat := 118140960795 + 6030662 * 2 ^ 59
def prefixEnd_6030662 : Nat := 4983230072969 + 3 ^ 40 * 6030662 * 2
def baseEnd_6030662 : Nat := 3096628270804789240890497

theorem tailTrace_6030662 : CollatzResearch.WordTrace tailWord_6030662 prefixEnd_6030662 3096628270804789240890497 := by
  unfold tailWord_6030662
  simp only [CollatzResearch.WordTrace]
  refine ⟨6873634789935906372368695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 146637542185299335943865493 6873634789935906372368695)
  ·
    refine ⟨10310452184903859558553043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6873634789935906372368695 10310452184903859558553043)
    ·
      refine ⟨15465678277355789337829565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10310452184903859558553043 15465678277355789337829565)
      ·
        refine ⟨5799629354008421001686087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15465678277355789337829565 5799629354008421001686087)
        ·
          refine ⟨8699444031012631502529131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5799629354008421001686087 8699444031012631502529131)
          ·
            refine ⟨13049166046518947253793697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8699444031012631502529131 13049166046518947253793697)
            ·
              refine ⟨9786874534889210440345273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13049166046518947253793697 9786874534889210440345273)
              ·
                refine ⟨7340155901166907830258955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9786874534889210440345273 7340155901166907830258955)
                ·
                  refine ⟨11010233851750361745388433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7340155901166907830258955 11010233851750361745388433)
                  ·
                    refine ⟨8257675388812771309041325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11010233851750361745388433 8257675388812771309041325)
                    ·
                      refine ⟨3096628270804789240890497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8257675388812771309041325 3096628270804789240890497)
                      ·
                        rfl

theorem cell23_6030662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 2, 2, 1, 2, 3].length) (baseStart_6030662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6030662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6030662 prefixEnd_6030662 := by exact prefixLift 6030662
  have htrace : WordTrace (prefixWord ++ tailWord_6030662) baseStart_6030662 baseEnd_6030662 := by
    simpa [prefixWord, tailWord_6030662, baseEnd_6030662] using wordTrace_append hprefix tailTrace_6030662
  have hstable : (prefixWord ++ tailWord_6030662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6030662).length < 2 ^ (prefixWord ++ tailWord_6030662).sum := by decide
  have hdescent : baseEnd_6030662 < baseStart_6030662 := by decide
  rcases family_descends (prefixWord ++ tailWord_6030662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6030667 : List Nat := [1, 1, 1, 1, 3, 1, 1, 2, 3, 6, 3]
def baseStart_6030667 : Nat := 118140960795 + 6030667 * 2 ^ 59
def prefixEnd_6030667 : Nat := 4983230072969 + 3 ^ 40 * 6030667 * 2
def baseEnd_6030667 : Nat := 3096630838208061721327973

theorem tailTrace_6030667 : CollatzResearch.WordTrace tailWord_6030667 prefixEnd_6030667 3096630838208061721327973 := by
  unfold tailWord_6030667
  simp only [CollatzResearch.WordTrace]
  refine ⟨219956495642930889769730255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146637663761953926513153503 219956495642930889769730255)
  ·
    refine ⟨329934743464396334654595383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219956495642930889769730255 329934743464396334654595383)
    ·
      refine ⟨494902115196594501981893075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 329934743464396334654595383 494902115196594501981893075)
      ·
        refine ⟨742353172794891752972839613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 494902115196594501981893075 742353172794891752972839613)
        ·
          refine ⟨278382439798084407364814855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 742353172794891752972839613 278382439798084407364814855)
          ·
            refine ⟨417573659697126611047222283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 278382439798084407364814855 417573659697126611047222283)
            ·
              refine ⟨626360489545689916570833425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 417573659697126611047222283 626360489545689916570833425)
              ·
                refine ⟨469770367159267437428125069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 626360489545689916570833425 469770367159267437428125069)
                ·
                  refine ⟨176163887684725289035546901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 469770367159267437428125069 176163887684725289035546901)
                  ·
                    refine ⟨8257682235221497923541261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 176163887684725289035546901 8257682235221497923541261)
                    ·
                      refine ⟨3096630838208061721327973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8257682235221497923541261 3096630838208061721327973)
                      ·
                        rfl

theorem cell23_6030667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 3, 6, 3].length) (baseStart_6030667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6030667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6030667 prefixEnd_6030667 := by exact prefixLift 6030667
  have htrace : WordTrace (prefixWord ++ tailWord_6030667) baseStart_6030667 baseEnd_6030667 := by
    simpa [prefixWord, tailWord_6030667, baseEnd_6030667] using wordTrace_append hprefix tailTrace_6030667
  have hstable : (prefixWord ++ tailWord_6030667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6030667).length < 2 ^ (prefixWord ++ tailWord_6030667).sum := by decide
  have hdescent : baseEnd_6030667 < baseStart_6030667 := by decide
  rcases family_descends (prefixWord ++ tailWord_6030667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6030668 : List Nat := [2, 2, 1, 3, 2, 3, 2, 2, 1, 3, 2]
def baseStart_6030668 : Nat := 118140960795 + 6030668 * 2 ^ 59
def prefixEnd_6030668 : Nat := 4983230072969 + 3 ^ 40 * 6030668 * 2
def baseEnd_6030668 : Nat := 3096631351688716217415469

theorem tailTrace_6030668 : CollatzResearch.WordTrace tailWord_6030668 prefixEnd_6030668 3096631351688716217415469 := by
  unfold tailWord_6030668
  simp only [CollatzResearch.WordTrace]
  refine ⟨109978266057963633470258329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146637688077284844627011105 109978266057963633470258329)
  ·
    refine ⟨82483699543472725102693747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109978266057963633470258329 82483699543472725102693747)
    ·
      refine ⟨123725549315209087654040621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82483699543472725102693747 123725549315209087654040621)
      ·
        refine ⟨46397080993203407870265233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123725549315209087654040621 46397080993203407870265233)
        ·
          refine ⟨34797810744902555902698925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46397080993203407870265233 34797810744902555902698925)
          ·
            refine ⟨13049179029338458463512097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34797810744902555902698925 13049179029338458463512097)
            ·
              refine ⟨9786884272003843847634073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13049179029338458463512097 9786884272003843847634073)
              ·
                refine ⟨7340163204002882885725555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9786884272003843847634073 7340163204002882885725555)
                ·
                  refine ⟨11010244806004324328588333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7340163204002882885725555 11010244806004324328588333)
                  ·
                    refine ⟨4128841802251621623220625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11010244806004324328588333 4128841802251621623220625)
                    ·
                      refine ⟨3096631351688716217415469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4128841802251621623220625 3096631351688716217415469)
                      ·
                        rfl

theorem cell23_6030668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 2, 2, 1, 3, 2].length) (baseStart_6030668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6030668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6030668 prefixEnd_6030668 := by exact prefixLift 6030668
  have htrace : WordTrace (prefixWord ++ tailWord_6030668) baseStart_6030668 baseEnd_6030668 := by
    simpa [prefixWord, tailWord_6030668, baseEnd_6030668] using wordTrace_append hprefix tailTrace_6030668
  have hstable : (prefixWord ++ tailWord_6030668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6030668).length < 2 ^ (prefixWord ++ tailWord_6030668).sum := by decide
  have hdescent : baseEnd_6030668 < baseStart_6030668 := by decide
  rcases family_descends (prefixWord ++ tailWord_6030668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6030681 : List Nat := [1, 2, 1, 2, 2, 2, 3, 2, 4, 2, 2]
def baseStart_6030681 : Nat := 118140960795 + 6030681 * 2 ^ 59
def prefixEnd_6030681 : Nat := 4983230072969 + 3 ^ 40 * 6030681 * 2
def baseEnd_6030681 : Nat := 3096638026937224666552909

theorem tailTrace_6030681 : CollatzResearch.WordTrace tailWord_6030681 prefixEnd_6030681 3096638026937224666552909 := by
  unfold tailWord_6030681
  simp only [CollatzResearch.WordTrace]
  refine ⟨219957006264880170160739897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146638004176586780107159931 219957006264880170160739897)
  ·
    refine ⟨164967754698660127620554923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219957006264880170160739897 164967754698660127620554923)
    ·
      refine ⟨247451632047990191430832385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164967754698660127620554923 247451632047990191430832385)
      ·
        refine ⟨185588724035992643573124289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 247451632047990191430832385 185588724035992643573124289)
        ·
          refine ⟨139191543026994482679843217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 185588724035992643573124289 139191543026994482679843217)
          ·
            refine ⟨104393657270245862009882413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 139191543026994482679843217 104393657270245862009882413)
            ·
              refine ⟨39147621476342198253705905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 104393657270245862009882413 39147621476342198253705905)
              ·
                refine ⟨29360716107256648690279429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39147621476342198253705905 29360716107256648690279429)
                ·
                  refine ⟨5505134270110621629427393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29360716107256648690279429 5505134270110621629427393)
                  ·
                    refine ⟨4128850702582966222070545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5505134270110621629427393 4128850702582966222070545)
                    ·
                      refine ⟨3096638026937224666552909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4128850702582966222070545 3096638026937224666552909)
                      ·
                        rfl

theorem cell23_6030681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 2, 4, 2, 2].length) (baseStart_6030681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6030681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6030681 prefixEnd_6030681 := by exact prefixLift 6030681
  have htrace : WordTrace (prefixWord ++ tailWord_6030681) baseStart_6030681 baseEnd_6030681 := by
    simpa [prefixWord, tailWord_6030681, baseEnd_6030681] using wordTrace_append hprefix tailTrace_6030681
  have hstable : (prefixWord ++ tailWord_6030681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6030681).length < 2 ^ (prefixWord ++ tailWord_6030681).sum := by decide
  have hdescent : baseEnd_6030681 < baseStart_6030681 := by decide
  rcases family_descends (prefixWord ++ tailWord_6030681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6030781 : List Nat := [1, 4, 1, 2, 2, 1, 3, 2, 3, 4]
def baseStart_6030781 : Nat := 118140960795 + 6030781 * 2 ^ 59
def prefixEnd_6030781 : Nat := 4983230072969 + 3 ^ 40 * 6030781 * 2
def baseEnd_6030781 : Nat := 1032229791667558091767483

theorem tailTrace_6030781 : CollatzResearch.WordTrace tailWord_6030781 prefixEnd_6030781 1032229791667558091767483 := by
  unfold tailWord_6030781
  simp only [CollatzResearch.WordTrace]
  refine ⟨219960653564517887239380197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146640435709678591492920131 219960653564517887239380197)
  ·
    refine ⟨41242622543347103857383787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 219960653564517887239380197 41242622543347103857383787)
    ·
      refine ⟨61863933815020655786075681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41242622543347103857383787 61863933815020655786075681)
      ·
        refine ⟨46397950361265491839556761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61863933815020655786075681 46397950361265491839556761)
        ·
          refine ⟨34798462770949118879667571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46397950361265491839556761 34798462770949118879667571)
          ·
            refine ⟨52197694156423678319501357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34798462770949118879667571 52197694156423678319501357)
            ·
              refine ⟨19574135308658879369813009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52197694156423678319501357 19574135308658879369813009)
              ·
                refine ⟨14680601481494159527359757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19574135308658879369813009 14680601481494159527359757)
                ·
                  refine ⟨5505225555560309822759909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14680601481494159527359757 5505225555560309822759909)
                  ·
                    refine ⟨1032229791667558091767483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5505225555560309822759909 1032229791667558091767483)
                    ·
                      rfl

theorem cell23_6030781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 3, 2, 3, 4].length) (baseStart_6030781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6030781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6030781 prefixEnd_6030781 := by exact prefixLift 6030781
  have htrace : WordTrace (prefixWord ++ tailWord_6030781) baseStart_6030781 baseEnd_6030781 := by
    simpa [prefixWord, tailWord_6030781, baseEnd_6030781] using wordTrace_append hprefix tailTrace_6030781
  have hstable : (prefixWord ++ tailWord_6030781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6030781).length < 2 ^ (prefixWord ++ tailWord_6030781).sum := by decide
  have hdescent : baseEnd_6030781 < baseStart_6030781 := by decide
  rcases family_descends (prefixWord ++ tailWord_6030781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6030788 : List Nat := [2, 3, 3, 2, 1, 1, 3, 1, 2, 1, 4]
def baseStart_6030788 : Nat := 118140960795 + 6030788 * 2 ^ 59
def prefixEnd_6030788 : Nat := 4983230072969 + 3 ^ 40 * 6030788 * 2
def baseEnd_6030788 : Nat := 3096692969367255747914917

theorem tailTrace_6030788 : CollatzResearch.WordTrace tailWord_6030788 prefixEnd_6030788 3096692969367255747914917 := by
  unfold tailWord_6030788
  simp only [CollatzResearch.WordTrace]
  refine ⟨109980454437746263717442509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146640605916995018289923345 109980454437746263717442509)
  ·
    refine ⟨41242670414154848894040941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109980454437746263717442509 41242670414154848894040941)
    ·
      refine ⟨15466001405308068335265353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41242670414154848894040941 15466001405308068335265353)
      ·
        refine ⟨11599501053981051251449015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15466001405308068335265353 11599501053981051251449015)
        ·
          refine ⟨17399251580971576877173523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11599501053981051251449015 17399251580971576877173523)
          ·
            refine ⟨26098877371457365315760285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17399251580971576877173523 26098877371457365315760285)
            ·
              refine ⟨9787079014296511993410107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26098877371457365315760285 9787079014296511993410107)
              ·
                refine ⟨14680618521444767990115161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9787079014296511993410107 14680618521444767990115161)
                ·
                  refine ⟨11010463891083575992586371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14680618521444767990115161 11010463891083575992586371)
                  ·
                    refine ⟨16515695836625363988879557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11010463891083575992586371 16515695836625363988879557)
                    ·
                      refine ⟨3096692969367255747914917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16515695836625363988879557 3096692969367255747914917)
                      ·
                        rfl

theorem cell23_6030788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 3, 1, 2, 1, 4].length) (baseStart_6030788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6030788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6030788 prefixEnd_6030788 := by exact prefixLift 6030788
  have htrace : WordTrace (prefixWord ++ tailWord_6030788) baseStart_6030788 baseEnd_6030788 := by
    simpa [prefixWord, tailWord_6030788, baseEnd_6030788] using wordTrace_append hprefix tailTrace_6030788
  have hstable : (prefixWord ++ tailWord_6030788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6030788).length < 2 ^ (prefixWord ++ tailWord_6030788).sum := by decide
  have hdescent : baseEnd_6030788 < baseStart_6030788 := by decide
  rcases family_descends (prefixWord ++ tailWord_6030788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6030798 : List Nat := [4, 1, 1, 1, 2, 1, 3, 5, 1, 4]
def baseStart_6030798 : Nat := 118140960795 + 6030798 * 2 ^ 59
def prefixEnd_6030798 : Nat := 4983230072969 + 3 ^ 40 * 6030798 * 2
def baseEnd_6030798 : Nat := 1032232701391266902929957

theorem tailTrace_6030798 : CollatzResearch.WordTrace tailWord_6030798 prefixEnd_6030798 1032232701391266902929957 := by
  unfold tailWord_6030798
  simp only [CollatzResearch.WordTrace]
  refine ⟨27495159200682037392843631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 146640849070304199428499365 27495159200682037392843631)
  ·
    refine ⟨41242738801023056089265447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27495159200682037392843631 41242738801023056089265447)
    ·
      refine ⟨61864108201534584133898171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41242738801023056089265447 61864108201534584133898171)
      ·
        refine ⟨92796162302301876200847257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61864108201534584133898171 92796162302301876200847257)
        ·
          refine ⟨69597121726726407150635443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92796162302301876200847257 69597121726726407150635443)
          ·
            refine ⟨104395682590089610725953165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69597121726726407150635443 104395682590089610725953165)
            ·
              refine ⟨39148380971283604022232437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 104395682590089610725953165 39148380971283604022232437)
              ·
                refine ⟨3670160716057837877084291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39148380971283604022232437 3670160716057837877084291)
                ·
                  refine ⟨5505241074086756815626437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3670160716057837877084291 5505241074086756815626437)
                  ·
                    refine ⟨1032232701391266902929957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5505241074086756815626437 1032232701391266902929957)
                    ·
                      rfl

theorem cell23_6030798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 5, 1, 4].length) (baseStart_6030798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6030798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6030798 prefixEnd_6030798 := by exact prefixLift 6030798
  have htrace : WordTrace (prefixWord ++ tailWord_6030798) baseStart_6030798 baseEnd_6030798 := by
    simpa [prefixWord, tailWord_6030798, baseEnd_6030798] using wordTrace_append hprefix tailTrace_6030798
  have hstable : (prefixWord ++ tailWord_6030798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6030798).length < 2 ^ (prefixWord ++ tailWord_6030798).sum := by decide
  have hdescent : baseEnd_6030798 < baseStart_6030798 := by decide
  rcases family_descends (prefixWord ++ tailWord_6030798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6030831 : List Nat := [1, 1, 2, 1, 4, 1, 3, 2, 1, 5, 2]
def baseStart_6030831 : Nat := 118140960795 + 6030831 * 2 ^ 59
def prefixEnd_6030831 : Nat := 4983230072969 + 3 ^ 40 * 6030831 * 2
def baseEnd_6030831 : Nat := 3096715049035399079677219

theorem tailTrace_6030831 : CollatzResearch.WordTrace tailWord_6030831 prefixEnd_6030831 3096715049035399079677219 := by
  unfold tailWord_6030831
  simp only [CollatzResearch.WordTrace]
  refine ⟨219962477214336745778700347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146641651476224497185800231 219962477214336745778700347)
  ·
    refine ⟨329943715821505118668050521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219962477214336745778700347 329943715821505118668050521)
    ·
      refine ⟨247457786866128839001037891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 329943715821505118668050521 247457786866128839001037891)
      ·
        refine ⟨371186680299193258501556837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 247457786866128839001037891 371186680299193258501556837)
        ·
          refine ⟨69597502556098735969041907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 371186680299193258501556837 69597502556098735969041907)
          ·
            refine ⟨104396253834148103953562861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69597502556098735969041907 104396253834148103953562861)
            ·
              refine ⟨39148595187805538982586073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 104396253834148103953562861 39148595187805538982586073)
              ·
                refine ⟨29361446390854154236939555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39148595187805538982586073 29361446390854154236939555)
                ·
                  refine ⟨44042169586281231355409333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29361446390854154236939555 44042169586281231355409333)
                  ·
                    refine ⟨4128953398713865439569625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 44042169586281231355409333 4128953398713865439569625)
                    ·
                      refine ⟨3096715049035399079677219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4128953398713865439569625 3096715049035399079677219)
                      ·
                        rfl

theorem cell23_6030831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 2, 1, 5, 2].length) (baseStart_6030831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6030831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6030831 prefixEnd_6030831 := by exact prefixLift 6030831
  have htrace : WordTrace (prefixWord ++ tailWord_6030831) baseStart_6030831 baseEnd_6030831 := by
    simpa [prefixWord, tailWord_6030831, baseEnd_6030831] using wordTrace_append hprefix tailTrace_6030831
  have hstable : (prefixWord ++ tailWord_6030831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6030831).length < 2 ^ (prefixWord ++ tailWord_6030831).sum := by decide
  have hdescent : baseEnd_6030831 < baseStart_6030831 := by decide
  rcases family_descends (prefixWord ++ tailWord_6030831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6030872 : List Nat := [2, 1, 2, 3, 5, 1, 1, 1, 3, 1, 3]
def baseStart_6030872 : Nat := 118140960795 + 6030872 * 2 ^ 59
def prefixEnd_6030872 : Nat := 4983230072969 + 3 ^ 40 * 6030872 * 2
def baseEnd_6030872 : Nat := 3096736101742233419264531

theorem tailTrace_6030872 : CollatzResearch.WordTrace tailWord_6030872 prefixEnd_6030872 3096736101742233419264531 := by
  unfold tailWord_6030872
  simp only [CollatzResearch.WordTrace]
  refine ⟨109981986303594104890471435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146642648404792139853961913 109981986303594104890471435)
  ·
    refine ⟨164972979455391157335707153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109981986303594104890471435 164972979455391157335707153)
    ·
      refine ⟨123729734591543368001780365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164972979455391157335707153 123729734591543368001780365)
      ·
        refine ⟨46398650471828763000667637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123729734591543368001780365 46398650471828763000667637)
        ·
          refine ⟨4349873481733946531312591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 46398650471828763000667637 4349873481733946531312591)
          ·
            refine ⟨6524810222600919796968887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4349873481733946531312591 6524810222600919796968887)
            ·
              refine ⟨9787215333901379695453331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6524810222600919796968887 9787215333901379695453331)
              ·
                refine ⟨14680823000852069543179997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9787215333901379695453331 14680823000852069543179997)
                ·
                  refine ⟨5505308625319526078692499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14680823000852069543179997 5505308625319526078692499)
                  ·
                    refine ⟨8257962937979289118038749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5505308625319526078692499 8257962937979289118038749)
                    ·
                      refine ⟨3096736101742233419264531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8257962937979289118038749 3096736101742233419264531)
                      ·
                        rfl

theorem cell23_6030872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 1, 1, 3, 1, 3].length) (baseStart_6030872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6030872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6030872 prefixEnd_6030872 := by exact prefixLift 6030872
  have htrace : WordTrace (prefixWord ++ tailWord_6030872) baseStart_6030872 baseEnd_6030872 := by
    simpa [prefixWord, tailWord_6030872, baseEnd_6030872] using wordTrace_append hprefix tailTrace_6030872
  have hstable : (prefixWord ++ tailWord_6030872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6030872).length < 2 ^ (prefixWord ++ tailWord_6030872).sum := by decide
  have hdescent : baseEnd_6030872 < baseStart_6030872 := by decide
  rcases family_descends (prefixWord ++ tailWord_6030872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6030881 : List Nat := [1, 2, 3, 2, 2, 2, 2, 2, 1, 1, 5]
def baseStart_6030881 : Nat := 118140960795 + 6030881 * 2 ^ 59
def prefixEnd_6030881 : Nat := 4983230072969 + 3 ^ 40 * 6030881 * 2
def baseEnd_6030881 : Nat := 3096740723068123884051989

theorem tailTrace_6030881 : CollatzResearch.WordTrace tailWord_6030881 prefixEnd_6030881 3096740723068123884051989 := by
  unfold tailWord_6030881
  simp only [CollatzResearch.WordTrace]
  refine ⟨219964300864155604318020497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146642867242770402878680331 219964300864155604318020497)
  ·
    refine ⟨164973225648116703238515373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219964300864155604318020497 164973225648116703238515373)
    ·
      refine ⟨61864959618043763714443265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 164973225648116703238515373 61864959618043763714443265)
      ·
        refine ⟨46398719713532822785832449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61864959618043763714443265 46398719713532822785832449)
        ·
          refine ⟨34799039785149617089374337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46398719713532822785832449 34799039785149617089374337)
          ·
            refine ⟨26099279838862212817030753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34799039785149617089374337 26099279838862212817030753)
            ·
              refine ⟨19574459879146659612773065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26099279838862212817030753 19574459879146659612773065)
              ·
                refine ⟨14680844909359994709579799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19574459879146659612773065 14680844909359994709579799)
                ·
                  refine ⟨22021267364039992064369699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14680844909359994709579799 22021267364039992064369699)
                  ·
                    refine ⟨33031901046059988096554549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22021267364039992064369699 33031901046059988096554549)
                    ·
                      refine ⟨3096740723068123884051989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33031901046059988096554549 3096740723068123884051989)
                      ·
                        rfl

theorem cell23_6030881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 2, 2, 1, 1, 5].length) (baseStart_6030881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6030881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6030881 prefixEnd_6030881 := by exact prefixLift 6030881
  have htrace : WordTrace (prefixWord ++ tailWord_6030881) baseStart_6030881 baseEnd_6030881 := by
    simpa [prefixWord, tailWord_6030881, baseEnd_6030881] using wordTrace_append hprefix tailTrace_6030881
  have hstable : (prefixWord ++ tailWord_6030881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6030881).length < 2 ^ (prefixWord ++ tailWord_6030881).sum := by decide
  have hdescent : baseEnd_6030881 < baseStart_6030881 := by decide
  rcases family_descends (prefixWord ++ tailWord_6030881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6030908 : List Nat := [2, 2, 2, 2, 4, 1, 1, 2, 1, 2, 4]
def baseStart_6030908 : Nat := 118140960795 + 6030908 * 2 ^ 59
def prefixEnd_6030908 : Nat := 4983230072969 + 3 ^ 40 * 6030908 * 2
def baseEnd_6030908 : Nat := 3096754587045795278414365

theorem tailTrace_6030908 : CollatzResearch.WordTrace tailWord_6030908 prefixEnd_6030908 3096754587045795278414365 := by
  unfold tailWord_6030908
  simp only [CollatzResearch.WordTrace]
  refine ⟨109982642817528893964626689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146643523756705191952835585 109982642817528893964626689)
  ·
    refine ⟨82486982113146670473470017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109982642817528893964626689 82486982113146670473470017)
    ·
      refine ⟨61865236584860002855102513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82486982113146670473470017 61865236584860002855102513)
      ·
        refine ⟨46398927438645002141326885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61865236584860002855102513 46398927438645002141326885)
        ·
          refine ⟨8699798894745937901498791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46398927438645002141326885 8699798894745937901498791)
          ·
            refine ⟨13049698342118906852248187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8699798894745937901498791 13049698342118906852248187)
            ·
              refine ⟨19574547513178360278372281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13049698342118906852248187 19574547513178360278372281)
              ·
                refine ⟨14680910634883770208779211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19574547513178360278372281 14680910634883770208779211)
                ·
                  refine ⟨22021365952325655313168817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14680910634883770208779211 22021365952325655313168817)
                  ·
                    refine ⟨16516024464244241484876613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22021365952325655313168817 16516024464244241484876613)
                    ·
                      refine ⟨3096754587045795278414365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16516024464244241484876613 3096754587045795278414365)
                      ·
                        rfl

theorem cell23_6030908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 1, 2, 1, 2, 4].length) (baseStart_6030908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6030908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6030908 prefixEnd_6030908 := by exact prefixLift 6030908
  have htrace : WordTrace (prefixWord ++ tailWord_6030908) baseStart_6030908 baseEnd_6030908 := by
    simpa [prefixWord, tailWord_6030908, baseEnd_6030908] using wordTrace_append hprefix tailTrace_6030908
  have hstable : (prefixWord ++ tailWord_6030908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6030908).length < 2 ^ (prefixWord ++ tailWord_6030908).sum := by decide
  have hdescent : baseEnd_6030908 < baseStart_6030908 := by decide
  rcases family_descends (prefixWord ++ tailWord_6030908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6030911 : List Nat := [1, 1, 2, 2, 3, 3, 1, 1, 3, 3, 3]
def baseStart_6030911 : Nat := 118140960795 + 6030911 * 2 ^ 59
def prefixEnd_6030911 : Nat := 4983230072969 + 3 ^ 40 * 6030911 * 2
def baseEnd_6030911 : Nat := 3096756127487758766676851

theorem tailTrace_6030911 : CollatzResearch.WordTrace tailWord_6030911 prefixEnd_6030911 3096756127487758766676851 := by
  unfold tailWord_6030911
  simp only [CollatzResearch.WordTrace]
  refine ⟨219965395054046919441612587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146643596702697946294408391 219965395054046919441612587)
  ·
    refine ⟨329948092581070379162418881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219965395054046919441612587 329948092581070379162418881)
    ·
      refine ⟨247461069435802784371814161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 329948092581070379162418881 247461069435802784371814161)
      ·
        refine ⟨185595802076852088278860621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 247461069435802784371814161 185595802076852088278860621)
        ·
          refine ⟨69598425778819533104572733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 185595802076852088278860621 69598425778819533104572733)
          ·
            refine ⟨26099409667057324914214775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69598425778819533104572733 26099409667057324914214775)
            ·
              refine ⟨39149114500585987371322163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26099409667057324914214775 39149114500585987371322163)
              ·
                refine ⟨58723671750878981056983245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39149114500585987371322163 58723671750878981056983245)
                ·
                  refine ⟨22021376906579617896368717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58723671750878981056983245 22021376906579617896368717)
                  ·
                    refine ⟨8258016339967356711138269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22021376906579617896368717 8258016339967356711138269)
                    ·
                      refine ⟨3096756127487758766676851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8258016339967356711138269 3096756127487758766676851)
                      ·
                        rfl

theorem cell23_6030911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 1, 3, 3, 3].length) (baseStart_6030911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6030911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6030911 prefixEnd_6030911 := by exact prefixLift 6030911
  have htrace : WordTrace (prefixWord ++ tailWord_6030911) baseStart_6030911 baseEnd_6030911 := by
    simpa [prefixWord, tailWord_6030911, baseEnd_6030911] using wordTrace_append hprefix tailTrace_6030911
  have hstable : (prefixWord ++ tailWord_6030911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6030911).length < 2 ^ (prefixWord ++ tailWord_6030911).sum := by decide
  have hdescent : baseEnd_6030911 < baseStart_6030911 := by decide
  rcases family_descends (prefixWord ++ tailWord_6030911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6030918 : List Nat := [6, 1, 1, 1, 3, 11]
def baseStart_6030918 : Nat := 118140960795 + 6030918 * 2 ^ 59
def prefixEnd_6030918 : Nat := 4983230072969 + 3 ^ 40 * 6030918 * 2
def baseEnd_6030918 : Nat := 12743867168116626499133

theorem tailTrace_6030918 : CollatzResearch.WordTrace tailWord_6030918 prefixEnd_6030918 12743867168116626499133 := by
  unfold tailWord_6030918
  simp only [CollatzResearch.WordTrace]
  refine ⟨6873926573906923738659919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 146643766910014373091411605 6873926573906923738659919)
  ·
    refine ⟨10310889860860385607989879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6873926573906923738659919 10310889860860385607989879)
    ·
      refine ⟨15466334791290578411984819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10310889860860385607989879 15466334791290578411984819)
      ·
        refine ⟨23199502186935867617977229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15466334791290578411984819 23199502186935867617977229)
        ·
          refine ⟨8699813320100950356741461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23199502186935867617977229 8699813320100950356741461)
          ·
            refine ⟨12743867168116626499133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 8699813320100950356741461 12743867168116626499133)
            ·
              rfl

theorem cell23_6030918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 11].length) (baseStart_6030918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6030918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6030918 prefixEnd_6030918 := by exact prefixLift 6030918
  have htrace : WordTrace (prefixWord ++ tailWord_6030918) baseStart_6030918 baseEnd_6030918 := by
    simpa [prefixWord, tailWord_6030918, baseEnd_6030918] using wordTrace_append hprefix tailTrace_6030918
  have hstable : (prefixWord ++ tailWord_6030918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6030918).length < 2 ^ (prefixWord ++ tailWord_6030918).sum := by decide
  have hdescent : baseEnd_6030918 < baseStart_6030918 := by decide
  rcases family_descends (prefixWord ++ tailWord_6030918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6030981 : List Nat := [1, 3, 1, 1, 4, 1, 1, 1, 4, 2, 4]
def baseStart_6030981 : Nat := 118140960795 + 6030981 * 2 ^ 59
def prefixEnd_6030981 : Nat := 4983230072969 + 3 ^ 40 * 6030981 * 2
def baseEnd_6030981 : Nat := 3096792071133573492801529

theorem tailTrace_6030981 : CollatzResearch.WordTrace tailWord_6030981 prefixEnd_6030981 3096792071133573492801529 := by
  unfold tailWord_6030981
  simp only [CollatzResearch.WordTrace]
  refine ⟨219967948163793321396660797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146645298775862214264440531 219967948163793321396660797)
  ·
    refine ⟨82487980561422495523747799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 219967948163793321396660797 82487980561422495523747799)
    ·
      refine ⟨123731970842133743285621699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82487980561422495523747799 123731970842133743285621699)
      ·
        refine ⟨185597956263200614928432549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123731970842133743285621699 185597956263200614928432549)
        ·
          refine ⟨34799616799350115299081103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 185597956263200614928432549 34799616799350115299081103)
          ·
            refine ⟨52199425199025172948621655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34799616799350115299081103 52199425199025172948621655)
            ·
              refine ⟨78299137798537759422932483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52199425199025172948621655 78299137798537759422932483)
              ·
                refine ⟨117448706697806639134398725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78299137798537759422932483 117448706697806639134398725)
                ·
                  refine ⟨22021632505838744837699761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 117448706697806639134398725 22021632505838744837699761)
                  ·
                    refine ⟨16516224379379058628274821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22021632505838744837699761 16516224379379058628274821)
                    ·
                      refine ⟨3096792071133573492801529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16516224379379058628274821 3096792071133573492801529)
                      ·
                        rfl

theorem cell23_6030981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 1, 4, 2, 4].length) (baseStart_6030981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6030981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6030981 prefixEnd_6030981 := by exact prefixLift 6030981
  have htrace : WordTrace (prefixWord ++ tailWord_6030981) baseStart_6030981 baseEnd_6030981 := by
    simpa [prefixWord, tailWord_6030981, baseEnd_6030981] using wordTrace_append hprefix tailTrace_6030981
  have hstable : (prefixWord ++ tailWord_6030981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6030981).length < 2 ^ (prefixWord ++ tailWord_6030981).sum := by decide
  have hdescent : baseEnd_6030981 < baseStart_6030981 := by decide
  rcases family_descends (prefixWord ++ tailWord_6030981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6031001 : List Nat := [1, 2, 1, 2, 1, 2, 2, 3, 1, 5, 3]
def baseStart_6031001 : Nat := 118140960795 + 6031001 * 2 ^ 59
def prefixEnd_6031001 : Nat := 4983230072969 + 3 ^ 40 * 6031001 * 2
def baseEnd_6031001 : Nat := 3096802340746663414551437

theorem tailTrace_6031001 : CollatzResearch.WordTrace tailWord_6031001 prefixEnd_6031001 3096802340746663414551437 := by
  unfold tailWord_6031001
  simp only [CollatzResearch.WordTrace]
  refine ⟨219968677623720864812388857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146645785082480576541592571 219968677623720864812388857)
  ·
    refine ⟨164976508217790648609291643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219968677623720864812388857 164976508217790648609291643)
    ·
      refine ⟨247464762326685972913937465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164976508217790648609291643 247464762326685972913937465)
      ·
        refine ⟨185598571745014479685453099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 247464762326685972913937465 185598571745014479685453099)
        ·
          refine ⟨278397857617521719528179649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185598571745014479685453099 278397857617521719528179649)
          ·
            refine ⟨208798393213141289646134737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 278397857617521719528179649 208798393213141289646134737)
            ·
              refine ⟨156598794909855967234601053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 208798393213141289646134737 156598794909855967234601053)
              ·
                refine ⟨58724548091195987712975395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 156598794909855967234601053 58724548091195987712975395)
                ·
                  refine ⟨88086822136793981569463093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58724548091195987712975395 88086822136793981569463093)
                  ·
                    refine ⟨8258139575324435772137165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 88086822136793981569463093 8258139575324435772137165)
                    ·
                      refine ⟨3096802340746663414551437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8258139575324435772137165 3096802340746663414551437)
                      ·
                        rfl

theorem cell23_6031001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 3, 1, 5, 3].length) (baseStart_6031001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6031001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6031001 prefixEnd_6031001 := by exact prefixLift 6031001
  have htrace : WordTrace (prefixWord ++ tailWord_6031001) baseStart_6031001 baseEnd_6031001 := by
    simpa [prefixWord, tailWord_6031001, baseEnd_6031001] using wordTrace_append hprefix tailTrace_6031001
  have hstable : (prefixWord ++ tailWord_6031001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6031001).length < 2 ^ (prefixWord ++ tailWord_6031001).sum := by decide
  have hdescent : baseEnd_6031001 < baseStart_6031001 := by decide
  rcases family_descends (prefixWord ++ tailWord_6031001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6031038 : List Nat := [4, 2, 1, 1, 2, 2, 1, 1, 4, 5]
def baseStart_6031038 : Nat := 118140960795 + 6031038 * 2 ^ 59
def prefixEnd_6031038 : Nat := 4983230072969 + 3 ^ 40 * 6031038 * 2
def baseEnd_6031038 : Nat := 1032273779843626589929589

theorem tailTrace_6031038 : CollatzResearch.WordTrace tailWord_6031038 prefixEnd_6031038 1032273779843626589929589 := by
  unfold tailWord_6031038
  simp only [CollatzResearch.WordTrace]
  refine ⟨27496253390573352516435721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 146646684749724546754323845 27496253390573352516435721)
  ·
    refine ⟨20622190042930014387326791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27496253390573352516435721 20622190042930014387326791)
    ·
      refine ⟨30933285064395021580990187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20622190042930014387326791 30933285064395021580990187)
      ·
        refine ⟨46399927596592532371485281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30933285064395021580990187 46399927596592532371485281)
        ·
          refine ⟨34799945697444399278613961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46399927596592532371485281 34799945697444399278613961)
          ·
            refine ⟨26099959273083299458960471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34799945697444399278613961 26099959273083299458960471)
            ·
              refine ⟨39149938909624949188440707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26099959273083299458960471 39149938909624949188440707)
              ·
                refine ⟨58724908364437423782661061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39149938909624949188440707 58724908364437423782661061)
                ·
                  refine ⟨11010920318332016959248949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 58724908364437423782661061 11010920318332016959248949)
                  ·
                    refine ⟨1032273779843626589929589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11010920318332016959248949 1032273779843626589929589)
                    ·
                      rfl

theorem cell23_6031038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 1, 4, 5].length) (baseStart_6031038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6031038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6031038 prefixEnd_6031038 := by exact prefixLift 6031038
  have htrace : WordTrace (prefixWord ++ tailWord_6031038) baseStart_6031038 baseEnd_6031038 := by
    simpa [prefixWord, tailWord_6031038, baseEnd_6031038] using wordTrace_append hprefix tailTrace_6031038
  have hstable : (prefixWord ++ tailWord_6031038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6031038).length < 2 ^ (prefixWord ++ tailWord_6031038).sum := by decide
  have hdescent : baseEnd_6031038 < baseStart_6031038 := by decide
  rcases family_descends (prefixWord ++ tailWord_6031038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6031053 : List Nat := [1, 6, 2, 1, 1, 3, 2, 1, 2, 2, 2]
def baseStart_6031053 : Nat := 118140960795 + 6031053 * 2 ^ 59
def prefixEnd_6031053 : Nat := 4983230072969 + 3 ^ 40 * 6031053 * 2
def baseEnd_6031053 : Nat := 3096829041740697211101199

theorem tailTrace_6031053 : CollatzResearch.WordTrace tailWord_6031053 prefixEnd_6031053 3096829041740697211101199 := by
  unfold tailWord_6031053
  simp only [CollatzResearch.WordTrace]
  refine ⟨219970574219532477693281813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146647049479688318462187875 219970574219532477693281813)
  ·
    refine ⟨10311120666540584891872585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 219970574219532477693281813 10311120666540584891872585)
    ·
      refine ⟨7733340499905438668904439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10311120666540584891872585 7733340499905438668904439)
      ·
        refine ⟨11600010749858158003356659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7733340499905438668904439 11600010749858158003356659)
        ·
          refine ⟨17400016124787237005034989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11600010749858158003356659 17400016124787237005034989)
          ·
            refine ⟨6525006046795213876888121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17400016124787237005034989 6525006046795213876888121)
            ·
              refine ⟨4893754535096410407666091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6525006046795213876888121 4893754535096410407666091)
              ·
                refine ⟨7340631802644615611499137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4893754535096410407666091 7340631802644615611499137)
                ·
                  refine ⟨5505473851983461708624353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7340631802644615611499137 5505473851983461708624353)
                  ·
                    refine ⟨4129105388987596281468265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5505473851983461708624353 4129105388987596281468265)
                    ·
                      refine ⟨3096829041740697211101199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4129105388987596281468265 3096829041740697211101199)
                      ·
                        rfl

theorem cell23_6031053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 2, 1, 2, 2, 2].length) (baseStart_6031053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6031053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6031053 prefixEnd_6031053 := by exact prefixLift 6031053
  have htrace : WordTrace (prefixWord ++ tailWord_6031053) baseStart_6031053 baseEnd_6031053 := by
    simpa [prefixWord, tailWord_6031053, baseEnd_6031053] using wordTrace_append hprefix tailTrace_6031053
  have hstable : (prefixWord ++ tailWord_6031053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6031053).length < 2 ^ (prefixWord ++ tailWord_6031053).sum := by decide
  have hdescent : baseEnd_6031053 < baseStart_6031053 := by decide
  rcases family_descends (prefixWord ++ tailWord_6031053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6031121 : List Nat := [1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 7]
def baseStart_6031121 : Nat := 118140960795 + 6031121 * 2 ^ 59
def prefixEnd_6031121 : Nat := 4983230072969 + 3 ^ 40 * 6031121 * 2
def baseEnd_6031121 : Nat := 3096863958425202945050885

theorem tailTrace_6031121 : CollatzResearch.WordTrace tailWord_6031121 prefixEnd_6031121 3096863958425202945050885 := by
  unfold tailWord_6031121
  simp only [CollatzResearch.WordTrace]
  refine ⟨219973054383286125306757217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146648702922190750204504811 219973054383286125306757217)
  ·
    refine ⟨164979790787464593980067913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219973054383286125306757217 164979790787464593980067913)
    ·
      refine ⟨123734843090598445485050935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164979790787464593980067913 123734843090598445485050935)
      ·
        refine ⟨185602264635897668227576403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123734843090598445485050935 185602264635897668227576403)
        ·
          refine ⟨278403396953846502341364605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185602264635897668227576403 278403396953846502341364605)
          ·
            refine ⟨104401273857692438378011727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 278403396953846502341364605 104401273857692438378011727)
            ·
              refine ⟨156601910786538657567017591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104401273857692438378011727 156601910786538657567017591)
              ·
                refine ⟨234902866179807986350526387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 156601910786538657567017591 234902866179807986350526387)
                ·
                  refine ⟨352354299269711979525789581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 234902866179807986350526387 352354299269711979525789581)
                  ·
                    refine ⟨132132862226141992322171093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 352354299269711979525789581 132132862226141992322171093)
                    ·
                      refine ⟨3096863958425202945050885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 132132862226141992322171093 3096863958425202945050885)
                      ·
                        rfl

theorem cell23_6031121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 7].length) (baseStart_6031121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6031121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6031121 prefixEnd_6031121 := by exact prefixLift 6031121
  have htrace : WordTrace (prefixWord ++ tailWord_6031121) baseStart_6031121 baseEnd_6031121 := by
    simpa [prefixWord, tailWord_6031121, baseEnd_6031121] using wordTrace_append hprefix tailTrace_6031121
  have hstable : (prefixWord ++ tailWord_6031121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6031121).length < 2 ^ (prefixWord ++ tailWord_6031121).sum := by decide
  have hdescent : baseEnd_6031121 < baseStart_6031121 := by decide
  rcases family_descends (prefixWord ++ tailWord_6031121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6031125 : List Nat := [1, 3, 2, 1, 2, 3, 1, 1, 5, 1, 3]
def baseStart_6031125 : Nat := 118140960795 + 6031125 * 2 ^ 59
def prefixEnd_6031125 : Nat := 4983230072969 + 3 ^ 40 * 6031125 * 2
def baseEnd_6031125 : Nat := 3096866012347820929400867

theorem tailTrace_6031125 : CollatzResearch.WordTrace tailWord_6031125 prefixEnd_6031125 3096866012347820929400867 := by
  unfold tailWord_6031125
  simp only [CollatzResearch.WordTrace]
  refine ⟨219973200275271633989902829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146648800183514422659935219 219973200275271633989902829)
  ·
    refine ⟨82489950103226862746213561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 219973200275271633989902829 82489950103226862746213561)
    ·
      refine ⟨61867462577420147059660171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82489950103226862746213561 61867462577420147059660171)
      ·
        refine ⟨92801193866130220589490257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61867462577420147059660171 92801193866130220589490257)
        ·
          refine ⟨69600895399597665442117693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92801193866130220589490257 69600895399597665442117693)
          ·
            refine ⟨26100335774849124540794135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69600895399597665442117693 26100335774849124540794135)
            ·
              refine ⟨39150503662273686811191203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26100335774849124540794135 39150503662273686811191203)
              ·
                refine ⟨58725755493410530216786805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39150503662273686811191203 58725755493410530216786805)
                ·
                  refine ⟨5505539577507237207823763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 58725755493410530216786805 5505539577507237207823763)
                  ·
                    refine ⟨8258309366260855811735645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5505539577507237207823763 8258309366260855811735645)
                    ·
                      refine ⟨3096866012347820929400867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8258309366260855811735645 3096866012347820929400867)
                      ·
                        rfl

theorem cell23_6031125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 1, 5, 1, 3].length) (baseStart_6031125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6031125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6031125 prefixEnd_6031125 := by exact prefixLift 6031125
  have htrace : WordTrace (prefixWord ++ tailWord_6031125) baseStart_6031125 baseEnd_6031125 := by
    simpa [prefixWord, tailWord_6031125, baseEnd_6031125] using wordTrace_append hprefix tailTrace_6031125
  have hstable : (prefixWord ++ tailWord_6031125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6031125).length < 2 ^ (prefixWord ++ tailWord_6031125).sum := by decide
  have hdescent : baseEnd_6031125 < baseStart_6031125 := by decide
  rcases family_descends (prefixWord ++ tailWord_6031125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6031128 : List Nat := [2, 1, 2, 3, 1, 1, 4, 1, 3, 5]
def baseStart_6031128 : Nat := 118140960795 + 6031128 * 2 ^ 59
def prefixEnd_6031128 : Nat := 4983230072969 + 3 ^ 40 * 6031128 * 2
def baseEnd_6031128 : Nat := 1032289184263261472554451

theorem tailTrace_6031128 : CollatzResearch.WordTrace tailWord_6031128 prefixEnd_6031128 1032289184263261472554451 := by
  unfold tailWord_6031128
  simp only [CollatzResearch.WordTrace]
  refine ⟨109986654847130382751131019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146648873129507177001508025 109986654847130382751131019)
  ·
    refine ⟨164979982270695574126696529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109986654847130382751131019 164979982270695574126696529)
    ·
      refine ⟨123734986703021680595022397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164979982270695574126696529 123734986703021680595022397)
      ·
        refine ⟨46400620013633130223133399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123734986703021680595022397 46400620013633130223133399)
        ·
          refine ⟨69600930020449695334700099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46400620013633130223133399 69600930020449695334700099)
          ·
            refine ⟨104401395030674543002050149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69600930020449695334700099 104401395030674543002050149)
            ·
              refine ⟨19575261568251476812884403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 104401395030674543002050149 19575261568251476812884403)
              ·
                refine ⟨29362892352377215219326605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19575261568251476812884403 29362892352377215219326605)
                ·
                  refine ⟨11011084632141455707247477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29362892352377215219326605 11011084632141455707247477)
                  ·
                    refine ⟨1032289184263261472554451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11011084632141455707247477 1032289184263261472554451)
                    ·
                      rfl

theorem cell23_6031128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4, 1, 3, 5].length) (baseStart_6031128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6031128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6031128 prefixEnd_6031128 := by exact prefixLift 6031128
  have htrace : WordTrace (prefixWord ++ tailWord_6031128) baseStart_6031128 baseEnd_6031128 := by
    simpa [prefixWord, tailWord_6031128, baseEnd_6031128] using wordTrace_append hprefix tailTrace_6031128
  have hstable : (prefixWord ++ tailWord_6031128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6031128).length < 2 ^ (prefixWord ++ tailWord_6031128).sum := by decide
  have hdescent : baseEnd_6031128 < baseStart_6031128 := by decide
  rcases family_descends (prefixWord ++ tailWord_6031128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6031135 : List Nat := [1, 1, 2, 4, 2, 1, 3, 1, 1, 5, 2]
def baseStart_6031135 : Nat := 118140960795 + 6031135 * 2 ^ 59
def prefixEnd_6031135 : Nat := 4983230072969 + 3 ^ 40 * 6031135 * 2
def baseEnd_6031135 : Nat := 3096871147154365890275821

theorem tailTrace_6031135 : CollatzResearch.WordTrace tailWord_6031135 prefixEnd_6031135 3096871147154365890275821 := by
  unfold tailWord_6031135
  simp only [CollatzResearch.WordTrace]
  refine ⟨219973565005235405697766859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146649043336823603798511239 219973565005235405697766859)
  ·
    refine ⟨329960347507853108546650289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219973565005235405697766859 329960347507853108546650289)
    ·
      refine ⟨247470260630889831409987717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 329960347507853108546650289 247470260630889831409987717)
      ·
        refine ⟨46400673868291843389372697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 247470260630889831409987717 46400673868291843389372697)
        ·
          refine ⟨34800505401218882542029523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46400673868291843389372697 34800505401218882542029523)
          ·
            refine ⟨52200758101828323813044285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34800505401218882542029523 52200758101828323813044285)
            ·
              refine ⟨19575284288185621429891607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52200758101828323813044285 19575284288185621429891607)
              ·
                refine ⟨29362926432278432144837411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19575284288185621429891607 29362926432278432144837411)
                ·
                  refine ⟨44044389648417648217256117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29362926432278432144837411 44044389648417648217256117)
                  ·
                    refine ⟨4129161529539154520367761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 44044389648417648217256117 4129161529539154520367761)
                    ·
                      refine ⟨3096871147154365890275821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4129161529539154520367761 3096871147154365890275821)
                      ·
                        rfl

theorem cell23_6031135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 3, 1, 1, 5, 2].length) (baseStart_6031135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6031135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6031135 prefixEnd_6031135 := by exact prefixLift 6031135
  have htrace : WordTrace (prefixWord ++ tailWord_6031135) baseStart_6031135 baseEnd_6031135 := by
    simpa [prefixWord, tailWord_6031135, baseEnd_6031135] using wordTrace_append hprefix tailTrace_6031135
  have hstable : (prefixWord ++ tailWord_6031135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6031135).length < 2 ^ (prefixWord ++ tailWord_6031135).sum := by decide
  have hdescent : baseEnd_6031135 < baseStart_6031135 := by decide
  rcases family_descends (prefixWord ++ tailWord_6031135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6031175 : List Nat := [1, 1, 4, 1, 2, 1, 2, 5, 2, 4]
def baseStart_6031175 : Nat := 118140960795 + 6031175 * 2 ^ 59
def prefixEnd_6031175 : Nat := 4983230072969 + 3 ^ 40 * 6031175 * 2
def baseEnd_6031175 : Nat := 1032297228793515244591879

theorem tailTrace_6031175 : CollatzResearch.WordTrace tailWord_6031175 prefixEnd_6031175 1032297228793515244591879 := by
  unfold tailWord_6031175
  simp only [CollatzResearch.WordTrace]
  refine ⟨219975023925090492529222979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146650015950060328352815319 219975023925090492529222979)
  ·
    refine ⟨329962535887635738793834469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219975023925090492529222979 329962535887635738793834469)
    ·
      refine ⟨61867975478931701023843963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 329962535887635738793834469 61867975478931701023843963)
      ·
        refine ⟨92801963218397551535765945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61867975478931701023843963 92801963218397551535765945)
        ·
          refine ⟨69601472413798163651824459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92801963218397551535765945 69601472413798163651824459)
          ·
            refine ⟨104402208620697245477736689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69601472413798163651824459 104402208620697245477736689)
            ·
              refine ⟨78301656465522934108302517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104402208620697245477736689 78301656465522934108302517)
              ·
                refine ⟨7340780293642775072653361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 78301656465522934108302517 7340780293642775072653361)
                ·
                  refine ⟨5505585220232081304490021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7340780293642775072653361 5505585220232081304490021)
                  ·
                    refine ⟨1032297228793515244591879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5505585220232081304490021 1032297228793515244591879)
                    ·
                      rfl

theorem cell23_6031175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 5, 2, 4].length) (baseStart_6031175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6031175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6031175 prefixEnd_6031175 := by exact prefixLift 6031175
  have htrace : WordTrace (prefixWord ++ tailWord_6031175) baseStart_6031175 baseEnd_6031175 := by
    simpa [prefixWord, tailWord_6031175, baseEnd_6031175] using wordTrace_append hprefix tailTrace_6031175
  have hstable : (prefixWord ++ tailWord_6031175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6031175).length < 2 ^ (prefixWord ++ tailWord_6031175).sum := by decide
  have hdescent : baseEnd_6031175 < baseStart_6031175 := by decide
  rcases family_descends (prefixWord ++ tailWord_6031175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6031178 : List Nat := [3, 1, 2, 1, 1, 1, 5, 1, 1, 1, 6]
def baseStart_6031178 : Nat := 118140960795 + 6031178 * 2 ^ 59
def prefixEnd_6031178 : Nat := 4983230072969 + 3 ^ 40 * 6031178 * 2
def baseEnd_6031178 : Nat := 3096893226822509222038123

theorem tailTrace_6031178 : CollatzResearch.WordTrace tailWord_6031178 prefixEnd_6031178 3096893226822509222038123 := by
  unfold tailWord_6031178
  simp only [CollatzResearch.WordTrace]
  refine ⟨54993783336019906010395547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146650088896053082694388125 54993783336019906010395547)
  ·
    refine ⟨82490675004029859015593321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54993783336019906010395547 82490675004029859015593321)
    ·
      refine ⟨61868006253022394261694991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82490675004029859015593321 61868006253022394261694991)
      ·
        refine ⟨92802009379533591392542487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61868006253022394261694991 92802009379533591392542487)
        ·
          refine ⟨139203014069300387088813731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92802009379533591392542487 139203014069300387088813731)
          ·
            refine ⟨208804521103950580633220597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139203014069300387088813731 208804521103950580633220597)
            ·
              refine ⟨19575423853495366934364431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 208804521103950580633220597 19575423853495366934364431)
              ·
                refine ⟨29363135780243050401546647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19575423853495366934364431 29363135780243050401546647)
                ·
                  refine ⟨44044703670364575602319971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29363135780243050401546647 44044703670364575602319971)
                  ·
                    refine ⟨66067055505546863403479957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 44044703670364575602319971 66067055505546863403479957)
                    ·
                      refine ⟨3096893226822509222038123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 66067055505546863403479957 3096893226822509222038123)
                      ·
                        rfl

theorem cell23_6031178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5, 1, 1, 1, 6].length) (baseStart_6031178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6031178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6031178 prefixEnd_6031178 := by exact prefixLift 6031178
  have htrace : WordTrace (prefixWord ++ tailWord_6031178) baseStart_6031178 baseEnd_6031178 := by
    simpa [prefixWord, tailWord_6031178, baseEnd_6031178] using wordTrace_append hprefix tailTrace_6031178
  have hstable : (prefixWord ++ tailWord_6031178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6031178).length < 2 ^ (prefixWord ++ tailWord_6031178).sum := by decide
  have hdescent : baseEnd_6031178 < baseStart_6031178 := by decide
  rcases family_descends (prefixWord ++ tailWord_6031178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6031202 : List Nat := [3, 3, 2, 1, 2, 2, 2, 1, 1, 1, 5]
def baseStart_6031202 : Nat := 118140960795 + 6031202 * 2 ^ 59
def prefixEnd_6031202 : Nat := 4983230072969 + 3 ^ 40 * 6031202 * 2
def baseEnd_6031202 : Nat := 3096905550358217128138013

theorem tailTrace_6031202 : CollatzResearch.WordTrace tailWord_6031202 prefixEnd_6031202 3096905550358217128138013 := by
  unfold tailWord_6031202
  simp only [CollatzResearch.WordTrace]
  refine ⟨54994002173998169035113965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146650672463995117426970573 54994002173998169035113965)
  ·
    refine ⟨20622750815249313388167737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54994002173998169035113965 20622750815249313388167737)
    ·
      refine ⟨15467063111436985041125803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20622750815249313388167737 15467063111436985041125803)
      ·
        refine ⟨23200594667155477561688705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15467063111436985041125803 23200594667155477561688705)
        ·
          refine ⟨17400446000366608171266529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23200594667155477561688705 17400446000366608171266529)
          ·
            refine ⟨13050334500274956128449897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17400446000366608171266529 13050334500274956128449897)
            ·
              refine ⟨9787750875206217096337423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13050334500274956128449897 9787750875206217096337423)
              ·
                refine ⟨14681626312809325644506135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9787750875206217096337423 14681626312809325644506135)
                ·
                  refine ⟨22022439469213988466759203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14681626312809325644506135 22022439469213988466759203)
                  ·
                    refine ⟨33033659203820982700138805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22022439469213988466759203 33033659203820982700138805)
                    ·
                      refine ⟨3096905550358217128138013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33033659203820982700138805 3096905550358217128138013)
                      ·
                        rfl

theorem cell23_6031202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 2, 1, 1, 1, 5].length) (baseStart_6031202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6031202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6031202 prefixEnd_6031202 := by exact prefixLift 6031202
  have htrace : WordTrace (prefixWord ++ tailWord_6031202) baseStart_6031202 baseEnd_6031202 := by
    simpa [prefixWord, tailWord_6031202, baseEnd_6031202] using wordTrace_append hprefix tailTrace_6031202
  have hstable : (prefixWord ++ tailWord_6031202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6031202).length < 2 ^ (prefixWord ++ tailWord_6031202).sum := by decide
  have hdescent : baseEnd_6031202 < baseStart_6031202 := by decide
  rcases family_descends (prefixWord ++ tailWord_6031202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6031218 : List Nat := [3, 2, 1, 2, 1, 1, 1, 3, 2, 7]
def baseStart_6031218 : Nat := 118140960795 + 6031218 * 2 ^ 59
def prefixEnd_6031218 : Nat := 4983230072969 + 3 ^ 40 * 6031218 * 2
def baseEnd_6031218 : Nat := 1032304588682896355179313

theorem tailTrace_6031218 : CollatzResearch.WordTrace tailWord_6031218 prefixEnd_6031218 1032304588682896355179313 := by
  unfold tailWord_6031218
  simp only [CollatzResearch.WordTrace]
  refine ⟨54994148065983677718259577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146651061509289807248692205 54994148065983677718259577)
  ·
    refine ⟨41245611049487758288694683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54994148065983677718259577 41245611049487758288694683)
    ·
      refine ⟨61868416574231637433042025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41245611049487758288694683 61868416574231637433042025)
      ·
        refine ⟨46401312430673728074781519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61868416574231637433042025 46401312430673728074781519)
        ·
          refine ⟨69601968646010592112172279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46401312430673728074781519 69601968646010592112172279)
          ·
            refine ⟨104402952969015888168258419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69601968646010592112172279 104402952969015888168258419)
            ·
              refine ⟨156604429453523832252387629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104402952969015888168258419 156604429453523832252387629)
              ·
                refine ⟨58726661045071437094645361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 156604429453523832252387629 58726661045071437094645361)
                ·
                  refine ⟨44044995783803577820984021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58726661045071437094645361 44044995783803577820984021)
                  ·
                    refine ⟨1032304588682896355179313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44044995783803577820984021 1032304588682896355179313)
                    ·
                      rfl

theorem cell23_6031218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 3, 2, 7].length) (baseStart_6031218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6031218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6031218 prefixEnd_6031218 := by exact prefixLift 6031218
  have htrace : WordTrace (prefixWord ++ tailWord_6031218) baseStart_6031218 baseEnd_6031218 := by
    simpa [prefixWord, tailWord_6031218, baseEnd_6031218] using wordTrace_append hprefix tailTrace_6031218
  have hstable : (prefixWord ++ tailWord_6031218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6031218).length < 2 ^ (prefixWord ++ tailWord_6031218).sum := by decide
  have hdescent : baseEnd_6031218 < baseStart_6031218 := by decide
  rcases family_descends (prefixWord ++ tailWord_6031218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6031222 : List Nat := [5, 1, 1, 3, 2, 1, 2, 8]
def baseStart_6031222 : Nat := 118140960795 + 6031222 * 2 ^ 59
def prefixEnd_6031222 : Nat := 4983230072969 + 3 ^ 40 * 6031222 * 2
def baseEnd_6031222 : Nat := 114700585924863224069923

theorem tailTrace_6031222 : CollatzResearch.WordTrace tailWord_6031222 prefixEnd_6031222 114700585924863224069923 := by
  unfold tailWord_6031222
  simp only [CollatzResearch.WordTrace]
  refine ⟨13748546134745013722261495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 146651158770613479704122613 13748546134745013722261495)
  ·
    refine ⟨20622819202117520583392243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13748546134745013722261495 20622819202117520583392243)
    ·
      refine ⟨30934228803176280875088365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20622819202117520583392243 30934228803176280875088365)
      ·
        refine ⟨11600335801191105328158137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30934228803176280875088365 11600335801191105328158137)
        ·
          refine ⟨8700251850893328996118603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11600335801191105328158137 8700251850893328996118603)
          ·
            refine ⟨13050377776339993494177905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8700251850893328996118603 13050377776339993494177905)
            ·
              refine ⟨9787783332254995120633429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13050377776339993494177905 9787783332254995120633429)
              ·
                refine ⟨114700585924863224069923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9787783332254995120633429 114700585924863224069923)
                ·
                  rfl

theorem cell23_6031222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 2, 8].length) (baseStart_6031222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6031222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6031222 prefixEnd_6031222 := by exact prefixLift 6031222
  have htrace : WordTrace (prefixWord ++ tailWord_6031222) baseStart_6031222 baseEnd_6031222 := by
    simpa [prefixWord, tailWord_6031222, baseEnd_6031222] using wordTrace_append hprefix tailTrace_6031222
  have hstable : (prefixWord ++ tailWord_6031222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6031222).length < 2 ^ (prefixWord ++ tailWord_6031222).sum := by decide
  have hdescent : baseEnd_6031222 < baseStart_6031222 := by decide
  rcases family_descends (prefixWord ++ tailWord_6031222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6031232 : List Nat := [2, 1, 1, 2, 1, 2, 5, 3, 2, 1, 3]
def baseStart_6031232 : Nat := 118140960795 + 6031232 * 2 ^ 59
def prefixEnd_6031232 : Nat := 4983230072969 + 3 ^ 40 * 6031232 * 2
def baseEnd_6031232 : Nat := 3096920954777852010762875

theorem tailTrace_6031232 : CollatzResearch.WordTrace tailWord_6031232 prefixEnd_6031232 3096920954777852010762875 := by
  unfold tailWord_6031232
  simp only [CollatzResearch.WordTrace]
  refine ⟨109988551442941995632023975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146651401923922660842698633 109988551442941995632023975)
  ·
    refine ⟨164982827164412993448035963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109988551442941995632023975 164982827164412993448035963)
    ·
      refine ⟨247474240746619490172053945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164982827164412993448035963 247474240746619490172053945)
      ·
        refine ⟨185605680559964617629040459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 247474240746619490172053945 185605680559964617629040459)
        ·
          refine ⟨278408520839946926443560689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185605680559964617629040459 278408520839946926443560689)
          ·
            refine ⟨208806390629960194832670517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 278408520839946926443560689 208806390629960194832670517)
            ·
              refine ⟨19575599121558768265562861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 208806390629960194832670517 19575599121558768265562861)
              ·
                refine ⟨7340849670584538099586073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19575599121558768265562861 7340849670584538099586073)
                ·
                  refine ⟨5505637252938403574689555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7340849670584538099586073 5505637252938403574689555)
                  ·
                    refine ⟨8258455879407605362034333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5505637252938403574689555 8258455879407605362034333)
                    ·
                      refine ⟨3096920954777852010762875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8258455879407605362034333 3096920954777852010762875)
                      ·
                        rfl

theorem cell23_6031232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5, 3, 2, 1, 3].length) (baseStart_6031232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6031232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6031232 prefixEnd_6031232 := by exact prefixLift 6031232
  have htrace : WordTrace (prefixWord ++ tailWord_6031232) baseStart_6031232 baseEnd_6031232 := by
    simpa [prefixWord, tailWord_6031232, baseEnd_6031232] using wordTrace_append hprefix tailTrace_6031232
  have hstable : (prefixWord ++ tailWord_6031232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6031232).length < 2 ^ (prefixWord ++ tailWord_6031232).sum := by decide
  have hdescent : baseEnd_6031232 < baseStart_6031232 := by decide
  rcases family_descends (prefixWord ++ tailWord_6031232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6031266 : List Nat := [3, 3, 1, 2, 3, 1, 2, 2, 2, 1, 3]
def baseStart_6031266 : Nat := 118140960795 + 6031266 * 2 ^ 59
def prefixEnd_6031266 : Nat := 4983230072969 + 3 ^ 40 * 6031266 * 2
def baseEnd_6031266 : Nat := 3096938413120104877737719

theorem tailTrace_6031266 : CollatzResearch.WordTrace tailWord_6031266 prefixEnd_6031266 3096938413120104877737719 := by
  unfold tailWord_6031266
  simp only [CollatzResearch.WordTrace]
  refine ⟨54994585741940203767696413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146652228645173876713857101 54994585741940203767696413)
  ·
    refine ⟨20622969653227576412886155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54994585741940203767696413 20622969653227576412886155)
    ·
      refine ⟨30934454479841364619329233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20622969653227576412886155 30934454479841364619329233)
      ·
        refine ⟨23200840859881023464496925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30934454479841364619329233 23200840859881023464496925)
        ·
          refine ⟨8700315322455383799186347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23200840859881023464496925 8700315322455383799186347)
          ·
            refine ⟨13050472983683075698779521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8700315322455383799186347 13050472983683075698779521)
            ·
              refine ⟨9787854737762306774084641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13050472983683075698779521 9787854737762306774084641)
              ·
                refine ⟨7340891053321730080563481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9787854737762306774084641 7340891053321730080563481)
                ·
                  refine ⟨5505668289991297560422611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7340891053321730080563481 5505668289991297560422611)
                  ·
                    refine ⟨8258502434986946340633917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5505668289991297560422611 8258502434986946340633917)
                    ·
                      refine ⟨3096938413120104877737719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8258502434986946340633917 3096938413120104877737719)
                      ·
                        rfl

theorem cell23_6031266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 2, 2, 2, 1, 3].length) (baseStart_6031266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6031266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6031266 prefixEnd_6031266 := by exact prefixLift 6031266
  have htrace : WordTrace (prefixWord ++ tailWord_6031266) baseStart_6031266 baseEnd_6031266 := by
    simpa [prefixWord, tailWord_6031266, baseEnd_6031266] using wordTrace_append hprefix tailTrace_6031266
  have hstable : (prefixWord ++ tailWord_6031266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6031266).length < 2 ^ (prefixWord ++ tailWord_6031266).sum := by decide
  have hdescent : baseEnd_6031266 < baseStart_6031266 := by decide
  rcases family_descends (prefixWord ++ tailWord_6031266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6031285 : List Nat := [1, 3, 3, 2, 1, 2, 1, 1, 1, 4, 4]
def baseStart_6031285 : Nat := 118140960795 + 6031285 * 2 ^ 59
def prefixEnd_6031285 : Nat := 4983230072969 + 3 ^ 40 * 6031285 * 2
def baseEnd_6031285 : Nat := 3096948169252540303400131

theorem tailTrace_6031285 : CollatzResearch.WordTrace tailWord_6031285 prefixEnd_6031285 3096948169252540303400131 := by
  unfold tailWord_6031285
  simp only [CollatzResearch.WordTrace]
  refine ⟨219979035954691981315727309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146652690636461320877151539 219979035954691981315727309)
  ·
    refine ⟨82492138483009492993397741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 219979035954691981315727309 82492138483009492993397741)
    ·
      refine ⟨30934551931128559872524153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82492138483009492993397741 30934551931128559872524153)
      ·
        refine ⟨23200913948346419904393115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30934551931128559872524153 23200913948346419904393115)
        ·
          refine ⟨34801370922519629856589673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23200913948346419904393115 34801370922519629856589673)
          ·
            refine ⟨26101028191889722392442255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34801370922519629856589673 26101028191889722392442255)
            ·
              refine ⟨39151542287834583588663383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26101028191889722392442255 39151542287834583588663383)
              ·
                refine ⟨58727313431751875382995075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39151542287834583588663383 58727313431751875382995075)
                ·
                  refine ⟨88090970147627813074492613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58727313431751875382995075 88090970147627813074492613)
                  ·
                    refine ⟨16517056902680214951467365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 88090970147627813074492613 16517056902680214951467365)
                    ·
                      refine ⟨3096948169252540303400131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16517056902680214951467365 3096948169252540303400131)
                      ·
                        rfl

theorem cell23_6031285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 1, 1, 4, 4].length) (baseStart_6031285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6031285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6031285 prefixEnd_6031285 := by exact prefixLift 6031285
  have htrace : WordTrace (prefixWord ++ tailWord_6031285) baseStart_6031285 baseEnd_6031285 := by
    simpa [prefixWord, tailWord_6031285, baseEnd_6031285] using wordTrace_append hprefix tailTrace_6031285
  have hstable : (prefixWord ++ tailWord_6031285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6031285).length < 2 ^ (prefixWord ++ tailWord_6031285).sum := by decide
  have hdescent : baseEnd_6031285 < baseStart_6031285 := by decide
  rcases family_descends (prefixWord ++ tailWord_6031285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6031289 : List Nat := [1, 2, 1, 4, 2, 1, 1, 5, 2, 2, 2]
def baseStart_6031289 : Nat := 118140960795 + 6031289 * 2 ^ 59
def prefixEnd_6031289 : Nat := 4983230072969 + 3 ^ 40 * 6031289 * 2
def baseEnd_6031289 : Nat := 3096950223175158287750113

theorem tailTrace_6031289 : CollatzResearch.WordTrace tailWord_6031289 prefixEnd_6031289 3096950223175158287750113 := by
  unfold tailWord_6031289
  simp only [CollatzResearch.WordTrace]
  refine ⟨219979181846677489998872921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146652787897784993332581947 219979181846677489998872921)
  ·
    refine ⟨164984386385008117499154691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219979181846677489998872921 164984386385008117499154691)
    ·
      refine ⟨247476579577512176248732037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164984386385008117499154691 247476579577512176248732037)
      ·
        refine ⟨46401858670783533046637257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 247476579577512176248732037 46401858670783533046637257)
        ·
          refine ⟨34801394003087649784977943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46401858670783533046637257 34801394003087649784977943)
          ·
            refine ⟨52202091004631474677466915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34801394003087649784977943 52202091004631474677466915)
            ·
              refine ⟨78303136506947212016200373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52202091004631474677466915 78303136506947212016200373)
              ·
                refine ⟨7340919047526301126518785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 78303136506947212016200373 7340919047526301126518785)
                ·
                  refine ⟨5505689285644725844889089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7340919047526301126518785 5505689285644725844889089)
                  ·
                    refine ⟨4129266964233544383666817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5505689285644725844889089 4129266964233544383666817)
                    ·
                      refine ⟨3096950223175158287750113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4129266964233544383666817 3096950223175158287750113)
                      ·
                        rfl

theorem cell23_6031289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 5, 2, 2, 2].length) (baseStart_6031289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6031289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6031289 prefixEnd_6031289 := by exact prefixLift 6031289
  have htrace : WordTrace (prefixWord ++ tailWord_6031289) baseStart_6031289 baseEnd_6031289 := by
    simpa [prefixWord, tailWord_6031289, baseEnd_6031289] using wordTrace_append hprefix tailTrace_6031289
  have hstable : (prefixWord ++ tailWord_6031289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6031289).length < 2 ^ (prefixWord ++ tailWord_6031289).sum := by decide
  have hdescent : baseEnd_6031289 < baseStart_6031289 := by decide
  rcases family_descends (prefixWord ++ tailWord_6031289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6031385 : List Nat := [1, 2, 1, 2, 1, 1, 3, 6, 6]
def baseStart_6031385 : Nat := 118140960795 + 6031385 * 2 ^ 59
def prefixEnd_6031385 : Nat := 4983230072969 + 3 ^ 40 * 6031385 * 2
def baseEnd_6031385 : Nat := 344111057479776656905519

theorem tailTrace_6031385 : CollatzResearch.WordTrace tailWord_6031385 prefixEnd_6031385 344111057479776656905519 := by
  unfold tailWord_6031385
  simp only [CollatzResearch.WordTrace]
  refine ⟨219982683254329698394367609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146655122169553132262911739 219982683254329698394367609)
  ·
    refine ⟨164987012440747273795775707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219982683254329698394367609 164987012440747273795775707)
    ·
      refine ⟨247480518661120910693663561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164987012440747273795775707 247480518661120910693663561)
      ·
        refine ⟨185610388995840683020247671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 247480518661120910693663561 185610388995840683020247671)
        ·
          refine ⟨278415583493761024530371507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185610388995840683020247671 278415583493761024530371507)
          ·
            refine ⟨417623375240641536795557261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 278415583493761024530371507 417623375240641536795557261)
            ·
              refine ⟨156608765715240576298333973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 417623375240641536795557261 156608765715240576298333973)
              ·
                refine ⟨7341035892901902013984405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 156608765715240576298333973 7341035892901902013984405)
                ·
                  refine ⟨344111057479776656905519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7341035892901902013984405 344111057479776656905519)
                  ·
                    rfl

theorem cell23_6031385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 6, 6].length) (baseStart_6031385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6031385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6031385 prefixEnd_6031385 := by exact prefixLift 6031385
  have htrace : WordTrace (prefixWord ++ tailWord_6031385) baseStart_6031385 baseEnd_6031385 := by
    simpa [prefixWord, tailWord_6031385, baseEnd_6031385] using wordTrace_append hprefix tailTrace_6031385
  have hstable : (prefixWord ++ tailWord_6031385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6031385).length < 2 ^ (prefixWord ++ tailWord_6031385).sum := by decide
  have hdescent : baseEnd_6031385 < baseStart_6031385 := by decide
  rcases family_descends (prefixWord ++ tailWord_6031385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6031389 : List Nat := [1, 4, 2, 2, 2, 1, 3, 1, 3, 4]
def baseStart_6031389 : Nat := 118140960795 + 6031389 * 2 ^ 59
def prefixEnd_6031389 : Nat := 4983230072969 + 3 ^ 40 * 6031389 * 2
def baseEnd_6031389 : Nat := 1032333857080202632166551

theorem tailTrace_6031389 : CollatzResearch.WordTrace tailWord_6031389 prefixEnd_6031389 1032333857080202632166551 := by
  unfold tailWord_6031389
  simp only [CollatzResearch.WordTrace]
  refine ⟨219982829146315207077513221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146655219430876804718342147 219982829146315207077513221)
  ·
    refine ⟨41246780464934101327033729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 219982829146315207077513221 41246780464934101327033729)
    ·
      refine ⟨30935085348700575995275297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41246780464934101327033729 30935085348700575995275297)
      ·
        refine ⟨23201314011525431996456473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30935085348700575995275297 23201314011525431996456473)
        ·
          refine ⟨17400985508644073997342355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23201314011525431996456473 17400985508644073997342355)
          ·
            refine ⟨26101478262966110996013533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17400985508644073997342355 26101478262966110996013533)
            ·
              refine ⟨9788054348612291623505075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26101478262966110996013533 9788054348612291623505075)
              ·
                refine ⟨14682081522918437435257613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9788054348612291623505075 14682081522918437435257613)
                ·
                  refine ⟨5505780571094414038221605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14682081522918437435257613 5505780571094414038221605)
                  ·
                    refine ⟨1032333857080202632166551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5505780571094414038221605 1032333857080202632166551)
                    ·
                      rfl

theorem cell23_6031389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 3, 1, 3, 4].length) (baseStart_6031389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6031389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6031389 prefixEnd_6031389 := by exact prefixLift 6031389
  have htrace : WordTrace (prefixWord ++ tailWord_6031389) baseStart_6031389 baseEnd_6031389 := by
    simpa [prefixWord, tailWord_6031389, baseEnd_6031389] using wordTrace_append hprefix tailTrace_6031389
  have hstable : (prefixWord ++ tailWord_6031389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6031389).length < 2 ^ (prefixWord ++ tailWord_6031389).sum := by decide
  have hdescent : baseEnd_6031389 < baseStart_6031389 := by decide
  rcases family_descends (prefixWord ++ tailWord_6031389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6031469 : List Nat := [1, 5, 1, 1, 2, 1, 2, 4, 1, 1, 4]
def baseStart_6031469 : Nat := 118140960795 + 6031469 * 2 ^ 59
def prefixEnd_6031469 : Nat := 4983230072969 + 3 ^ 40 * 6031469 * 2
def baseEnd_6031469 : Nat := 3097042649692967583499285

theorem tailTrace_6031469 : CollatzResearch.WordTrace tailWord_6031469 prefixEnd_6031469 3097042649692967583499285 := by
  unfold tailWord_6031469
  simp only [CollatzResearch.WordTrace]
  refine ⟨219985746986025380740425461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146657164657350253826950307 219985746986025380740425461)
  ·
    refine ⟨20623663779939879444414887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 219985746986025380740425461 20623663779939879444414887)
    ·
      refine ⟨30935495669909819166622331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20623663779939879444414887 30935495669909819166622331)
      ·
        refine ⟨46403243504864728749933497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30935495669909819166622331 46403243504864728749933497)
        ·
          refine ⟨34802432628648546562450123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46403243504864728749933497 34802432628648546562450123)
          ·
            refine ⟨52203648942972819843675185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34802432628648546562450123 52203648942972819843675185)
            ·
              refine ⟨39152736707229614882756389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52203648942972819843675185 39152736707229614882756389)
              ·
                refine ⟨7341138132605552790516823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39152736707229614882756389 7341138132605552790516823)
                ·
                  refine ⟨11011707198908329185775235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7341138132605552790516823 11011707198908329185775235)
                  ·
                    refine ⟨16517560798362493778662853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11011707198908329185775235 16517560798362493778662853)
                    ·
                      refine ⟨3097042649692967583499285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16517560798362493778662853 3097042649692967583499285)
                      ·
                        rfl

theorem cell23_6031469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 4, 1, 1, 4].length) (baseStart_6031469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6031469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6031469 prefixEnd_6031469 := by exact prefixLift 6031469
  have htrace : WordTrace (prefixWord ++ tailWord_6031469) baseStart_6031469 baseEnd_6031469 := by
    simpa [prefixWord, tailWord_6031469, baseEnd_6031469] using wordTrace_append hprefix tailTrace_6031469
  have hstable : (prefixWord ++ tailWord_6031469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6031469).length < 2 ^ (prefixWord ++ tailWord_6031469).sum := by decide
  have hdescent : baseEnd_6031469 < baseStart_6031469 := by decide
  rcases family_descends (prefixWord ++ tailWord_6031469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6031496 : List Nat := [2, 1, 3, 4, 1, 1, 3, 2, 2, 4]
def baseStart_6031496 : Nat := 118140960795 + 6031496 * 2 ^ 59
def prefixEnd_6031496 : Nat := 4983230072969 + 3 ^ 40 * 6031496 * 2
def baseEnd_6031496 : Nat := 1032352171223546325953887

theorem tailTrace_6031496 : CollatzResearch.WordTrace tailWord_6031496 prefixEnd_6031496 1032352171223546325953887 := by
  unfold tailWord_6031496
  simp only [CollatzResearch.WordTrace]
  refine ⟨109993365878463782175829171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146657821171285042901105561 109993365878463782175829171)
  ·
    refine ⟨164990048817695673263743757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109993365878463782175829171 164990048817695673263743757)
    ·
      refine ⟨61871268306635877473903909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 164990048817695673263743757 61871268306635877473903909)
      ·
        refine ⟨11600862807494227026356983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61871268306635877473903909 11600862807494227026356983)
        ·
          refine ⟨17401294211241340539535475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11600862807494227026356983 17401294211241340539535475)
          ·
            refine ⟨26101941316862010809303213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17401294211241340539535475 26101941316862010809303213)
            ·
              refine ⟨9788227993823254053488705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26101941316862010809303213 9788227993823254053488705)
              ·
                refine ⟨7341170995367440540116529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9788227993823254053488705 7341170995367440540116529)
                ·
                  refine ⟨5505878246525580405087397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7341170995367440540116529 5505878246525580405087397)
                  ·
                    refine ⟨1032352171223546325953887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5505878246525580405087397 1032352171223546325953887)
                    ·
                      rfl

theorem cell23_6031496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 3, 2, 2, 4].length) (baseStart_6031496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6031496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6031496 prefixEnd_6031496 := by exact prefixLift 6031496
  have htrace : WordTrace (prefixWord ++ tailWord_6031496) baseStart_6031496 baseEnd_6031496 := by
    simpa [prefixWord, tailWord_6031496, baseEnd_6031496] using wordTrace_append hprefix tailTrace_6031496
  have hstable : (prefixWord ++ tailWord_6031496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6031496).length < 2 ^ (prefixWord ++ tailWord_6031496).sum := by decide
  have hdescent : baseEnd_6031496 < baseStart_6031496 := by decide
  rcases family_descends (prefixWord ++ tailWord_6031496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6031537 : List Nat := [1, 2, 2, 5, 2, 2, 1, 3, 1, 2, 2]
def baseStart_6031537 : Nat := 118140960795 + 6031537 * 2 ^ 59
def prefixEnd_6031537 : Nat := 4983230072969 + 3 ^ 40 * 6031537 * 2
def baseEnd_6031537 : Nat := 3097077566377473317448973

theorem tailTrace_6031537 : CollatzResearch.WordTrace tailWord_6031537 prefixEnd_6031537 3097077566377473317448973 := by
  unfold tailWord_6031537
  simp only [CollatzResearch.WordTrace]
  refine ⟨219988227149779028353900865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146658818099852685569267243 219988227149779028353900865)
  ·
    refine ⟨164991170362334271265425649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219988227149779028353900865 164991170362334271265425649)
    ·
      refine ⟨123743377771750703449069237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164991170362334271265425649 123743377771750703449069237)
      ·
        refine ⟨11600941666101628448350241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 123743377771750703449069237 11600941666101628448350241)
        ·
          refine ⟨8700706249576221336262681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11600941666101628448350241 8700706249576221336262681)
          ·
            refine ⟨6525529687182166002197011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8700706249576221336262681 6525529687182166002197011)
            ·
              refine ⟨9788294530773249003295517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6525529687182166002197011 9788294530773249003295517)
              ·
                refine ⟨3670610449039968376235819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9788294530773249003295517 3670610449039968376235819)
                ·
                  refine ⟨5505915673559952564353729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3670610449039968376235819 5505915673559952564353729)
                  ·
                    refine ⟨4129436755169964423265297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5505915673559952564353729 4129436755169964423265297)
                    ·
                      refine ⟨3097077566377473317448973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4129436755169964423265297 3097077566377473317448973)
                      ·
                        rfl

theorem cell23_6031537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 1, 3, 1, 2, 2].length) (baseStart_6031537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6031537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6031537 prefixEnd_6031537 := by exact prefixLift 6031537
  have htrace : WordTrace (prefixWord ++ tailWord_6031537) baseStart_6031537 baseEnd_6031537 := by
    simpa [prefixWord, tailWord_6031537, baseEnd_6031537] using wordTrace_append hprefix tailTrace_6031537
  have hstable : (prefixWord ++ tailWord_6031537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6031537).length < 2 ^ (prefixWord ++ tailWord_6031537).sum := by decide
  have hdescent : baseEnd_6031537 < baseStart_6031537 := by decide
  rcases family_descends (prefixWord ++ tailWord_6031537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6031540 : List Nat := [2, 5, 3, 1, 1, 1, 2, 1, 1, 1, 5]
def baseStart_6031540 : Nat := 118140960795 + 6031540 * 2 ^ 59
def prefixEnd_6031540 : Nat := 4983230072969 + 3 ^ 40 * 6031540 * 2
def baseEnd_6031540 : Nat := 3097079106819436805711459

theorem tailTrace_6031540 : CollatzResearch.WordTrace tailWord_6031540 prefixEnd_6031540 3097079106819436805711459 := by
  unfold tailWord_6031540
  simp only [CollatzResearch.WordTrace]
  refine ⟨109994168284384079933130037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146658891045845439910840049 109994168284384079933130037)
  ·
    refine ⟨10311953276661007493730941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 109994168284384079933130037 10311953276661007493730941)
    ·
      refine ⟨3866982478747877810149103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10311953276661007493730941 3866982478747877810149103)
      ·
        refine ⟨5800473718121816715223655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3866982478747877810149103 5800473718121816715223655)
        ·
          refine ⟨8700710577182725072835483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5800473718121816715223655 8700710577182725072835483)
          ·
            refine ⟨13051065865774087609253225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8700710577182725072835483 13051065865774087609253225)
            ·
              refine ⟨9788299399330565706939919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13051065865774087609253225 9788299399330565706939919)
              ·
                refine ⟨14682449098995848560409879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9788299399330565706939919 14682449098995848560409879)
                ·
                  refine ⟨22023673648493772840614819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14682449098995848560409879 22023673648493772840614819)
                  ·
                    refine ⟨33035510472740659260922229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22023673648493772840614819 33035510472740659260922229)
                    ·
                      refine ⟨3097079106819436805711459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33035510472740659260922229 3097079106819436805711459)
                      ·
                        rfl

theorem cell23_6031540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 2, 1, 1, 1, 5].length) (baseStart_6031540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6031540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6031540 prefixEnd_6031540 := by exact prefixLift 6031540
  have htrace : WordTrace (prefixWord ++ tailWord_6031540) baseStart_6031540 baseEnd_6031540 := by
    simpa [prefixWord, tailWord_6031540, baseEnd_6031540] using wordTrace_append hprefix tailTrace_6031540
  have hstable : (prefixWord ++ tailWord_6031540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6031540).length < 2 ^ (prefixWord ++ tailWord_6031540).sum := by decide
  have hdescent : baseEnd_6031540 < baseStart_6031540 := by decide
  rcases family_descends (prefixWord ++ tailWord_6031540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6031546 : List Nat := [3, 1, 1, 1, 2, 2, 4, 3, 1, 3, 2]
def baseStart_6031546 : Nat := 118140960795 + 6031546 * 2 ^ 59
def prefixEnd_6031546 : Nat := 4983230072969 + 3 ^ 40 * 6031546 * 2
def baseEnd_6031546 : Nat := 3097082187703363782236431

theorem tailTrace_6031546 : CollatzResearch.WordTrace tailWord_6031546 prefixEnd_6031546 3097082187703363782236431 := by
  unfold tailWord_6031546
  simp only [CollatzResearch.WordTrace]
  refine ⟨54997138851686605722744623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146659036937830948593985661 54997138851686605722744623)
  ·
    refine ⟨82495708277529908584116935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54997138851686605722744623 82495708277529908584116935)
    ·
      refine ⟨123743562416294862876175403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82495708277529908584116935 123743562416294862876175403)
      ·
        refine ⟨185615343624442294314263105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123743562416294862876175403 185615343624442294314263105)
        ·
          refine ⟨139211507718331720735697329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 185615343624442294314263105 139211507718331720735697329)
          ·
            refine ⟨104408630788748790551772997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 139211507718331720735697329 104408630788748790551772997)
            ·
              refine ⟨19576618272890398228457437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 104408630788748790551772997 19576618272890398228457437)
              ·
                refine ⟨7341231852333899335671539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19576618272890398228457437 7341231852333899335671539)
                ·
                  refine ⟨11011847778500849003507309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7341231852333899335671539 11011847778500849003507309)
                  ·
                    refine ⟨4129442916937818376315241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11011847778500849003507309 4129442916937818376315241)
                    ·
                      refine ⟨3097082187703363782236431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4129442916937818376315241 3097082187703363782236431)
                      ·
                        rfl

theorem cell23_6031546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4, 3, 1, 3, 2].length) (baseStart_6031546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6031546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6031546 prefixEnd_6031546 := by exact prefixLift 6031546
  have htrace : WordTrace (prefixWord ++ tailWord_6031546) baseStart_6031546 baseEnd_6031546 := by
    simpa [prefixWord, tailWord_6031546, baseEnd_6031546] using wordTrace_append hprefix tailTrace_6031546
  have hstable : (prefixWord ++ tailWord_6031546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6031546).length < 2 ^ (prefixWord ++ tailWord_6031546).sum := by decide
  have hdescent : baseEnd_6031546 < baseStart_6031546 := by decide
  rcases family_descends (prefixWord ++ tailWord_6031546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6031562 : List Nat := [3, 1, 2, 1, 3, 1, 1, 2, 1, 3, 5]
def baseStart_6031562 : Nat := 118140960795 + 6031562 * 2 ^ 59
def prefixEnd_6031562 : Nat := 4983230072969 + 3 ^ 40 * 6031562 * 2
def baseEnd_6031562 : Nat := 3097090403393835719636357

theorem tailTrace_6031562 : CollatzResearch.WordTrace tailWord_6031562 prefixEnd_6031562 3097090403393835719636357 := by
  unfold tailWord_6031562
  simp only [CollatzResearch.WordTrace]
  refine ⟨54997284743672114405890235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146659425983125638415707293 54997284743672114405890235)
  ·
    refine ⟨82495927115508171608835353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54997284743672114405890235 82495927115508171608835353)
    ·
      refine ⟨61871945336631128706626515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82495927115508171608835353 61871945336631128706626515)
      ·
        refine ⟨92807918004946693059939773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61871945336631128706626515 92807918004946693059939773)
        ·
          refine ⟨34802969251855009897477415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92807918004946693059939773 34802969251855009897477415)
          ·
            refine ⟨52204453877782514846216123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34802969251855009897477415 52204453877782514846216123)
            ·
              refine ⟨78306680816673772269324185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52204453877782514846216123 78306680816673772269324185)
              ·
                refine ⟨58730010612505329201993139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78306680816673772269324185 58730010612505329201993139)
                ·
                  refine ⟨88095015918757993802989709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58730010612505329201993139 88095015918757993802989709)
                  ·
                    refine ⟨33035630969534247676121141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 88095015918757993802989709 33035630969534247676121141)
                    ·
                      refine ⟨3097090403393835719636357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33035630969534247676121141 3097090403393835719636357)
                      ·
                        rfl

theorem cell23_6031562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 2, 1, 3, 5].length) (baseStart_6031562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6031562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6031562 prefixEnd_6031562 := by exact prefixLift 6031562
  have htrace : WordTrace (prefixWord ++ tailWord_6031562) baseStart_6031562 baseEnd_6031562 := by
    simpa [prefixWord, tailWord_6031562, baseEnd_6031562] using wordTrace_append hprefix tailTrace_6031562
  have hstable : (prefixWord ++ tailWord_6031562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6031562).length < 2 ^ (prefixWord ++ tailWord_6031562).sum := by decide
  have hdescent : baseEnd_6031562 < baseStart_6031562 := by decide
  rcases family_descends (prefixWord ++ tailWord_6031562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6031570 : List Nat := [3, 2, 2, 2, 1, 4, 2, 1, 2, 1, 3]
def baseStart_6031570 : Nat := 118140960795 + 6031570 * 2 ^ 59
def prefixEnd_6031570 : Nat := 4983230072969 + 3 ^ 40 * 6031570 * 2
def baseEnd_6031570 : Nat := 3097094511239071688336321

theorem tailTrace_6031570 : CollatzResearch.WordTrace tailWord_6031570 prefixEnd_6031570 3097094511239071688336321 := by
  unfold tailWord_6031570
  simp only [CollatzResearch.WordTrace]
  refine ⟨54997357689664868747463041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146659620505772983326568109 54997357689664868747463041)
  ·
    refine ⟨41248018267248651560597281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54997357689664868747463041 41248018267248651560597281)
    ·
      refine ⟨30936013700436488670447961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41248018267248651560597281 30936013700436488670447961)
      ·
        refine ⟨23202010275327366502835971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30936013700436488670447961 23202010275327366502835971)
        ·
          refine ⟨34803015412991049754253957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23202010275327366502835971 34803015412991049754253957)
          ·
            refine ⟨6525565389935821828922617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34803015412991049754253957 6525565389935821828922617)
            ·
              refine ⟨4894174042451866371691963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6525565389935821828922617 4894174042451866371691963)
              ·
                refine ⟨7341261063677799557537945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4894174042451866371691963 7341261063677799557537945)
                ·
                  refine ⟨5505945797758349668153459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7341261063677799557537945 5505945797758349668153459)
                  ·
                    refine ⟨8258918696637524502230189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5505945797758349668153459 8258918696637524502230189)
                    ·
                      refine ⟨3097094511239071688336321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8258918696637524502230189 3097094511239071688336321)
                      ·
                        rfl

theorem cell23_6031570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 2, 1, 2, 1, 3].length) (baseStart_6031570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6031570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6031570 prefixEnd_6031570 := by exact prefixLift 6031570
  have htrace : WordTrace (prefixWord ++ tailWord_6031570) baseStart_6031570 baseEnd_6031570 := by
    simpa [prefixWord, tailWord_6031570, baseEnd_6031570] using wordTrace_append hprefix tailTrace_6031570
  have hstable : (prefixWord ++ tailWord_6031570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6031570).length < 2 ^ (prefixWord ++ tailWord_6031570).sum := by decide
  have hdescent : baseEnd_6031570 < baseStart_6031570 := by decide
  rcases family_descends (prefixWord ++ tailWord_6031570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6031580 : List Nat := [2, 2, 5, 2, 1, 1, 1, 1, 3, 3, 2]
def baseStart_6031580 : Nat := 118140960795 + 6031580 * 2 ^ 59
def prefixEnd_6031580 : Nat := 4983230072969 + 3 ^ 40 * 6031580 * 2
def baseEnd_6031580 : Nat := 3097099646045616649211275

theorem tailTrace_6031580 : CollatzResearch.WordTrace tailWord_6031580 prefixEnd_6031580 3097099646045616649211275 := by
  unfold tailWord_6031580
  simp only [CollatzResearch.WordTrace]
  refine ⟨109994897744311623348858097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146659863659082164465144129 109994897744311623348858097)
  ·
    refine ⟨82496173308233717511643573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109994897744311623348858097 82496173308233717511643573)
    ·
      refine ⟨7734016247646911016716585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 82496173308233717511643573 7734016247646911016716585)
      ·
        refine ⟨5800512185735183262537439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7734016247646911016716585 5800512185735183262537439)
        ·
          refine ⟨8700768278602774893806159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5800512185735183262537439 8700768278602774893806159)
          ·
            refine ⟨13051152417904162340709239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8700768278602774893806159 13051152417904162340709239)
            ·
              refine ⟨19576728626856243511063859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13051152417904162340709239 19576728626856243511063859)
              ·
                refine ⟨29365092940284365266595789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19576728626856243511063859 29365092940284365266595789)
                ·
                  refine ⟨11011909852606636974973421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29365092940284365266595789 11011909852606636974973421)
                  ·
                    refine ⟨4129466194727488865615033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11011909852606636974973421 4129466194727488865615033)
                    ·
                      refine ⟨3097099646045616649211275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4129466194727488865615033 3097099646045616649211275)
                      ·
                        rfl

theorem cell23_6031580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 1, 1, 3, 3, 2].length) (baseStart_6031580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6031580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6031580 prefixEnd_6031580 := by exact prefixLift 6031580
  have htrace : WordTrace (prefixWord ++ tailWord_6031580) baseStart_6031580 baseEnd_6031580 := by
    simpa [prefixWord, tailWord_6031580, baseEnd_6031580] using wordTrace_append hprefix tailTrace_6031580
  have hstable : (prefixWord ++ tailWord_6031580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6031580).length < 2 ^ (prefixWord ++ tailWord_6031580).sum := by decide
  have hdescent : baseEnd_6031580 < baseStart_6031580 := by decide
  rcases family_descends (prefixWord ++ tailWord_6031580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6031616 : List Nat := [2, 1, 1, 2, 1, 1, 8, 2, 5]
def baseStart_6031616 : Nat := 118140960795 + 6031616 * 2 ^ 59
def prefixEnd_6031616 : Nat := 4983230072969 + 3 ^ 40 * 6031616 * 2
def baseEnd_6031616 : Nat := 344124236816575389817901

theorem tailTrace_6031616 : CollatzResearch.WordTrace tailWord_6031616 prefixEnd_6031616 344124236816575389817901 := by
  unfold tailWord_6031616
  simp only [CollatzResearch.WordTrace]
  refine ⟨109995554258246412423013351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146660739010995216564017801 109995554258246412423013351)
  ·
    refine ⟨164993331387369618634520027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109995554258246412423013351 164993331387369618634520027)
    ·
      refine ⟨247489997081054427951780041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164993331387369618634520027 247489997081054427951780041)
      ·
        refine ⟨185617497810790820963835031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 247489997081054427951780041 185617497810790820963835031)
        ·
          refine ⟨278426246716186231445752547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185617497810790820963835031 278426246716186231445752547)
          ·
            refine ⟨417639370074279347168628821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 278426246716186231445752547 417639370074279347168628821)
            ·
              refine ⟨4894211368057961099632369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 417639370074279347168628821 4894211368057961099632369)
              ·
                refine ⟨3670658526043470824724277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4894211368057961099632369 3670658526043470824724277)
                ·
                  refine ⟨344124236816575389817901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3670658526043470824724277 344124236816575389817901)
                  ·
                    rfl

theorem cell23_6031616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 8, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 8, 2, 5].length) (baseStart_6031616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6031616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6031616 prefixEnd_6031616 := by exact prefixLift 6031616
  have htrace : WordTrace (prefixWord ++ tailWord_6031616) baseStart_6031616 baseEnd_6031616 := by
    simpa [prefixWord, tailWord_6031616, baseEnd_6031616] using wordTrace_append hprefix tailTrace_6031616
  have hstable : (prefixWord ++ tailWord_6031616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6031616).length < 2 ^ (prefixWord ++ tailWord_6031616).sum := by decide
  have hdescent : baseEnd_6031616 < baseStart_6031616 := by decide
  rcases family_descends (prefixWord ++ tailWord_6031616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6031619 : List Nat := [1, 1, 1, 3, 2, 3, 1, 1, 1, 7, 2]
def baseStart_6031619 : Nat := 118140960795 + 6031619 * 2 ^ 59
def prefixEnd_6031619 : Nat := 4983230072969 + 3 ^ 40 * 6031619 * 2
def baseEnd_6031619 : Nat := 3097119671791141996623595

theorem tailTrace_6031619 : CollatzResearch.WordTrace tailWord_6031619 prefixEnd_6031619 3097119671791141996623595 := by
  unfold tailWord_6031619
  simp only [CollatzResearch.WordTrace]
  refine ⟨219991217935481956358385911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146660811956987970905590607 219991217935481956358385911)
  ·
    refine ⟨329986826903222934537578867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219991217935481956358385911 329986826903222934537578867)
    ·
      refine ⟨494980240354834401806368301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 329986826903222934537578867 494980240354834401806368301)
      ·
        refine ⟨185617590133062900677388113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 494980240354834401806368301 185617590133062900677388113)
        ·
          refine ⟨139213192599797175508041085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 185617590133062900677388113 139213192599797175508041085)
          ·
            refine ⟨52204947224923940815515407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 139213192599797175508041085 52204947224923940815515407)
            ·
              refine ⟨78307420837385911223273111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52204947224923940815515407 78307420837385911223273111)
              ·
                refine ⟨117461131256078866834909667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78307420837385911223273111 117461131256078866834909667)
                ·
                  refine ⟨176191696884118300252364501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 117461131256078866834909667 176191696884118300252364501)
                  ·
                    refine ⟨4129492895721522662164793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 176191696884118300252364501 4129492895721522662164793)
                    ·
                      refine ⟨3097119671791141996623595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4129492895721522662164793 3097119671791141996623595)
                      ·
                        rfl

theorem cell23_6031619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 1, 1, 7, 2].length) (baseStart_6031619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6031619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6031619 prefixEnd_6031619 := by exact prefixLift 6031619
  have htrace : WordTrace (prefixWord ++ tailWord_6031619) baseStart_6031619 baseEnd_6031619 := by
    simpa [prefixWord, tailWord_6031619, baseEnd_6031619] using wordTrace_append hprefix tailTrace_6031619
  have hstable : (prefixWord ++ tailWord_6031619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6031619).length < 2 ^ (prefixWord ++ tailWord_6031619).sum := by decide
  have hdescent : baseEnd_6031619 < baseStart_6031619 := by decide
  rcases family_descends (prefixWord ++ tailWord_6031619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6031676 : List Nat := [2, 2, 2, 2, 1, 2, 4, 1, 3, 4]
def baseStart_6031676 : Nat := 118140960795 + 6031676 * 2 ^ 59
def prefixEnd_6031676 : Nat := 4983230072969 + 3 ^ 40 * 6031676 * 2
def baseEnd_6031676 : Nat := 1032382980062816091203611

theorem tailTrace_6031676 : CollatzResearch.WordTrace tailWord_6031676 prefixEnd_6031676 1032382980062816091203611 := by
  unfold tailWord_6031676
  simp only [CollatzResearch.WordTrace]
  refine ⟨109996648448137727546605441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146662197930850303395473921 109996648448137727546605441)
  ·
    refine ⟨82497486336103295659954081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109996648448137727546605441 82497486336103295659954081)
    ·
      refine ⟨61873114752077471744965561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82497486336103295659954081 61873114752077471744965561)
      ·
        refine ⟨46404836064058103808724171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61873114752077471744965561 46404836064058103808724171)
        ·
          refine ⟨69607254096087155713086257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46404836064058103808724171 69607254096087155713086257)
          ·
            refine ⟨52205440572065366784814693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69607254096087155713086257 52205440572065366784814693)
            ·
              refine ⟨9788520107262256272152755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52205440572065366784814693 9788520107262256272152755)
              ·
                refine ⟨14682780160893384408229133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9788520107262256272152755 14682780160893384408229133)
                ·
                  refine ⟨5506042560335019153085925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14682780160893384408229133 5506042560335019153085925)
                  ·
                    refine ⟨1032382980062816091203611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5506042560335019153085925 1032382980062816091203611)
                    ·
                      rfl

theorem cell23_6031676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 4, 1, 3, 4].length) (baseStart_6031676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6031676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6031676 prefixEnd_6031676 := by exact prefixLift 6031676
  have htrace : WordTrace (prefixWord ++ tailWord_6031676) baseStart_6031676 baseEnd_6031676 := by
    simpa [prefixWord, tailWord_6031676, baseEnd_6031676] using wordTrace_append hprefix tailTrace_6031676
  have hstable : (prefixWord ++ tailWord_6031676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6031676).length < 2 ^ (prefixWord ++ tailWord_6031676).sum := by decide
  have hdescent : baseEnd_6031676 < baseStart_6031676 := by decide
  rcases family_descends (prefixWord ++ tailWord_6031676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6031749 : List Nat := [1, 3, 1, 1, 3, 1, 1, 5, 1, 6]
def baseStart_6031749 : Nat := 118140960795 + 6031749 * 2 ^ 59
def prefixEnd_6031749 : Nat := 4983230072969 + 3 ^ 40 * 6031749 * 2
def baseEnd_6031749 : Nat := 1032395474758742162665999

theorem tailTrace_6031749 : CollatzResearch.WordTrace tailWord_6031749 prefixEnd_6031749 1032395474758742162665999 := by
  unfold tailWord_6031749
  simp only [CollatzResearch.WordTrace]
  refine ⟨219995959425010988560618301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146663972950007325707078867 219995959425010988560618301)
  ·
    refine ⟨82498484784379120710231863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 219995959425010988560618301 82498484784379120710231863)
    ·
      refine ⟨123747727176568681065347795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82498484784379120710231863 123747727176568681065347795)
      ·
        refine ⟨185621590764853021598021693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123747727176568681065347795 185621590764853021598021693)
        ·
          refine ⟨69608096536819883099258135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 185621590764853021598021693 69608096536819883099258135)
          ·
            refine ⟨104412144805229824648887203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69608096536819883099258135 104412144805229824648887203)
            ·
              refine ⟨156618217207844736973330805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104412144805229824648887203 156618217207844736973330805)
              ·
                refine ⟨14682957863235444091249763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 156618217207844736973330805 14682957863235444091249763)
                ·
                  refine ⟨22024436794853166136874645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14682957863235444091249763 22024436794853166136874645)
                  ·
                    refine ⟨1032395474758742162665999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22024436794853166136874645 1032395474758742162665999)
                    ·
                      rfl

theorem cell23_6031749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 5, 1, 6].length) (baseStart_6031749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6031749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6031749 prefixEnd_6031749 := by exact prefixLift 6031749
  have htrace : WordTrace (prefixWord ++ tailWord_6031749) baseStart_6031749 baseEnd_6031749 := by
    simpa [prefixWord, tailWord_6031749, baseEnd_6031749] using wordTrace_append hprefix tailTrace_6031749
  have hstable : (prefixWord ++ tailWord_6031749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6031749).length < 2 ^ (prefixWord ++ tailWord_6031749).sum := by decide
  have hdescent : baseEnd_6031749 < baseStart_6031749 := by decide
  rcases family_descends (prefixWord ++ tailWord_6031749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6031753 : List Nat := [1, 2, 1, 1, 6, 3, 1, 2, 1, 5]
def baseStart_6031753 : Nat := 118140960795 + 6031753 * 2 ^ 59
def prefixEnd_6031753 : Nat := 4983230072969 + 3 ^ 40 * 6031753 * 2
def baseEnd_6031753 : Nat := 1032396159399614824115993

theorem tailTrace_6031753 : CollatzResearch.WordTrace tailWord_6031753 prefixEnd_6031753 1032396159399614824115993 := by
  unfold tailWord_6031753
  simp only [CollatzResearch.WordTrace]
  refine ⟨219996105316996497243763913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146664070211330998162509275 219996105316996497243763913)
  ·
    refine ⟨164997078987747372932822935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219996105316996497243763913 164997078987747372932822935)
    ·
      refine ⟨247495618481621059399234403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164997078987747372932822935 247495618481621059399234403)
      ·
        refine ⟨371243427722431589098851605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 247495618481621059399234403 371243427722431589098851605)
        ·
          refine ⟨17402035674488980739008669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 371243427722431589098851605 17402035674488980739008669)
          ·
            refine ⟨6525763377933367777128251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17402035674488980739008669 6525763377933367777128251)
            ·
              refine ⟨9788645066900051665692377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6525763377933367777128251 9788645066900051665692377)
              ·
                refine ⟨7341483800175038749269283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9788645066900051665692377 7341483800175038749269283)
                ·
                  refine ⟨11012225700262558123903925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7341483800175038749269283 11012225700262558123903925)
                  ·
                    refine ⟨1032396159399614824115993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11012225700262558123903925 1032396159399614824115993)
                    ·
                      rfl

theorem cell23_6031753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 1, 2, 1, 5].length) (baseStart_6031753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6031753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6031753 prefixEnd_6031753 := by exact prefixLift 6031753
  have htrace : WordTrace (prefixWord ++ tailWord_6031753) baseStart_6031753 baseEnd_6031753 := by
    simpa [prefixWord, tailWord_6031753, baseEnd_6031753] using wordTrace_append hprefix tailTrace_6031753
  have hstable : (prefixWord ++ tailWord_6031753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6031753).length < 2 ^ (prefixWord ++ tailWord_6031753).sum := by decide
  have hdescent : baseEnd_6031753 < baseStart_6031753 := by decide
  rcases family_descends (prefixWord ++ tailWord_6031753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6031756 : List Nat := [2, 2, 1, 2, 1, 5, 1, 1, 3, 1, 4]
def baseStart_6031756 : Nat := 118140960795 + 6031756 * 2 ^ 59
def prefixEnd_6031756 : Nat := 4983230072969 + 3 ^ 40 * 6031756 * 2
def baseEnd_6031756 : Nat := 3097190018640807960610465

theorem tailTrace_6031756 : CollatzResearch.WordTrace tailWord_6031756 prefixEnd_6031756 3097190018640807960610465 := by
  unfold tailWord_6031756
  simp only [CollatzResearch.WordTrace]
  refine ⟨109998107367992814378061561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146664143157323752504082081 109998107367992814378061561)
  ·
    refine ⟨82498580525994610783546171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109998107367992814378061561 82498580525994610783546171)
    ·
      refine ⟨123747870788991916175319257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82498580525994610783546171 123747870788991916175319257)
      ·
        refine ⟨92810903091743937131489443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123747870788991916175319257 92810903091743937131489443)
        ·
          refine ⟨139216354637615905697234165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92810903091743937131489443 139216354637615905697234165)
          ·
            refine ⟨13051533247276491159115703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 139216354637615905697234165 13051533247276491159115703)
            ·
              refine ⟨19577299870914736738673555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13051533247276491159115703 19577299870914736738673555)
              ·
                refine ⟨29365949806372105108010333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19577299870914736738673555 29365949806372105108010333)
                ·
                  refine ⟨11012231177389539415503875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29365949806372105108010333 11012231177389539415503875)
                  ·
                    refine ⟨16518346766084309123255813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11012231177389539415503875 16518346766084309123255813)
                    ·
                      refine ⟨3097190018640807960610465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16518346766084309123255813 3097190018640807960610465)
                      ·
                        rfl

theorem cell23_6031756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 1, 1, 3, 1, 4].length) (baseStart_6031756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6031756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6031756 prefixEnd_6031756 := by exact prefixLift 6031756
  have htrace : WordTrace (prefixWord ++ tailWord_6031756) baseStart_6031756 baseEnd_6031756 := by
    simpa [prefixWord, tailWord_6031756, baseEnd_6031756] using wordTrace_append hprefix tailTrace_6031756
  have hstable : (prefixWord ++ tailWord_6031756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6031756).length < 2 ^ (prefixWord ++ tailWord_6031756).sum := by decide
  have hdescent : baseEnd_6031756 < baseStart_6031756 := by decide
  rcases family_descends (prefixWord ++ tailWord_6031756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6031776 : List Nat := [2, 1, 1, 4, 1, 3, 3, 1, 1, 1, 5]
def baseStart_6031776 : Nat := 118140960795 + 6031776 * 2 ^ 59
def prefixEnd_6031776 : Nat := 4983230072969 + 3 ^ 40 * 6031776 * 2
def baseEnd_6031776 : Nat := 3097200288253897882360373

theorem tailTrace_6031776 : CollatzResearch.WordTrace tailWord_6031776 prefixEnd_6031776 3097200288253897882360373 := by
  unfold tailWord_6031776
  simp only [CollatzResearch.WordTrace]
  refine ⟨109998472097956586085925591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146664629463942114781234121 109998472097956586085925591)
  ·
    refine ⟨164997708146934879128888387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109998472097956586085925591 164997708146934879128888387)
    ·
      refine ⟨247496562220402318693332581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164997708146934879128888387 247496562220402318693332581)
      ·
        refine ⟨46405605416325434754999859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 247496562220402318693332581 46405605416325434754999859)
        ·
          refine ⟨69608408124488152132499789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46405605416325434754999859 69608408124488152132499789)
          ·
            refine ⟨26103153046683057049687421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69608408124488152132499789 26103153046683057049687421)
            ·
              refine ⟨9788682392506146393632783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26103153046683057049687421 9788682392506146393632783)
              ·
                refine ⟨14683023588759219590449175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9788682392506146393632783 14683023588759219590449175)
                ·
                  refine ⟨22024535383138829385673763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14683023588759219590449175 22024535383138829385673763)
                  ·
                    refine ⟨33036803074708244078510645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22024535383138829385673763 33036803074708244078510645)
                    ·
                      refine ⟨3097200288253897882360373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33036803074708244078510645 3097200288253897882360373)
                      ·
                        rfl

theorem cell23_6031776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 3, 1, 1, 1, 5].length) (baseStart_6031776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6031776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6031776 prefixEnd_6031776 := by exact prefixLift 6031776
  have htrace : WordTrace (prefixWord ++ tailWord_6031776) baseStart_6031776 baseEnd_6031776 := by
    simpa [prefixWord, tailWord_6031776, baseEnd_6031776] using wordTrace_append hprefix tailTrace_6031776
  have hstable : (prefixWord ++ tailWord_6031776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6031776).length < 2 ^ (prefixWord ++ tailWord_6031776).sum := by decide
  have hdescent : baseEnd_6031776 < baseStart_6031776 := by decide
  rcases family_descends (prefixWord ++ tailWord_6031776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6031783 : List Nat := [1, 1, 6, 1, 1, 2, 1, 4, 2, 4]
def baseStart_6031783 : Nat := 118140960795 + 6031783 * 2 ^ 59
def prefixEnd_6031783 : Nat := 4983230072969 + 3 ^ 40 * 6031783 * 2
def baseEnd_6031783 : Nat := 1032401294206159784990947

theorem tailTrace_6031783 : CollatzResearch.WordTrace tailWord_6031783 prefixEnd_6031783 1032401294206159784990947 := by
  unfold tailWord_6031783
  simp only [CollatzResearch.WordTrace]
  refine ⟨219997199506887812367356003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146664799671258541578237335 219997199506887812367356003)
  ·
    refine ⟨329995799260331718551034005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219997199506887812367356003 329995799260331718551034005)
    ·
      refine ⟨15468553090328049307079719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 329995799260331718551034005 15468553090328049307079719)
      ·
        refine ⟨23202829635492073960619579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15468553090328049307079719 23202829635492073960619579)
        ·
          refine ⟨34804244453238110940929369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23202829635492073960619579 34804244453238110940929369)
          ·
            refine ⟨26103183339928583205697027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34804244453238110940929369 26103183339928583205697027)
            ·
              refine ⟨39154775009892874808545541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26103183339928583205697027 39154775009892874808545541)
              ·
                refine ⟨7341520314354914026602289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39154775009892874808545541 7341520314354914026602289)
                ·
                  refine ⟨5506140235766185519951717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7341520314354914026602289 5506140235766185519951717)
                  ·
                    refine ⟨1032401294206159784990947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5506140235766185519951717 1032401294206159784990947)
                    ·
                      rfl

theorem cell23_6031783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 4, 2, 4].length) (baseStart_6031783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6031783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6031783 prefixEnd_6031783 := by exact prefixLift 6031783
  have htrace : WordTrace (prefixWord ++ tailWord_6031783) baseStart_6031783 baseEnd_6031783 := by
    simpa [prefixWord, tailWord_6031783, baseEnd_6031783] using wordTrace_append hprefix tailTrace_6031783
  have hstable : (prefixWord ++ tailWord_6031783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6031783).length < 2 ^ (prefixWord ++ tailWord_6031783).sum := by decide
  have hdescent : baseEnd_6031783 < baseStart_6031783 := by decide
  rcases family_descends (prefixWord ++ tailWord_6031783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6031784 : List Nat := [2, 1, 6, 1, 1, 1, 4, 2, 1, 1, 3]
def baseStart_6031784 : Nat := 118140960795 + 6031784 * 2 ^ 59
def prefixEnd_6031784 : Nat := 4983230072969 + 3 ^ 40 * 6031784 * 2
def baseEnd_6031784 : Nat := 3097204396099133851060337

theorem tailTrace_6031784 : CollatzResearch.WordTrace tailWord_6031784 prefixEnd_6031784 3097204396099133851060337 := by
  unfold tailWord_6031784
  simp only [CollatzResearch.WordTrace]
  refine ⟨109998617989942094769071203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146664823986589459692094937 109998617989942094769071203)
  ·
    refine ⟨164997926984913142153606805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109998617989942094769071203 164997926984913142153606805)
    ·
      refine ⟨7734277827417803538450319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 164997926984913142153606805 7734277827417803538450319)
      ·
        refine ⟨11601416741126705307675479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7734277827417803538450319 11601416741126705307675479)
        ·
          refine ⟨17402125111690057961513219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11601416741126705307675479 17402125111690057961513219)
          ·
            refine ⟨26103187667535086942269829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17402125111690057961513219 26103187667535086942269829)
            ·
              refine ⟨4894347687662828801675593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26103187667535086942269829 4894347687662828801675593)
              ·
                refine ⟨3670760765747121601256695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4894347687662828801675593 3670760765747121601256695)
                ·
                  refine ⟨5506141148620682401885043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3670760765747121601256695 5506141148620682401885043)
                  ·
                    refine ⟨8259211722931023602827565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5506141148620682401885043 8259211722931023602827565)
                    ·
                      refine ⟨3097204396099133851060337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8259211722931023602827565 3097204396099133851060337)
                      ·
                        rfl

theorem cell23_6031784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 4, 2, 1, 1, 3].length) (baseStart_6031784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6031784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6031784 prefixEnd_6031784 := by exact prefixLift 6031784
  have htrace : WordTrace (prefixWord ++ tailWord_6031784) baseStart_6031784 baseEnd_6031784 := by
    simpa [prefixWord, tailWord_6031784, baseEnd_6031784] using wordTrace_append hprefix tailTrace_6031784
  have hstable : (prefixWord ++ tailWord_6031784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6031784).length < 2 ^ (prefixWord ++ tailWord_6031784).sum := by decide
  have hdescent : baseEnd_6031784 < baseStart_6031784 := by decide
  rcases family_descends (prefixWord ++ tailWord_6031784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6031819 : List Nat := [1, 1, 1, 1, 3, 3, 1, 3, 2, 2, 5]
def baseStart_6031819 : Nat := 118140960795 + 6031819 * 2 ^ 59
def prefixEnd_6031819 : Nat := 4983230072969 + 3 ^ 40 * 6031819 * 2
def baseEnd_6031819 : Nat := 3097222367922041214122675

theorem tailTrace_6031819 : CollatzResearch.WordTrace tailWord_6031819 prefixEnd_6031819 3097222367922041214122675 := by
  unfold tailWord_6031819
  simp only [CollatzResearch.WordTrace]
  refine ⟨219998512534757390515666511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146665675023171593677111007 219998512534757390515666511)
  ·
    refine ⟨329997768802136085773499767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219998512534757390515666511 329997768802136085773499767)
    ·
      refine ⟨494996653203204128660249651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 329997768802136085773499767 494996653203204128660249651)
      ·
        refine ⟨742494979804806192990374477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 494996653203204128660249651 742494979804806192990374477)
        ·
          refine ⟨278435617426802322371390429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 742494979804806192990374477 278435617426802322371390429)
          ·
            refine ⟨104413356535050870889271411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 278435617426802322371390429 104413356535050870889271411)
            ·
              refine ⟨156620034802576306333907117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104413356535050870889271411 156620034802576306333907117)
              ·
                refine ⟨58732513050966114875215169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 156620034802576306333907117 58732513050966114875215169)
                ·
                  refine ⟨44049384788224586156411377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58732513050966114875215169 44049384788224586156411377)
                  ·
                    refine ⟨33037038591168439617308533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 44049384788224586156411377 33037038591168439617308533)
                    ·
                      refine ⟨3097222367922041214122675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33037038591168439617308533 3097222367922041214122675)
                      ·
                        rfl

theorem cell23_6031819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 3, 2, 2, 5].length) (baseStart_6031819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6031819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6031819 prefixEnd_6031819 := by exact prefixLift 6031819
  have htrace : WordTrace (prefixWord ++ tailWord_6031819) baseStart_6031819 baseEnd_6031819 := by
    simpa [prefixWord, tailWord_6031819, baseEnd_6031819] using wordTrace_append hprefix tailTrace_6031819
  have hstable : (prefixWord ++ tailWord_6031819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6031819).length < 2 ^ (prefixWord ++ tailWord_6031819).sum := by decide
  have hdescent : baseEnd_6031819 < baseStart_6031819 := by decide
  rcases family_descends (prefixWord ++ tailWord_6031819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6031849 : List Nat := [1, 2, 1, 1, 1, 2, 1, 3, 3, 3, 5]
def baseStart_6031849 : Nat := 118140960795 + 6031849 * 2 ^ 59
def prefixEnd_6031849 : Nat := 4983230072969 + 3 ^ 40 * 6031849 * 2
def baseEnd_6031849 : Nat := 3097237772341676096747537

theorem tailTrace_6031849 : CollatzResearch.WordTrace tailWord_6031849 prefixEnd_6031849 3097237772341676096747537 := by
  unfold tailWord_6031849
  simp only [CollatzResearch.WordTrace]
  refine ⟨219999606724648705639258601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146666404483099137092839067 219999606724648705639258601)
  ·
    refine ⟨164999705043486529229443951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219999606724648705639258601 164999705043486529229443951)
    ·
      refine ⟨247499557565229793844165927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164999705043486529229443951 247499557565229793844165927)
      ·
        refine ⟨371249336347844690766248891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 247499557565229793844165927 371249336347844690766248891)
        ·
          refine ⟨556874004521767036149373337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 371249336347844690766248891 556874004521767036149373337)
          ·
            refine ⟨417655503391325277112030003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 556874004521767036149373337 417655503391325277112030003)
            ·
              refine ⟨626483255086987915668045005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 417655503391325277112030003 626483255086987915668045005)
              ·
                refine ⟨234931220657620468375516877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 626483255086987915668045005 234931220657620468375516877)
                ·
                  refine ⟨88099207746607675640818829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 234931220657620468375516877 88099207746607675640818829)
                  ·
                    refine ⟨33037202904977878365307061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 88099207746607675640818829 33037202904977878365307061)
                    ·
                      refine ⟨3097237772341676096747537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33037202904977878365307061 3097237772341676096747537)
                      ·
                        rfl

theorem cell23_6031849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 3, 3, 3, 5].length) (baseStart_6031849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6031849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6031849 prefixEnd_6031849 := by exact prefixLift 6031849
  have htrace : WordTrace (prefixWord ++ tailWord_6031849) baseStart_6031849 baseEnd_6031849 := by
    simpa [prefixWord, tailWord_6031849, baseEnd_6031849] using wordTrace_append hprefix tailTrace_6031849
  have hstable : (prefixWord ++ tailWord_6031849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6031849).length < 2 ^ (prefixWord ++ tailWord_6031849).sum := by decide
  have hdescent : baseEnd_6031849 < baseStart_6031849 := by decide
  rcases family_descends (prefixWord ++ tailWord_6031849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6031899 : List Nat := [1, 1, 1, 1, 1, 1, 3, 1, 2, 11]
def baseStart_6031899 : Nat := 118140960795 + 6031899 * 2 ^ 59
def prefixEnd_6031899 : Nat := 4983230072969 + 3 ^ 40 * 6031899 * 2
def baseEnd_6031899 : Nat := 1032421148791466967040769

theorem tailTrace_6031899 : CollatzResearch.WordTrace tailWord_6031899 prefixEnd_6031899 1032421148791466967040769 := by
  unfold tailWord_6031899
  simp only [CollatzResearch.WordTrace]
  refine ⟨220001430374467564178578751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146667620249645042785719167 220001430374467564178578751)
  ·
    refine ⟨330002145561701346267868127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220001430374467564178578751 330002145561701346267868127)
    ·
      refine ⟨495003218342552019401802191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 330002145561701346267868127 495003218342552019401802191)
      ·
        refine ⟨742504827513828029102703287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 495003218342552019401802191 742504827513828029102703287)
        ·
          refine ⟨1113757241270742043654054931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 742504827513828029102703287 1113757241270742043654054931)
          ·
            refine ⟨1670635861906113065481082397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1113757241270742043654054931 1670635861906113065481082397)
            ·
              refine ⟨626488448214792399555405899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1670635861906113065481082397 626488448214792399555405899)
              ·
                refine ⟨939732672322188599333108849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 626488448214792399555405899 939732672322188599333108849)
                ·
                  refine ⟨704799504241641449499831637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 939732672322188599333108849 704799504241641449499831637)
                  ·
                    refine ⟨1032421148791466967040769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 704799504241641449499831637 1032421148791466967040769)
                    ·
                      rfl

theorem cell23_6031899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 11].length) (baseStart_6031899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6031899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6031899 prefixEnd_6031899 := by exact prefixLift 6031899
  have htrace : WordTrace (prefixWord ++ tailWord_6031899) baseStart_6031899 baseEnd_6031899 := by
    simpa [prefixWord, tailWord_6031899, baseEnd_6031899] using wordTrace_append hprefix tailTrace_6031899
  have hstable : (prefixWord ++ tailWord_6031899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6031899).length < 2 ^ (prefixWord ++ tailWord_6031899).sum := by decide
  have hdescent : baseEnd_6031899 < baseStart_6031899 := by decide
  rcases family_descends (prefixWord ++ tailWord_6031899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6031914 : List Nat := [3, 1, 4, 1, 1, 2, 4, 1, 2, 2, 2]
def baseStart_6031914 : Nat := 118140960795 + 6031914 * 2 ^ 59
def prefixEnd_6031914 : Nat := 4983230072969 + 3 ^ 40 * 6031914 * 2
def baseEnd_6031914 : Nat := 3097271148584218342434739

theorem tailTrace_6031914 : CollatzResearch.WordTrace tailWord_6031914 prefixEnd_6031914 3097271148584218342434739 := by
  unfold tailWord_6031914
  simp only [CollatzResearch.WordTrace]
  refine ⟨55000494367353305435093699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146667984979608814493583197 55000494367353305435093699)
  ·
    refine ⟨82500741551029958152640549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55000494367353305435093699 82500741551029958152640549)
    ·
      refine ⟨15468889040818117153620103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 82500741551029958152640549 15468889040818117153620103)
      ·
        refine ⟨23203333561227175730430155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15468889040818117153620103 23203333561227175730430155)
        ·
          refine ⟨34805000341840763595645233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23203333561227175730430155 34805000341840763595645233)
          ·
            refine ⟨26103750256380572696733925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34805000341840763595645233 26103750256380572696733925)
            ·
              refine ⟨4894453173071357380637611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26103750256380572696733925 4894453173071357380637611)
              ·
                refine ⟨7341679759607036070956417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4894453173071357380637611 7341679759607036070956417)
                ·
                  refine ⟨5506259819705277053217313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7341679759607036070956417 5506259819705277053217313)
                  ·
                    refine ⟨4129694864778957789912985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5506259819705277053217313 4129694864778957789912985)
                    ·
                      refine ⟨3097271148584218342434739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4129694864778957789912985 3097271148584218342434739)
                      ·
                        rfl

theorem cell23_6031914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 4, 1, 2, 2, 2].length) (baseStart_6031914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6031914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6031914 prefixEnd_6031914 := by exact prefixLift 6031914
  have htrace : WordTrace (prefixWord ++ tailWord_6031914) baseStart_6031914 baseEnd_6031914 := by
    simpa [prefixWord, tailWord_6031914, baseEnd_6031914] using wordTrace_append hprefix tailTrace_6031914
  have hstable : (prefixWord ++ tailWord_6031914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6031914).length < 2 ^ (prefixWord ++ tailWord_6031914).sum := by decide
  have hdescent : baseEnd_6031914 < baseStart_6031914 := by decide
  rcases family_descends (prefixWord ++ tailWord_6031914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6031933 : List Nat := [1, 4, 1, 3, 2, 1, 1, 3, 2, 5]
def baseStart_6031933 : Nat := 118140960795 + 6031933 * 2 ^ 59
def prefixEnd_6031933 : Nat := 4983230072969 + 3 ^ 40 * 6031933 * 2
def baseEnd_6031933 : Nat := 1032426968238884589365717

theorem tailTrace_6031933 : CollatzResearch.WordTrace tailWord_6031933 prefixEnd_6031933 1032426968238884589365717 := by
  unfold tailWord_6031933
  simp only [CollatzResearch.WordTrace]
  refine ⟨220002670456344387985316453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146668446970896258656877635 220002670456344387985316453)
  ·
    refine ⟨41250500710564572747246835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 220002670456344387985316453 41250500710564572747246835)
    ·
      refine ⟨61875751065846859120870253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41250500710564572747246835 61875751065846859120870253)
      ·
        refine ⟨23203406649692572170326345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61875751065846859120870253 23203406649692572170326345)
        ·
          refine ⟨17402554987269429127744759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23203406649692572170326345 17402554987269429127744759)
          ·
            refine ⟨26103832480904143691617139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17402554987269429127744759 26103832480904143691617139)
            ·
              refine ⟨39155748721356215537425709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26103832480904143691617139 39155748721356215537425709)
              ·
                refine ⟨14683405770508580826534641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39155748721356215537425709 14683405770508580826534641)
                ·
                  refine ⟨11012554327881435619900981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14683405770508580826534641 11012554327881435619900981)
                  ·
                    refine ⟨1032426968238884589365717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11012554327881435619900981 1032426968238884589365717)
                    ·
                      rfl

theorem cell23_6031933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 3, 2, 5].length) (baseStart_6031933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6031933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6031933 prefixEnd_6031933 := by exact prefixLift 6031933
  have htrace : WordTrace (prefixWord ++ tailWord_6031933) baseStart_6031933 baseEnd_6031933 := by
    simpa [prefixWord, tailWord_6031933, baseEnd_6031933] using wordTrace_append hprefix tailTrace_6031933
  have hstable : (prefixWord ++ tailWord_6031933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6031933).length < 2 ^ (prefixWord ++ tailWord_6031933).sum := by decide
  have hdescent : baseEnd_6031933 < baseStart_6031933 := by decide
  rcases family_descends (prefixWord ++ tailWord_6031933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6031936 : List Nat := [2, 1, 1, 2, 2, 2, 2, 3, 1, 3, 4]
def baseStart_6031936 : Nat := 118140960795 + 6031936 * 2 ^ 59
def prefixEnd_6031936 : Nat := 4983230072969 + 3 ^ 40 * 6031936 * 2
def baseEnd_6031936 : Nat := 3097282445158617256359637

theorem tailTrace_6031936 : CollatzResearch.WordTrace tailWord_6031936 prefixEnd_6031936 3097282445158617256359637 := by
  unfold tailWord_6031936
  simp only [CollatzResearch.WordTrace]
  refine ⟨110001389937666759748837831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146668519916889012998450441 110001389937666759748837831)
  ·
    refine ⟨165002084906500139623256747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110001389937666759748837831 165002084906500139623256747)
    ·
      refine ⟨247503127359750209434885121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165002084906500139623256747 247503127359750209434885121)
      ·
        refine ⟨185627345519812657076163841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 247503127359750209434885121 185627345519812657076163841)
        ·
          refine ⟨139220509139859492807122881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 185627345519812657076163841 139220509139859492807122881)
          ·
            refine ⟨104415381854894619605342161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 139220509139859492807122881 104415381854894619605342161)
            ·
              refine ⟨78311536391170964704006621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104415381854894619605342161 78311536391170964704006621)
              ·
                refine ⟨29366826146689111764002483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78311536391170964704006621 29366826146689111764002483)
                ·
                  refine ⟨44050239220033667646003725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29366826146689111764002483 44050239220033667646003725)
                  ·
                    refine ⟨16518839707512625367251397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 44050239220033667646003725 16518839707512625367251397)
                    ·
                      refine ⟨3097282445158617256359637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16518839707512625367251397 3097282445158617256359637)
                      ·
                        rfl

theorem cell23_6031936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 3, 1, 3, 4].length) (baseStart_6031936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6031936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6031936 prefixEnd_6031936 := by exact prefixLift 6031936
  have htrace : WordTrace (prefixWord ++ tailWord_6031936) baseStart_6031936 baseEnd_6031936 := by
    simpa [prefixWord, tailWord_6031936, baseEnd_6031936] using wordTrace_append hprefix tailTrace_6031936
  have hstable : (prefixWord ++ tailWord_6031936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6031936).length < 2 ^ (prefixWord ++ tailWord_6031936).sum := by decide
  have hdescent : baseEnd_6031936 < baseStart_6031936 := by decide
  rcases family_descends (prefixWord ++ tailWord_6031936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6031953 : List Nat := [1, 2, 2, 1, 3, 3, 2, 2, 2, 1, 4]
def baseStart_6031953 : Nat := 118140960795 + 6031953 * 2 ^ 59
def prefixEnd_6031953 : Nat := 4983230072969 + 3 ^ 40 * 6031953 * 2
def baseEnd_6031953 : Nat := 3097291174329743689847059

theorem tailTrace_6031953 : CollatzResearch.WordTrace tailWord_6031953 prefixEnd_6031953 3097291174329743689847059 := by
  unfold tailWord_6031953
  simp only [CollatzResearch.WordTrace]
  refine ⟨220003399916271931401044513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146668933277514620934029675 220003399916271931401044513)
  ·
    refine ⟨165002549937203948550783385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220003399916271931401044513 165002549937203948550783385)
    ·
      refine ⟨123751912452902961413087539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165002549937203948550783385 123751912452902961413087539)
      ·
        refine ⟨185627868679354442119631309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123751912452902961413087539 185627868679354442119631309)
        ·
          refine ⟨69610450754757915794861741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 185627868679354442119631309 69610450754757915794861741)
          ·
            refine ⟨26103919033034218423073153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69610450754757915794861741 26103919033034218423073153)
            ·
              refine ⟨19577939274775663817304865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26103919033034218423073153 19577939274775663817304865)
              ·
                refine ⟨14683454456081747862978649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19577939274775663817304865 14683454456081747862978649)
                ·
                  refine ⟨11012590842061310897233987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14683454456081747862978649 11012590842061310897233987)
                  ·
                    refine ⟨16518886263091966345850981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11012590842061310897233987 16518886263091966345850981)
                    ·
                      refine ⟨3097291174329743689847059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16518886263091966345850981 3097291174329743689847059)
                      ·
                        rfl

theorem cell23_6031953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 2, 2, 2, 1, 4].length) (baseStart_6031953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6031953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6031953 prefixEnd_6031953 := by exact prefixLift 6031953
  have htrace : WordTrace (prefixWord ++ tailWord_6031953) baseStart_6031953 baseEnd_6031953 := by
    simpa [prefixWord, tailWord_6031953, baseEnd_6031953] using wordTrace_append hprefix tailTrace_6031953
  have hstable : (prefixWord ++ tailWord_6031953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6031953).length < 2 ^ (prefixWord ++ tailWord_6031953).sum := by decide
  have hdescent : baseEnd_6031953 < baseStart_6031953 := by decide
  rcases family_descends (prefixWord ++ tailWord_6031953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6032060 : List Nat := [2, 2, 2, 3, 1, 1, 1, 5, 1, 1, 4]
def baseStart_6032060 : Nat := 118140960795 + 6032060 * 2 ^ 59
def prefixEnd_6032060 : Nat := 4983230072969 + 3 ^ 40 * 6032060 * 2
def baseEnd_6032060 : Nat := 3097346116759774771209067

theorem tailTrace_6032060 : CollatzResearch.WordTrace tailWord_6032060 prefixEnd_6032060 3097346116759774771209067 := by
  unfold tailWord_6032060
  simp only [CollatzResearch.WordTrace]
  refine ⟨110003651263442144337594817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146671535017922859116793089 110003651263442144337594817)
  ·
    refine ⟨82502738447581608253196113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110003651263442144337594817 82502738447581608253196113)
    ·
      refine ⟨61877053835686206189897085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82502738447581608253196113 61877053835686206189897085)
      ·
        refine ⟨23203895188382327321211407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61877053835686206189897085 23203895188382327321211407)
        ·
          refine ⟨34805842782573490981817111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23203895188382327321211407 34805842782573490981817111)
          ·
            refine ⟨52208764173860236472725667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34805842782573490981817111 52208764173860236472725667)
            ·
              refine ⟨78313146260790354709088501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52208764173860236472725667 78313146260790354709088501)
              ·
                refine ⟨7341857461949095753977047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 78313146260790354709088501 7341857461949095753977047)
                ·
                  refine ⟨11012786192923643630965571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7341857461949095753977047 11012786192923643630965571)
                  ·
                    refine ⟨16519179289385465446448357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11012786192923643630965571 16519179289385465446448357)
                    ·
                      refine ⟨3097346116759774771209067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16519179289385465446448357 3097346116759774771209067)
                      ·
                        rfl

theorem cell23_6032060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 5, 1, 1, 4].length) (baseStart_6032060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6032060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6032060 prefixEnd_6032060 := by exact prefixLift 6032060
  have htrace : WordTrace (prefixWord ++ tailWord_6032060) baseStart_6032060 baseEnd_6032060 := by
    simpa [prefixWord, tailWord_6032060, baseEnd_6032060] using wordTrace_append hprefix tailTrace_6032060
  have hstable : (prefixWord ++ tailWord_6032060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6032060).length < 2 ^ (prefixWord ++ tailWord_6032060).sum := by decide
  have hdescent : baseEnd_6032060 < baseStart_6032060 := by decide
  rcases family_descends (prefixWord ++ tailWord_6032060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6032063 : List Nat := [1, 1, 2, 2, 2, 4, 1, 3, 1, 1, 5]
def baseStart_6032063 : Nat := 118140960795 + 6032063 * 2 ^ 59
def prefixEnd_6032063 : Nat := 4983230072969 + 3 ^ 40 * 6032063 * 2
def baseEnd_6032063 : Nat := 3097347657201738259471553

theorem tailTrace_6032063 : CollatzResearch.WordTrace tailWord_6032063 prefixEnd_6032063 3097347657201738259471553 := by
  unfold tailWord_6032063
  simp only [CollatzResearch.WordTrace]
  refine ⟨220007411945873420187548843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146671607963915613458365895 220007411945873420187548843)
  ·
    refine ⟨330011117918810130281323265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220007411945873420187548843 330011117918810130281323265)
    ·
      refine ⟨247508338439107597710992449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 330011117918810130281323265 247508338439107597710992449)
      ·
        refine ⟨185631253829330698283244337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 247508338439107597710992449 185631253829330698283244337)
        ·
          refine ⟨139223440371998023712433253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 185631253829330698283244337 139223440371998023712433253)
          ·
            refine ⟨26104395069749629446081235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 139223440371998023712433253 26104395069749629446081235)
            ·
              refine ⟨39156592604624444169121853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26104395069749629446081235 39156592604624444169121853)
              ·
                refine ⟨14683722226734166563420695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39156592604624444169121853 14683722226734166563420695)
                ·
                  refine ⟨22025583340101249845131043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14683722226734166563420695 22025583340101249845131043)
                  ·
                    refine ⟨33038375010151874767696565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22025583340101249845131043 33038375010151874767696565)
                    ·
                      refine ⟨3097347657201738259471553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33038375010151874767696565 3097347657201738259471553)
                      ·
                        rfl

theorem cell23_6032063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 3, 1, 1, 5].length) (baseStart_6032063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6032063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6032063 prefixEnd_6032063 := by exact prefixLift 6032063
  have htrace : WordTrace (prefixWord ++ tailWord_6032063) baseStart_6032063 baseEnd_6032063 := by
    simpa [prefixWord, tailWord_6032063, baseEnd_6032063] using wordTrace_append hprefix tailTrace_6032063
  have hstable : (prefixWord ++ tailWord_6032063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6032063).length < 2 ^ (prefixWord ++ tailWord_6032063).sum := by decide
  have hdescent : baseEnd_6032063 < baseStart_6032063 := by decide
  rcases family_descends (prefixWord ++ tailWord_6032063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6032087 : List Nat := [1, 1, 3, 2, 1, 4, 4, 1, 2, 4]
def baseStart_6032087 : Nat := 118140960795 + 6032087 * 2 ^ 59
def prefixEnd_6032087 : Nat := 4983230072969 + 3 ^ 40 * 6032087 * 2
def baseEnd_6032087 : Nat := 1032453326912482055190481

theorem tailTrace_6032087 : CollatzResearch.WordTrace tailWord_6032087 prefixEnd_6032087 1032453326912482055190481 := by
  unfold tailWord_6032087
  simp only [CollatzResearch.WordTrace]
  refine ⟨220008287297786472286422515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146672191531857648190948343 220008287297786472286422515)
  ·
    refine ⟨330012430946679708429633773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220008287297786472286422515 330012430946679708429633773)
    ·
      refine ⟨123754661605004890661112665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 330012430946679708429633773 123754661605004890661112665)
      ·
        refine ⟨92815996203753667995834499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123754661605004890661112665 92815996203753667995834499)
        ·
          refine ⟨139223994305630501993751749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92815996203753667995834499 139223994305630501993751749)
          ·
            refine ⟨26104498932305719123828453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 139223994305630501993751749 26104498932305719123828453)
            ·
              refine ⟨4894593549807322335717835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26104498932305719123828453 4894593549807322335717835)
              ·
                refine ⟨7341890324710983503576753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4894593549807322335717835 7341890324710983503576753)
                ·
                  refine ⟨5506417743533237627682565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7341890324710983503576753 5506417743533237627682565)
                  ·
                    refine ⟨1032453326912482055190481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5506417743533237627682565 1032453326912482055190481)
                    ·
                      rfl

theorem cell23_6032087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 4, 1, 2, 4].length) (baseStart_6032087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6032087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6032087 prefixEnd_6032087 := by exact prefixLift 6032087
  have htrace : WordTrace (prefixWord ++ tailWord_6032087) baseStart_6032087 baseEnd_6032087 := by
    simpa [prefixWord, tailWord_6032087, baseEnd_6032087] using wordTrace_append hprefix tailTrace_6032087
  have hstable : (prefixWord ++ tailWord_6032087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6032087).length < 2 ^ (prefixWord ++ tailWord_6032087).sum := by decide
  have hdescent : baseEnd_6032087 < baseStart_6032087 := by decide
  rcases family_descends (prefixWord ++ tailWord_6032087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6032097 : List Nat := [1, 2, 3, 1, 4, 1, 3, 2, 1, 2, 3]
def baseStart_6032097 : Nat := 118140960795 + 6032097 * 2 ^ 59
def prefixEnd_6032097 : Nat := 4983230072969 + 3 ^ 40 * 6032097 * 2
def baseEnd_6032097 : Nat := 3097365115543991126446397

theorem tailTrace_6032097 : CollatzResearch.WordTrace tailWord_6032097 prefixEnd_6032097 3097365115543991126446397 := by
  unfold tailWord_6032097
  simp only [CollatzResearch.WordTrace]
  refine ⟨220008652027750243994286545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146672434685166829329524363 220008652027750243994286545)
  ·
    refine ⟨165006489020812682995714909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220008652027750243994286545 165006489020812682995714909)
    ·
      refine ⟨61877433382804756123393091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 165006489020812682995714909 61877433382804756123393091)
      ·
        refine ⟨92816150074207134185089637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61877433382804756123393091 92816150074207134185089637)
        ·
          refine ⟨17403028138913837659704307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 92816150074207134185089637 17403028138913837659704307)
          ·
            refine ⟨26104542208370756489556461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17403028138913837659704307 26104542208370756489556461)
            ·
              refine ⟨9789203328139033683583673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26104542208370756489556461 9789203328139033683583673)
              ·
                refine ⟨7341902496104275262687755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9789203328139033683583673 7341902496104275262687755)
                ·
                  refine ⟨11012853744156412894031633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7341902496104275262687755 11012853744156412894031633)
                  ·
                    refine ⟨8259640308117309670523725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11012853744156412894031633 8259640308117309670523725)
                    ·
                      refine ⟨3097365115543991126446397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8259640308117309670523725 3097365115543991126446397)
                      ·
                        rfl

theorem cell23_6032097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 3, 2, 1, 2, 3].length) (baseStart_6032097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6032097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6032097 prefixEnd_6032097 := by exact prefixLift 6032097
  have htrace : WordTrace (prefixWord ++ tailWord_6032097) baseStart_6032097 baseEnd_6032097 := by
    simpa [prefixWord, tailWord_6032097, baseEnd_6032097] using wordTrace_append hprefix tailTrace_6032097
  have hstable : (prefixWord ++ tailWord_6032097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6032097).length < 2 ^ (prefixWord ++ tailWord_6032097).sum := by decide
  have hdescent : baseEnd_6032097 < baseStart_6032097 := by decide
  rcases family_descends (prefixWord ++ tailWord_6032097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6032110 : List Nat := [4, 1, 2, 1, 1, 3, 1, 1, 3, 3, 3]
def baseStart_6032110 : Nat := 118140960795 + 6032110 * 2 ^ 59
def prefixEnd_6032110 : Nat := 4983230072969 + 3 ^ 40 * 6032110 * 2
def baseEnd_6032110 : Nat := 3097371790792499575583837

theorem tailTrace_6032110 : CollatzResearch.WordTrace tailWord_6032110 prefixEnd_6032110 3097371790792499575583837 := by
  unfold tailWord_6032110
  simp only [CollatzResearch.WordTrace]
  refine ⟨27501140772087893401813723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 146672750784468764809673189 27501140772087893401813723)
  ·
    refine ⟨41251711158131840102720585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27501140772087893401813723 41251711158131840102720585)
    ·
      refine ⟨30938783368598880077040439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41251711158131840102720585 30938783368598880077040439)
      ·
        refine ⟨46408175052898320115560659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30938783368598880077040439 46408175052898320115560659)
        ·
          refine ⟨69612262579347480173340989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46408175052898320115560659 69612262579347480173340989)
          ·
            refine ⟨26104598467255305065002871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69612262579347480173340989 26104598467255305065002871)
            ·
              refine ⟨39156897700882957597504307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26104598467255305065002871 39156897700882957597504307)
              ·
                refine ⟨58735346551324436396256461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39156897700882957597504307 58735346551324436396256461)
                ·
                  refine ⟨22025754956746663648596173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58735346551324436396256461 22025754956746663648596173)
                  ·
                    refine ⟨8259658108779998868223565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22025754956746663648596173 8259658108779998868223565)
                    ·
                      refine ⟨3097371790792499575583837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8259658108779998868223565 3097371790792499575583837)
                      ·
                        rfl

theorem cell23_6032110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 1, 3, 3, 3].length) (baseStart_6032110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6032110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6032110 prefixEnd_6032110 := by exact prefixLift 6032110
  have htrace : WordTrace (prefixWord ++ tailWord_6032110) baseStart_6032110 baseEnd_6032110 := by
    simpa [prefixWord, tailWord_6032110, baseEnd_6032110] using wordTrace_append hprefix tailTrace_6032110
  have hstable : (prefixWord ++ tailWord_6032110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6032110).length < 2 ^ (prefixWord ++ tailWord_6032110).sum := by decide
  have hdescent : baseEnd_6032110 < baseStart_6032110 := by decide
  rcases family_descends (prefixWord ++ tailWord_6032110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6032114 : List Nat := [3, 2, 1, 3, 1, 3, 3, 1, 1, 2, 3]
def baseStart_6032114 : Nat := 118140960795 + 6032114 * 2 ^ 59
def prefixEnd_6032114 : Nat := 4983230072969 + 3 ^ 40 * 6032114 * 2
def baseEnd_6032114 : Nat := 3097373844715117559933819

theorem tailTrace_6032114 : CollatzResearch.WordTrace tailWord_6032114 prefixEnd_6032114 3097373844715117559933819 := by
  unfold tailWord_6032114
  simp only [CollatzResearch.WordTrace]
  refine ⟨55002318017172163974413849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146672848045792437265103597 55002318017172163974413849)
  ·
    refine ⟨41251738512879122980810387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55002318017172163974413849 41251738512879122980810387)
    ·
      refine ⟨61877607769318684471215581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41251738512879122980810387 61877607769318684471215581)
      ·
        refine ⟨23204102913494506676705843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61877607769318684471215581 23204102913494506676705843)
        ·
          refine ⟨34806154370241760015058765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23204102913494506676705843 34806154370241760015058765)
          ·
            refine ⟨13052307888840660005647037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34806154370241760015058765 13052307888840660005647037)
            ·
              refine ⟨4894615458315247502117639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13052307888840660005647037 4894615458315247502117639)
              ·
                refine ⟨7341923187472871253176459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4894615458315247502117639 7341923187472871253176459)
                ·
                  refine ⟨11012884781209306879764689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7341923187472871253176459 11012884781209306879764689)
                  ·
                    refine ⟨8259663585906980159823517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11012884781209306879764689 8259663585906980159823517)
                    ·
                      refine ⟨3097373844715117559933819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8259663585906980159823517 3097373844715117559933819)
                      ·
                        rfl

theorem cell23_6032114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 3, 1, 1, 2, 3].length) (baseStart_6032114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6032114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6032114 prefixEnd_6032114 := by exact prefixLift 6032114
  have htrace : WordTrace (prefixWord ++ tailWord_6032114) baseStart_6032114 baseEnd_6032114 := by
    simpa [prefixWord, tailWord_6032114, baseEnd_6032114] using wordTrace_append hprefix tailTrace_6032114
  have hstable : (prefixWord ++ tailWord_6032114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6032114).length < 2 ^ (prefixWord ++ tailWord_6032114).sum := by decide
  have hdescent : baseEnd_6032114 < baseStart_6032114 := by decide
  rcases family_descends (prefixWord ++ tailWord_6032114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6032117 : List Nat := [1, 3, 6, 1, 1, 11]
def baseStart_6032117 : Nat := 118140960795 + 6032117 * 2 ^ 59
def prefixEnd_6032117 : Nat := 4983230072969 + 3 ^ 40 * 6032117 * 2
def baseEnd_6032117 : Nat := 12746400761963296494635

theorem tailTrace_6032117 : CollatzResearch.WordTrace tailWord_6032117 prefixEnd_6032117 12746400761963296494635 := by
  unfold tailWord_6032117
  simp only [CollatzResearch.WordTrace]
  refine ⟨220009381487677787410014605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146672920991785191606676403 220009381487677787410014605)
  ·
    refine ⟨82503518057879170278755477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 220009381487677787410014605 82503518057879170278755477)
    ·
      refine ⟨3867352408963086106816663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 82503518057879170278755477 3867352408963086106816663)
      ·
        refine ⟨5801028613444629160224995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3867352408963086106816663 5801028613444629160224995)
        ·
          refine ⟨8701542920166943740337493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5801028613444629160224995 8701542920166943740337493)
          ·
            refine ⟨12746400761963296494635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 8701542920166943740337493 12746400761963296494635)
            ·
              rfl

theorem cell23_6032117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 11].length) (baseStart_6032117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6032117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6032117 prefixEnd_6032117 := by exact prefixLift 6032117
  have htrace : WordTrace (prefixWord ++ tailWord_6032117) baseStart_6032117 baseEnd_6032117 := by
    simpa [prefixWord, tailWord_6032117, baseEnd_6032117] using wordTrace_append hprefix tailTrace_6032117
  have hstable : (prefixWord ++ tailWord_6032117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6032117).length < 2 ^ (prefixWord ++ tailWord_6032117).sum := by decide
  have hdescent : baseEnd_6032117 < baseStart_6032117 := by decide
  rcases family_descends (prefixWord ++ tailWord_6032117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6032130 : List Nat := [3, 4, 1, 1, 1, 2, 1, 1, 2, 7]
def baseStart_6032130 : Nat := 118140960795 + 6032130 * 2 ^ 59
def prefixEnd_6032130 : Nat := 4983230072969 + 3 ^ 40 * 6032130 * 2
def baseEnd_6032130 : Nat := 1032460686801863165777915

theorem tailTrace_6032130 : CollatzResearch.WordTrace tailWord_6032130 prefixEnd_6032130 1032460686801863165777915 := by
  unfold tailWord_6032130
  simp only [CollatzResearch.WordTrace]
  refine ⟨55002463909157672657559461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146673237091087127086825229 55002463909157672657559461)
  ·
    refine ⟨10312961982967063623292399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55002463909157672657559461 10312961982967063623292399)
    ·
      refine ⟨15469442974450595434938599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10312961982967063623292399 15469442974450595434938599)
      ·
        refine ⟨23204164461675893152407899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15469442974450595434938599 23204164461675893152407899)
        ·
          refine ⟨34806246692513839728611849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23204164461675893152407899 34806246692513839728611849)
          ·
            refine ⟨26104685019385379796458887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34806246692513839728611849 26104685019385379796458887)
            ·
              refine ⟨39157027529078069694688331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26104685019385379796458887 39157027529078069694688331)
              ·
                refine ⟨58735541293617104542032497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39157027529078069694688331 58735541293617104542032497)
                ·
                  refine ⟨44051655970212828406524373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58735541293617104542032497 44051655970212828406524373)
                  ·
                    refine ⟨1032460686801863165777915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44051655970212828406524373 1032460686801863165777915)
                    ·
                      rfl

theorem cell23_6032130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 1, 2, 7].length) (baseStart_6032130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6032130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6032130 prefixEnd_6032130 := by exact prefixLift 6032130
  have htrace : WordTrace (prefixWord ++ tailWord_6032130) baseStart_6032130 baseEnd_6032130 := by
    simpa [prefixWord, tailWord_6032130, baseEnd_6032130] using wordTrace_append hprefix tailTrace_6032130
  have hstable : (prefixWord ++ tailWord_6032130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6032130).length < 2 ^ (prefixWord ++ tailWord_6032130).sum := by decide
  have hdescent : baseEnd_6032130 < baseStart_6032130 := by decide
  rcases family_descends (prefixWord ++ tailWord_6032130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6032143 : List Nat := [1, 1, 2, 1, 1, 1, 7, 1, 2, 6]
def baseStart_6032143 : Nat := 118140960795 + 6032143 * 2 ^ 59
def prefixEnd_6032143 : Nat := 4983230072969 + 3 ^ 40 * 6032143 * 2
def baseEnd_6032143 : Nat := 1032462911884699315490395

theorem tailTrace_6032143 : CollatzResearch.WordTrace tailWord_6032143 prefixEnd_6032143 1032462911884699315490395 := by
  unfold tailWord_6032143
  simp only [CollatzResearch.WordTrace]
  refine ⟨220010329785583593850461083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146673553190389062566974055 220010329785583593850461083)
  ·
    refine ⟨330015494678375390775691625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220010329785583593850461083 330015494678375390775691625)
    ·
      refine ⟨247511621008781543081768719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 330015494678375390775691625 247511621008781543081768719)
      ·
        refine ⟨371267431513172314622653079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 247511621008781543081768719 371267431513172314622653079)
        ·
          refine ⟨556901147269758471933979619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 371267431513172314622653079 556901147269758471933979619)
          ·
            refine ⟨835351720904637707900969429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 556901147269758471933979619 835351720904637707900969429)
            ·
              refine ⟨19578555958702446278928971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 835351720904637707900969429 19578555958702446278928971)
              ·
                refine ⟨29367833938053669418393457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19578555958702446278928971 29367833938053669418393457)
                ·
                  refine ⟨22025875453540252063795093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29367833938053669418393457 22025875453540252063795093)
                  ·
                    refine ⟨1032462911884699315490395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22025875453540252063795093 1032462911884699315490395)
                    ·
                      rfl

theorem cell23_6032143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7, 1, 2, 6].length) (baseStart_6032143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6032143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6032143 prefixEnd_6032143 := by exact prefixLift 6032143
  have htrace : WordTrace (prefixWord ++ tailWord_6032143) baseStart_6032143 baseEnd_6032143 := by
    simpa [prefixWord, tailWord_6032143, baseEnd_6032143] using wordTrace_append hprefix tailTrace_6032143
  have hstable : (prefixWord ++ tailWord_6032143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6032143).length < 2 ^ (prefixWord ++ tailWord_6032143).sum := by decide
  have hdescent : baseEnd_6032143 < baseStart_6032143 := by decide
  rcases family_descends (prefixWord ++ tailWord_6032143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6032153 : List Nat := [1, 2, 1, 2, 1, 1, 1, 6, 2, 1, 5]
def baseStart_6032153 : Nat := 118140960795 + 6032153 * 2 ^ 59
def prefixEnd_6032153 : Nat := 4983230072969 + 3 ^ 40 * 6032153 * 2
def baseEnd_6032153 : Nat := 3097393870460642907346139

theorem tailTrace_6032153 : CollatzResearch.WordTrace tailWord_6032153 prefixEnd_6032153 3097393870460642907346139 := by
  unfold tailWord_6032153
  simp only [CollatzResearch.WordTrace]
  refine ⟨220010694515547365558325113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146673796343698243705550075 220010694515547365558325113)
  ·
    refine ⟨165008020886660524168743835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220010694515547365558325113 165008020886660524168743835)
    ·
      refine ⟨247512031329990786253115753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165008020886660524168743835 247512031329990786253115753)
      ·
        refine ⟨185634023497493089689836815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 247512031329990786253115753 185634023497493089689836815)
        ·
          refine ⟨278451035246239634534755223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185634023497493089689836815 278451035246239634534755223)
          ·
            refine ⟨417676552869359451802132835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 278451035246239634534755223 417676552869359451802132835)
            ·
              refine ⟨626514829304039177703199253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 417676552869359451802132835 626514829304039177703199253)
              ·
                refine ⟨29367882623626836454837465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 626514829304039177703199253 29367882623626836454837465)
                ·
                  refine ⟨22025911967720127341128099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29367882623626836454837465 22025911967720127341128099)
                  ·
                    refine ⟨33038867951580191011692149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22025911967720127341128099 33038867951580191011692149)
                    ·
                      refine ⟨3097393870460642907346139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33038867951580191011692149 3097393870460642907346139)
                      ·
                        rfl

theorem cell23_6032153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 6, 2, 1, 5].length) (baseStart_6032153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6032153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6032153 prefixEnd_6032153 := by exact prefixLift 6032153
  have htrace : WordTrace (prefixWord ++ tailWord_6032153) baseStart_6032153 baseEnd_6032153 := by
    simpa [prefixWord, tailWord_6032153, baseEnd_6032153] using wordTrace_append hprefix tailTrace_6032153
  have hstable : (prefixWord ++ tailWord_6032153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6032153).length < 2 ^ (prefixWord ++ tailWord_6032153).sum := by decide
  have hdescent : baseEnd_6032153 < baseStart_6032153 := by decide
  rcases family_descends (prefixWord ++ tailWord_6032153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6032163 : List Nat := [1, 1, 1, 4, 2, 1, 1, 1, 3, 4, 4]
def baseStart_6032163 : Nat := 118140960795 + 6032163 * 2 ^ 59
def prefixEnd_6032163 : Nat := 4983230072969 + 3 ^ 40 * 6032163 * 2
def baseEnd_6032163 : Nat := 3097399005267187868221093

theorem tailTrace_6032163 : CollatzResearch.WordTrace tailWord_6032163 prefixEnd_6032163 3097399005267187868221093 := by
  unfold tailWord_6032163
  simp only [CollatzResearch.WordTrace]
  refine ⟨220011059245511137266189143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146674039497007424844126095 220011059245511137266189143)
  ·
    refine ⟨330016588868266705899283715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220011059245511137266189143 330016588868266705899283715)
    ·
      refine ⟨495024883302400058848925573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 330016588868266705899283715 495024883302400058848925573)
      ·
        refine ⟨92817165619200011034173545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 495024883302400058848925573 92817165619200011034173545)
        ·
          refine ⟨69612874214400008275630159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92817165619200011034173545 69612874214400008275630159)
          ·
            refine ⟨104419311321600012413445239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69612874214400008275630159 104419311321600012413445239)
            ·
              refine ⟨156628966982400018620167859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104419311321600012413445239 156628966982400018620167859)
              ·
                refine ⟨234943450473600027930251789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 156628966982400018620167859 234943450473600027930251789)
                ·
                  refine ⟨88103793927600010473844421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 234943450473600027930251789 88103793927600010473844421)
                  ·
                    refine ⟨16519461361425001963845829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 88103793927600010473844421 16519461361425001963845829)
                    ·
                      refine ⟨3097399005267187868221093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16519461361425001963845829 3097399005267187868221093)
                      ·
                        rfl

theorem cell23_6032163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 1, 3, 4, 4].length) (baseStart_6032163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6032163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6032163 prefixEnd_6032163 := by exact prefixLift 6032163
  have htrace : WordTrace (prefixWord ++ tailWord_6032163) baseStart_6032163 baseEnd_6032163 := by
    simpa [prefixWord, tailWord_6032163, baseEnd_6032163] using wordTrace_append hprefix tailTrace_6032163
  have hstable : (prefixWord ++ tailWord_6032163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6032163).length < 2 ^ (prefixWord ++ tailWord_6032163).sum := by decide
  have hdescent : baseEnd_6032163 < baseStart_6032163 := by decide
  rcases family_descends (prefixWord ++ tailWord_6032163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6032200 : List Nat := [2, 1, 3, 1, 1, 3, 1, 3, 2, 3, 3]
def baseStart_6032200 : Nat := 118140960795 + 6032200 * 2 ^ 59
def prefixEnd_6032200 : Nat := 4983230072969 + 3 ^ 40 * 6032200 * 2
def baseEnd_6032200 : Nat := 3097418004051404223458423

theorem tailTrace_6032200 : CollatzResearch.WordTrace tailWord_6032200 prefixEnd_6032200 3097418004051404223458423 := by
  unfold tailWord_6032200
  simp only [CollatzResearch.WordTrace]
  refine ⟨110006204373188546292643027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146674939164251395056857369 110006204373188546292643027)
  ·
    refine ⟨165009306559782819438964541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110006204373188546292643027 165009306559782819438964541)
    ·
      refine ⟨61878489959918557289611703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 165009306559782819438964541 61878489959918557289611703)
      ·
        refine ⟨92817734939877835934417555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61878489959918557289611703 92817734939877835934417555)
        ·
          refine ⟨139226602409816753901626333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92817734939877835934417555 139226602409816753901626333)
          ·
            refine ⟨52209975903681282713109875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 139226602409816753901626333 52209975903681282713109875)
            ·
              refine ⟨78314963855521924069664813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52209975903681282713109875 78314963855521924069664813)
              ·
                refine ⟨29368111445820721526124305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78314963855521924069664813 29368111445820721526124305)
                ·
                  refine ⟨22026083584365541144593229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29368111445820721526124305 22026083584365541144593229)
                  ·
                    refine ⟨8259781344137077929222461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22026083584365541144593229 8259781344137077929222461)
                    ·
                      refine ⟨3097418004051404223458423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8259781344137077929222461 3097418004051404223458423)
                      ·
                        rfl

theorem cell23_6032200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 3, 2, 3, 3].length) (baseStart_6032200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6032200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6032200 prefixEnd_6032200 := by exact prefixLift 6032200
  have htrace : WordTrace (prefixWord ++ tailWord_6032200) baseStart_6032200 baseEnd_6032200 := by
    simpa [prefixWord, tailWord_6032200, baseEnd_6032200] using wordTrace_append hprefix tailTrace_6032200
  have hstable : (prefixWord ++ tailWord_6032200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6032200).length < 2 ^ (prefixWord ++ tailWord_6032200).sum := by decide
  have hdescent : baseEnd_6032200 < baseStart_6032200 := by decide
  rcases family_descends (prefixWord ++ tailWord_6032200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6032201 : List Nat := [1, 2, 1, 1, 2, 6, 3, 1, 2, 2, 2]
def baseStart_6032201 : Nat := 118140960795 + 6032201 * 2 ^ 59
def prefixEnd_6032201 : Nat := 4983230072969 + 3 ^ 40 * 6032201 * 2
def baseEnd_6032201 : Nat := 3097418517532058719545919

theorem tailTrace_6032201 : CollatzResearch.WordTrace tailWord_6032201 prefixEnd_6032201 3097418517532058719545919 := by
  unfold tailWord_6032201
  simp only [CollatzResearch.WordTrace]
  refine ⟨220012445219373469756072457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146674963479582313170714971 220012445219373469756072457)
  ·
    refine ⟨165009333914530102317054343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220012445219373469756072457 165009333914530102317054343)
    ·
      refine ⟨247514000871795153475581515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165009333914530102317054343 247514000871795153475581515)
      ·
        refine ⟨371271001307692730213372273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 247514000871795153475581515 371271001307692730213372273)
        ·
          refine ⟨278453250980769547660029205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 371271001307692730213372273 278453250980769547660029205)
          ·
            refine ⟨13052496139723572546563869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 278453250980769547660029205 13052496139723572546563869)
            ·
              refine ⟨4894686052396339704961451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13052496139723572546563869 4894686052396339704961451)
              ·
                refine ⟨7342029078594509557442177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4894686052396339704961451 7342029078594509557442177)
                ·
                  refine ⟨5506521808945882168081633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7342029078594509557442177 5506521808945882168081633)
                  ·
                    refine ⟨4129891356709411626061225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5506521808945882168081633 4129891356709411626061225)
                    ·
                      refine ⟨3097418517532058719545919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4129891356709411626061225 3097418517532058719545919)
                      ·
                        rfl

theorem cell23_6032201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 3, 1, 2, 2, 2].length) (baseStart_6032201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6032201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6032201 prefixEnd_6032201 := by exact prefixLift 6032201
  have htrace : WordTrace (prefixWord ++ tailWord_6032201) baseStart_6032201 baseEnd_6032201 := by
    simpa [prefixWord, tailWord_6032201, baseEnd_6032201] using wordTrace_append hprefix tailTrace_6032201
  have hstable : (prefixWord ++ tailWord_6032201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6032201).length < 2 ^ (prefixWord ++ tailWord_6032201).sum := by decide
  have hdescent : baseEnd_6032201 < baseStart_6032201 := by decide
  rcases family_descends (prefixWord ++ tailWord_6032201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6032240 : List Nat := [2, 1, 1, 1, 4, 1, 3, 1, 4, 1, 4]
def baseStart_6032240 : Nat := 118140960795 + 6032240 * 2 ^ 59
def prefixEnd_6032240 : Nat := 4983230072969 + 3 ^ 40 * 6032240 * 2
def baseEnd_6032240 : Nat := 3097438543277584066958239

theorem tailTrace_6032240 : CollatzResearch.WordTrace tailWord_6032240 prefixEnd_6032240 3097438543277584066958239 := by
  unfold tailWord_6032240
  simp only [CollatzResearch.WordTrace]
  refine ⟨110006933833116089708371087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146675911777488119611161449 110006933833116089708371087)
  ·
    refine ⟨165010400749674134562556631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110006933833116089708371087 165010400749674134562556631)
    ·
      refine ⟨247515601124511201843834947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165010400749674134562556631 247515601124511201843834947)
      ·
        refine ⟨371273401686766802765752421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 247515601124511201843834947 371273401686766802765752421)
        ·
          refine ⟨69613762816268775518578579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 371273401686766802765752421 69613762816268775518578579)
          ·
            refine ⟨104420644224403163277867869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69613762816268775518578579 104420644224403163277867869)
            ·
              refine ⟨39157741584151186229200451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 104420644224403163277867869 39157741584151186229200451)
              ·
                refine ⟨58736612376226779343800677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39157741584151186229200451 58736612376226779343800677)
                ·
                  refine ⟨11013114820542521126962627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 58736612376226779343800677 11013114820542521126962627)
                  ·
                    refine ⟨16519672230813781690443941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11013114820542521126962627 16519672230813781690443941)
                    ·
                      refine ⟨3097438543277584066958239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16519672230813781690443941 3097438543277584066958239)
                      ·
                        rfl

theorem cell23_6032240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 1, 4, 1, 4].length) (baseStart_6032240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6032240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6032240 prefixEnd_6032240 := by exact prefixLift 6032240
  have htrace : WordTrace (prefixWord ++ tailWord_6032240) baseStart_6032240 baseEnd_6032240 := by
    simpa [prefixWord, tailWord_6032240, baseEnd_6032240] using wordTrace_append hprefix tailTrace_6032240
  have hstable : (prefixWord ++ tailWord_6032240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6032240).length < 2 ^ (prefixWord ++ tailWord_6032240).sum := by decide
  have hdescent : baseEnd_6032240 < baseStart_6032240 := by decide
  rcases family_descends (prefixWord ++ tailWord_6032240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6032277 : List Nat := [1, 3, 2, 1, 1, 4, 1, 3, 2, 2, 3]
def baseStart_6032277 : Nat := 118140960795 + 6032277 * 2 ^ 59
def prefixEnd_6032277 : Nat := 4983230072969 + 3 ^ 40 * 6032277 * 2
def baseEnd_6032277 : Nat := 3097457542061800422195569

theorem tailTrace_6032277 : CollatzResearch.WordTrace tailWord_6032277 prefixEnd_6032277 3097457542061800422195569 := by
  unfold tailWord_6032277
  simp only [CollatzResearch.WordTrace]
  refine ⟨220015217167098134735839085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146676811444732089823892723 220015217167098134735839085)
  ·
    refine ⟨82505706437661800525939657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 220015217167098134735839085 82505706437661800525939657)
    ·
      refine ⟨61879279828246350394454743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82505706437661800525939657 61879279828246350394454743)
      ·
        refine ⟨92818919742369525591682115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61879279828246350394454743 92818919742369525591682115)
        ·
          refine ⟨139228379613554288387523173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92818919742369525591682115 139228379613554288387523173)
          ·
            refine ⟨26105321177541429072660595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 139228379613554288387523173 26105321177541429072660595)
            ·
              refine ⟨39157981766312143608990893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26105321177541429072660595 39157981766312143608990893)
              ·
                refine ⟨14684243162367053853371585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39157981766312143608990893 14684243162367053853371585)
                ·
                  refine ⟨11013182371775290390028689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14684243162367053853371585 11013182371775290390028689)
                  ·
                    refine ⟨8259886778831467792521517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11013182371775290390028689 8259886778831467792521517)
                    ·
                      refine ⟨3097457542061800422195569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8259886778831467792521517 3097457542061800422195569)
                      ·
                        rfl

theorem cell23_6032277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 3, 2, 2, 3].length) (baseStart_6032277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6032277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6032277 prefixEnd_6032277 := by exact prefixLift 6032277
  have htrace : WordTrace (prefixWord ++ tailWord_6032277) baseStart_6032277 baseEnd_6032277 := by
    simpa [prefixWord, tailWord_6032277, baseEnd_6032277] using wordTrace_append hprefix tailTrace_6032277
  have hstable : (prefixWord ++ tailWord_6032277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6032277).length < 2 ^ (prefixWord ++ tailWord_6032277).sum := by decide
  have hdescent : baseEnd_6032277 < baseStart_6032277 := by decide
  rcases family_descends (prefixWord ++ tailWord_6032277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6032334 : List Nat := [4, 1, 1, 1, 2, 4, 1, 1, 1, 5, 2]
def baseStart_6032334 : Nat := 118140960795 + 6032334 * 2 ^ 59
def prefixEnd_6032334 : Nat := 4983230072969 + 3 ^ 40 * 6032334 * 2
def baseEnd_6032334 : Nat := 3097486810459106699182807

theorem tailTrace_6032334 : CollatzResearch.WordTrace tailWord_6032334 prefixEnd_6032334 3097486810459106699182807 := by
  unfold tailWord_6032334
  simp only [CollatzResearch.WordTrace]
  refine ⟨27502162015986454183833007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 146678197418594422313776037 27502162015986454183833007)
  ·
    refine ⟨41253243023979681275749511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27502162015986454183833007 41253243023979681275749511)
    ·
      refine ⟨61879864535969521913624267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41253243023979681275749511 61879864535969521913624267)
      ·
        refine ⟨92819796803954282870436401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61879864535969521913624267 92819796803954282870436401)
        ·
          refine ⟨69614847602965712152827301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92819796803954282870436401 69614847602965712152827301)
          ·
            refine ⟨13052783925556071028655119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 69614847602965712152827301 13052783925556071028655119)
            ·
              refine ⟨19579175888334106542982679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13052783925556071028655119 19579175888334106542982679)
              ·
                refine ⟨29368763832501159814474019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19579175888334106542982679 29368763832501159814474019)
                ·
                  refine ⟨44053145748751739721711029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29368763832501159814474019 44053145748751739721711029)
                  ·
                    refine ⟨4129982413945475598910409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 44053145748751739721711029 4129982413945475598910409)
                    ·
                      refine ⟨3097486810459106699182807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4129982413945475598910409 3097486810459106699182807)
                      ·
                        rfl

theorem cell23_6032334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 1, 1, 1, 5, 2].length) (baseStart_6032334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6032334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6032334 prefixEnd_6032334 := by exact prefixLift 6032334
  have htrace : WordTrace (prefixWord ++ tailWord_6032334) baseStart_6032334 baseEnd_6032334 := by
    simpa [prefixWord, tailWord_6032334, baseEnd_6032334] using wordTrace_append hprefix tailTrace_6032334
  have hstable : (prefixWord ++ tailWord_6032334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6032334).length < 2 ^ (prefixWord ++ tailWord_6032334).sum := by decide
  have hdescent : baseEnd_6032334 < baseStart_6032334 := by decide
  rcases family_descends (prefixWord ++ tailWord_6032334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6032344 : List Nat := [2, 1, 2, 2, 2, 3, 4, 1, 1, 5]
def baseStart_6032344 : Nat := 118140960795 + 6032344 * 2 ^ 59
def prefixEnd_6032344 : Nat := 4983230072969 + 3 ^ 40 * 6032344 * 2
def baseEnd_6032344 : Nat := 1032497315088550553352587

theorem tailTrace_6032344 : CollatzResearch.WordTrace tailWord_6032344 prefixEnd_6032344 1032497315088550553352587 := by
  unfold tailWord_6032344
  simp only [CollatzResearch.WordTrace]
  refine ⟨110008830428927702589264043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146678440571903603452352057 110008830428927702589264043)
  ·
    refine ⟨165013245643391553883896065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110008830428927702589264043 165013245643391553883896065)
    ·
      refine ⟨123759934232543665412922049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165013245643391553883896065 123759934232543665412922049)
      ·
        refine ⟨92819950674407749059691537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123759934232543665412922049 92819950674407749059691537)
        ·
          refine ⟨69614963005805811794768653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92819950674407749059691537 69614963005805811794768653)
          ·
            refine ⟨26105611127177179423038245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69614963005805811794768653 26105611127177179423038245)
            ·
              refine ⟨4894802086345721141819671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26105611127177179423038245 4894802086345721141819671)
              ·
                refine ⟨7342203129518581712729507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4894802086345721141819671 7342203129518581712729507)
                ·
                  refine ⟨11013304694277872569094261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7342203129518581712729507 11013304694277872569094261)
                  ·
                    refine ⟨1032497315088550553352587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11013304694277872569094261 1032497315088550553352587)
                    ·
                      rfl

theorem cell23_6032344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 4, 1, 1, 5].length) (baseStart_6032344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6032344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6032344 prefixEnd_6032344 := by exact prefixLift 6032344
  have htrace : WordTrace (prefixWord ++ tailWord_6032344) baseStart_6032344 baseEnd_6032344 := by
    simpa [prefixWord, tailWord_6032344, baseEnd_6032344] using wordTrace_append hprefix tailTrace_6032344
  have hstable : (prefixWord ++ tailWord_6032344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6032344).length < 2 ^ (prefixWord ++ tailWord_6032344).sum := by decide
  have hdescent : baseEnd_6032344 < baseStart_6032344 := by decide
  rcases family_descends (prefixWord ++ tailWord_6032344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6032367 : List Nat := [1, 1, 2, 1, 4, 4, 1, 2, 1, 1, 5]
def baseStart_6032367 : Nat := 118140960795 + 6032367 * 2 ^ 59
def prefixEnd_6032367 : Nat := 4983230072969 + 3 ^ 40 * 6032367 * 2
def baseEnd_6032367 : Nat := 3097503755320705070070155

theorem tailTrace_6032367 : CollatzResearch.WordTrace tailWord_6032367 prefixEnd_6032367 3097503755320705070070155 := by
  unfold tailWord_6032367
  simp only [CollatzResearch.WordTrace]
  refine ⟨220018499736772080106615355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146678999824514720071076903 220018499736772080106615355)
  ·
    refine ⟨330027749605158120159923033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220018499736772080106615355 330027749605158120159923033)
    ·
      refine ⟨247520812203868590119942275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 330027749605158120159923033 247520812203868590119942275)
      ·
        refine ⟨371281218305802885179913413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 247520812203868590119942275 371281218305802885179913413)
        ·
          refine ⟨69615228432338040971233765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 371281218305802885179913413 69615228432338040971233765)
          ·
            refine ⟨13052855331063382682106331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 69615228432338040971233765 13052855331063382682106331)
            ·
              refine ⟨19579282996595074023159497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13052855331063382682106331 19579282996595074023159497)
              ·
                refine ⟨14684462247446305517369623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19579282996595074023159497 14684462247446305517369623)
                ·
                  refine ⟨22026693371169458276054435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14684462247446305517369623 22026693371169458276054435)
                  ·
                    refine ⟨33040040056754187414081653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22026693371169458276054435 33040040056754187414081653)
                    ·
                      refine ⟨3097503755320705070070155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33040040056754187414081653 3097503755320705070070155)
                      ·
                        rfl

theorem cell23_6032367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 1, 2, 1, 1, 5].length) (baseStart_6032367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6032367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6032367 prefixEnd_6032367 := by exact prefixLift 6032367
  have htrace : WordTrace (prefixWord ++ tailWord_6032367) baseStart_6032367 baseEnd_6032367 := by
    simpa [prefixWord, tailWord_6032367, baseEnd_6032367] using wordTrace_append hprefix tailTrace_6032367
  have hstable : (prefixWord ++ tailWord_6032367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6032367).length < 2 ^ (prefixWord ++ tailWord_6032367).sum := by decide
  have hdescent : baseEnd_6032367 < baseStart_6032367 := by decide
  rcases family_descends (prefixWord ++ tailWord_6032367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6032374 : List Nat := [5, 1, 1, 1, 3, 1, 3, 1, 1, 6]
def baseStart_6032374 : Nat := 118140960795 + 6032374 * 2 ^ 59
def prefixEnd_6032374 : Nat := 4983230072969 + 3 ^ 40 * 6032374 * 2
def baseEnd_6032374 : Nat := 1032502449895095514227541

theorem tailTrace_6032374 : CollatzResearch.WordTrace tailWord_6032374 prefixEnd_6032374 1032502449895095514227541 := by
  unfold tailWord_6032374
  simp only [CollatzResearch.WordTrace]
  refine ⟨13751172190484170018882511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 146679170031831146868080117 13751172190484170018882511)
  ·
    refine ⟨20626758285726255028323767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13751172190484170018882511 20626758285726255028323767)
    ·
      refine ⟨30940137428589382542485651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20626758285726255028323767 30940137428589382542485651)
      ·
        refine ⟨46410206142884073813728477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30940137428589382542485651 46410206142884073813728477)
        ·
          refine ⟨17403827303581527680148179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46410206142884073813728477 17403827303581527680148179)
          ·
            refine ⟨26105740955372291520222269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17403827303581527680148179 26105740955372291520222269)
            ·
              refine ⟨9789652858264609320083351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26105740955372291520222269 9789652858264609320083351)
              ·
                refine ⟨14684479287396913980125027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9789652858264609320083351 14684479287396913980125027)
                ·
                  refine ⟨22026718931095370970187541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14684479287396913980125027 22026718931095370970187541)
                  ·
                    refine ⟨1032502449895095514227541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22026718931095370970187541 1032502449895095514227541)
                    ·
                      rfl

theorem cell23_6032374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 3, 1, 1, 6].length) (baseStart_6032374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6032374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6032374 prefixEnd_6032374 := by exact prefixLift 6032374
  have htrace : WordTrace (prefixWord ++ tailWord_6032374) baseStart_6032374 baseEnd_6032374 := by
    simpa [prefixWord, tailWord_6032374, baseEnd_6032374] using wordTrace_append hprefix tailTrace_6032374
  have hstable : (prefixWord ++ tailWord_6032374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6032374).length < 2 ^ (prefixWord ++ tailWord_6032374).sum := by decide
  have hdescent : baseEnd_6032374 < baseStart_6032374 := by decide
  rcases family_descends (prefixWord ++ tailWord_6032374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6032415 : List Nat := [1, 1, 2, 4, 1, 4, 3, 2, 1, 2, 2]
def baseStart_6032415 : Nat := 118140960795 + 6032415 * 2 ^ 59
def prefixEnd_6032415 : Nat := 4983230072969 + 3 ^ 40 * 6032415 * 2
def baseEnd_6032415 : Nat := 3097528402392120882269935

theorem tailTrace_6032415 : CollatzResearch.WordTrace tailWord_6032415 prefixEnd_6032415 3097528402392120882269935 := by
  unfold tailWord_6032415
  simp only [CollatzResearch.WordTrace]
  refine ⟨220020250440598184304362699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146680166960398789536241799 220020250440598184304362699)
  ·
    refine ⟨330030375660897276456544049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220020250440598184304362699 330030375660897276456544049)
    ·
      refine ⟨247522781745672957342408037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 330030375660897276456544049 247522781745672957342408037)
      ·
        refine ⟨46410521577313679501701507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 247522781745672957342408037 46410521577313679501701507)
        ·
          refine ⟨69615782365970519252552261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46410521577313679501701507 69615782365970519252552261)
          ·
            refine ⟨13052959193619472359853549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 69615782365970519252552261 13052959193619472359853549)
            ·
              refine ⟨4894859697607302134945081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13052959193619472359853549 4894859697607302134945081)
              ·
                refine ⟨3671144773205476601208811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4894859697607302134945081 3671144773205476601208811)
                ·
                  refine ⟨5506717159808214901813217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3671144773205476601208811 5506717159808214901813217)
                  ·
                    refine ⟨4130037869856161176359913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5506717159808214901813217 4130037869856161176359913)
                    ·
                      refine ⟨3097528402392120882269935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4130037869856161176359913 3097528402392120882269935)
                      ·
                        rfl

theorem cell23_6032415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 3, 2, 1, 2, 2].length) (baseStart_6032415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6032415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6032415 prefixEnd_6032415 := by exact prefixLift 6032415
  have htrace : WordTrace (prefixWord ++ tailWord_6032415) baseStart_6032415 baseEnd_6032415 := by
    simpa [prefixWord, tailWord_6032415, baseEnd_6032415] using wordTrace_append hprefix tailTrace_6032415
  have hstable : (prefixWord ++ tailWord_6032415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6032415).length < 2 ^ (prefixWord ++ tailWord_6032415).sum := by decide
  have hdescent : baseEnd_6032415 < baseStart_6032415 := by decide
  rcases family_descends (prefixWord ++ tailWord_6032415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6032441 : List Nat := [1, 2, 1, 5, 2, 2, 1, 1, 3, 3, 2]
def baseStart_6032441 : Nat := 118140960795 + 6032441 * 2 ^ 59
def prefixEnd_6032441 : Nat := 4983230072969 + 3 ^ 40 * 6032441 * 2
def baseEnd_6032441 : Nat := 3097541752889137780544815

theorem tailTrace_6032441 : CollatzResearch.WordTrace tailWord_6032441 prefixEnd_6032441 3097541752889137780544815 := by
  unfold tailWord_6032441
  simp only [CollatzResearch.WordTrace]
  refine ⟨220021198738503990744809177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146680799159002660496539451 220021198738503990744809177)
  ·
    refine ⟨165015899053877993058606883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220021198738503990744809177 165015899053877993058606883)
    ·
      refine ⟨247523848580816989587910325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165015899053877993058606883 247523848580816989587910325)
      ·
        refine ⟨23205360804451592773866593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 247523848580816989587910325 23205360804451592773866593)
        ·
          refine ⟨17404020603338694580399945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23205360804451592773866593 17404020603338694580399945)
          ·
            refine ⟨13053015452504020935299959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17404020603338694580399945 13053015452504020935299959)
            ·
              refine ⟨19579523178756031402949939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13053015452504020935299959 19579523178756031402949939)
              ·
                refine ⟨29369284768134047104424909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19579523178756031402949939 29369284768134047104424909)
                ·
                  refine ⟨11013481788050267664159341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29369284768134047104424909 11013481788050267664159341)
                  ·
                    refine ⟨4130055670518850374059753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11013481788050267664159341 4130055670518850374059753)
                    ·
                      refine ⟨3097541752889137780544815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4130055670518850374059753 3097541752889137780544815)
                      ·
                        rfl

theorem cell23_6032441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 1, 1, 3, 3, 2].length) (baseStart_6032441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6032441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6032441 prefixEnd_6032441 := by exact prefixLift 6032441
  have htrace : WordTrace (prefixWord ++ tailWord_6032441) baseStart_6032441 baseEnd_6032441 := by
    simpa [prefixWord, tailWord_6032441, baseEnd_6032441] using wordTrace_append hprefix tailTrace_6032441
  have hstable : (prefixWord ++ tailWord_6032441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6032441).length < 2 ^ (prefixWord ++ tailWord_6032441).sum := by decide
  have hdescent : baseEnd_6032441 < baseStart_6032441 := by decide
  rcases family_descends (prefixWord ++ tailWord_6032441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6032494 : List Nat := [4, 1, 2, 2, 1, 3, 1, 2, 7]
def baseStart_6032494 : Nat := 118140960795 + 6032494 * 2 ^ 59
def prefixEnd_6032494 : Nat := 4983230072969 + 3 ^ 40 * 6032494 * 2
def baseEnd_6032494 : Nat := 344174329707091785909119

theorem tailTrace_6032494 : CollatzResearch.WordTrace tailWord_6032494 prefixEnd_6032494 344174329707091785909119 := by
  unfold tailWord_6032494
  simp only [CollatzResearch.WordTrace]
  refine ⟨27502891475913997599561067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 146682087871541320530992357 27502891475913997599561067)
  ·
    refine ⟨41254337213870996399341601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27502891475913997599561067 41254337213870996399341601)
    ·
      refine ⟨30940752910403247299506201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41254337213870996399341601 30940752910403247299506201)
      ·
        refine ⟨23205564682802435474629651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30940752910403247299506201 23205564682802435474629651)
        ·
          refine ⟨34808347024203653211944477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23205564682802435474629651 34808347024203653211944477)
          ·
            refine ⟨13053130134076369954479179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34808347024203653211944477 13053130134076369954479179)
            ·
              refine ⟨19579695201114554931718769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13053130134076369954479179 19579695201114554931718769)
              ·
                refine ⟨14684771400835916198789077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19579695201114554931718769 14684771400835916198789077)
                ·
                  refine ⟨344174329707091785909119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14684771400835916198789077 344174329707091785909119)
                  ·
                    rfl

theorem cell23_6032494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 1, 2, 7].length) (baseStart_6032494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6032494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6032494 prefixEnd_6032494 := by exact prefixLift 6032494
  have htrace : WordTrace (prefixWord ++ tailWord_6032494) baseStart_6032494 baseEnd_6032494 := by
    simpa [prefixWord, tailWord_6032494, baseEnd_6032494] using wordTrace_append hprefix tailTrace_6032494
  have hstable : (prefixWord ++ tailWord_6032494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6032494).length < 2 ^ (prefixWord ++ tailWord_6032494).sum := by decide
  have hdescent : baseEnd_6032494 < baseStart_6032494 := by decide
  rcases family_descends (prefixWord ++ tailWord_6032494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6032567 : List Nat := [1, 1, 3, 1, 4, 1, 1, 1, 10]
def baseStart_6032567 : Nat := 118140960795 + 6032567 * 2 ^ 59
def prefixEnd_6032567 : Nat := 4983230072969 + 3 ^ 40 * 6032567 * 2
def baseEnd_6032567 : Nat := 344178494605733809729915

theorem tailTrace_6032567 : CollatzResearch.WordTrace tailWord_6032567 prefixEnd_6032567 344178494605733809729915 := by
  unfold tailWord_6032567
  simp only [CollatzResearch.WordTrace]
  refine ⟨220025794336047514263895955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146683862890698342842597303 220025794336047514263895955)
  ·
    refine ⟨330038691504071271395843933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220025794336047514263895955 330038691504071271395843933)
    ·
      refine ⟨123764509314026726773441475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 330038691504071271395843933 123764509314026726773441475)
      ·
        refine ⟨185646763971040090160162213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123764509314026726773441475 185646763971040090160162213)
        ·
          refine ⟨34808768244570016905030415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 185646763971040090160162213 34808768244570016905030415)
          ·
            refine ⟨52213152366855025357545623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34808768244570016905030415 52213152366855025357545623)
            ·
              refine ⟨78319728550282538036318435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52213152366855025357545623 78319728550282538036318435)
              ·
                refine ⟨117479592825423807054477653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78319728550282538036318435 117479592825423807054477653)
                ·
                  refine ⟨344178494605733809729915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 117479592825423807054477653 344178494605733809729915)
                  ·
                    rfl

theorem cell23_6032567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 1, 10].length) (baseStart_6032567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6032567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6032567 prefixEnd_6032567 := by exact prefixLift 6032567
  have htrace : WordTrace (prefixWord ++ tailWord_6032567) baseStart_6032567 baseEnd_6032567 := by
    simpa [prefixWord, tailWord_6032567, baseEnd_6032567] using wordTrace_append hprefix tailTrace_6032567
  have hstable : (prefixWord ++ tailWord_6032567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6032567).length < 2 ^ (prefixWord ++ tailWord_6032567).sum := by decide
  have hdescent : baseEnd_6032567 < baseStart_6032567 := by decide
  rcases family_descends (prefixWord ++ tailWord_6032567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6032571 : List Nat := [1, 1, 1, 1, 1, 2, 4, 7, 1, 4]
def baseStart_6032571 : Nat := 118140960795 + 6032571 * 2 ^ 59
def prefixEnd_6032571 : Nat := 4983230072969 + 3 ^ 40 * 6032571 * 2
def baseEnd_6032571 : Nat := 1032536168458074090639739

theorem tailTrace_6032571 : CollatzResearch.WordTrace tailWord_6032571 prefixEnd_6032571 1032536168458074090639739 := by
  unfold tailWord_6032571
  simp only [CollatzResearch.WordTrace]
  refine ⟨220025940228033022947041567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146683960152022015298027711 220025940228033022947041567)
  ·
    refine ⟨330038910342049534420562351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220025940228033022947041567 330038910342049534420562351)
    ·
      refine ⟨495058365513074301630843527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 330038910342049534420562351 495058365513074301630843527)
      ·
        refine ⟨742587548269611452446265291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 495058365513074301630843527 742587548269611452446265291)
        ·
          refine ⟨1113881322404417178669397937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 742587548269611452446265291 1113881322404417178669397937)
          ·
            refine ⟨835410991803312884002048453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1113881322404417178669397937 835410991803312884002048453)
            ·
              refine ⟨156639560963121165750384085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 835410991803312884002048453 156639560963121165750384085)
              ·
                refine ⟨3671239710073152322274627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 156639560963121165750384085 3671239710073152322274627)
                ·
                  refine ⟨5506859565109728483411941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3671239710073152322274627 5506859565109728483411941)
                  ·
                    refine ⟨1032536168458074090639739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5506859565109728483411941 1032536168458074090639739)
                    ·
                      rfl

theorem cell23_6032571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 7, 1, 4].length) (baseStart_6032571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6032571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6032571 prefixEnd_6032571 := by exact prefixLift 6032571
  have htrace : WordTrace (prefixWord ++ tailWord_6032571) baseStart_6032571 baseEnd_6032571 := by
    simpa [prefixWord, tailWord_6032571, baseEnd_6032571] using wordTrace_append hprefix tailTrace_6032571
  have hstable : (prefixWord ++ tailWord_6032571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6032571).length < 2 ^ (prefixWord ++ tailWord_6032571).sum := by decide
  have hdescent : baseEnd_6032571 < baseStart_6032571 := by decide
  rcases family_descends (prefixWord ++ tailWord_6032571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6032587 : List Nat := [1, 1, 1, 1, 3, 2, 2, 3, 1, 2, 6]
def baseStart_6032587 : Nat := 118140960795 + 6032587 * 2 ^ 59
def prefixEnd_6032587 : Nat := 4983230072969 + 3 ^ 40 * 6032587 * 2
def baseEnd_6032587 : Nat := 3097616721064694209319143

theorem tailTrace_6032587 : CollatzResearch.WordTrace tailWord_6032587 prefixEnd_6032587 3097616721064694209319143 := by
  unfold tailWord_6032587
  simp only [CollatzResearch.WordTrace]
  refine ⟨220026523795975057679624015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146684349197316705119749343 220026523795975057679624015)
  ·
    refine ⟨330039785693962586519436023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220026523795975057679624015 330039785693962586519436023)
    ·
      refine ⟨495059678540943879779154035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 330039785693962586519436023 495059678540943879779154035)
      ·
        refine ⟨742589517811415819668731053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 495059678540943879779154035 742589517811415819668731053)
        ·
          refine ⟨278471069179280932375774145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 742589517811415819668731053 278471069179280932375774145)
          ·
            refine ⟨208853301884460699281830609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 278471069179280932375774145 208853301884460699281830609)
            ·
              refine ⟨156639976413345524461372957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 208853301884460699281830609 156639976413345524461372957)
              ·
                refine ⟨58739991155004571673014859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 156639976413345524461372957 58739991155004571673014859)
                ·
                  refine ⟨88109986732506857509522289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58739991155004571673014859 88109986732506857509522289)
                  ·
                    refine ⟨66082490049380143132141717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 88109986732506857509522289 66082490049380143132141717)
                    ·
                      refine ⟨3097616721064694209319143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 66082490049380143132141717 3097616721064694209319143)
                      ·
                        rfl

theorem cell23_6032587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 3, 1, 2, 6].length) (baseStart_6032587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6032587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6032587 prefixEnd_6032587 := by exact prefixLift 6032587
  have htrace : WordTrace (prefixWord ++ tailWord_6032587) baseStart_6032587 baseEnd_6032587 := by
    simpa [prefixWord, tailWord_6032587, baseEnd_6032587] using wordTrace_append hprefix tailTrace_6032587
  have hstable : (prefixWord ++ tailWord_6032587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6032587).length < 2 ^ (prefixWord ++ tailWord_6032587).sum := by decide
  have hdescent : baseEnd_6032587 < baseStart_6032587 := by decide
  rcases family_descends (prefixWord ++ tailWord_6032587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6032668 : List Nat := [2, 2, 3, 1, 1, 1, 3, 1, 5, 2, 2]
def baseStart_6032668 : Nat := 118140960795 + 6032668 * 2 ^ 59
def prefixEnd_6032668 : Nat := 4983230072969 + 3 ^ 40 * 6032668 * 2
def baseEnd_6032668 : Nat := 3097658312997708392406271

theorem tailTrace_6032668 : CollatzResearch.WordTrace tailWord_6032668 prefixEnd_6032668 3097658312997708392406271 := by
  unfold tailWord_6032668
  simp only [CollatzResearch.WordTrace]
  refine ⟨110014739054340804256661329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146686318739121072342215105 110014739054340804256661329)
  ·
    refine ⟨82511054290755603192495997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110014739054340804256661329 82511054290755603192495997)
    ·
      refine ⟨30941645359033351197185999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82511054290755603192495997 30941645359033351197185999)
      ·
        refine ⟨46412468038550026795778999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30941645359033351197185999 46412468038550026795778999)
        ·
          refine ⟨69618702057825040193668499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46412468038550026795778999 69618702057825040193668499)
          ·
            refine ⟨104428053086737560290502749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69618702057825040193668499 104428053086737560290502749)
            ·
              refine ⟨39160519907526585108938531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 104428053086737560290502749 39160519907526585108938531)
              ·
                refine ⟨58740779861289877663407797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39160519907526585108938531 58740779861289877663407797)
                ·
                  refine ⟨5506948111995926030944481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 58740779861289877663407797 5506948111995926030944481)
                  ·
                    refine ⟨4130211083996944523208361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5506948111995926030944481 4130211083996944523208361)
                    ·
                      refine ⟨3097658312997708392406271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4130211083996944523208361 3097658312997708392406271)
                      ·
                        rfl

theorem cell23_6032668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 1, 5, 2, 2].length) (baseStart_6032668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6032668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6032668 prefixEnd_6032668 := by exact prefixLift 6032668
  have htrace : WordTrace (prefixWord ++ tailWord_6032668) baseStart_6032668 baseEnd_6032668 := by
    simpa [prefixWord, tailWord_6032668, baseEnd_6032668] using wordTrace_append hprefix tailTrace_6032668
  have hstable : (prefixWord ++ tailWord_6032668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6032668).length < 2 ^ (prefixWord ++ tailWord_6032668).sum := by decide
  have hdescent : baseEnd_6032668 < baseStart_6032668 := by decide
  rcases family_descends (prefixWord ++ tailWord_6032668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6032672 : List Nat := [2, 1, 1, 5, 4, 1, 1, 1, 2, 3, 2]
def baseStart_6032672 : Nat := 118140960795 + 6032672 * 2 ^ 59
def prefixEnd_6032672 : Nat := 4983230072969 + 3 ^ 40 * 6032672 * 2
def baseEnd_6032672 : Nat := 3097660366920326376756253

theorem tailTrace_6032672 : CollatzResearch.WordTrace tailWord_6032672 prefixEnd_6032672 3097660366920326376756253 := by
  unfold tailWord_6032672
  simp only [CollatzResearch.WordTrace]
  refine ⟨110014812000333558598234135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146686416000444744797645513 110014812000333558598234135)
  ·
    refine ⟨165022218000500337897351203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110014812000333558598234135 165022218000500337897351203)
    ·
      refine ⟨247533327000750506846026805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165022218000500337897351203 247533327000750506846026805)
      ·
        refine ⟨23206249406320360016815013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 247533327000750506846026805 23206249406320360016815013)
        ·
          refine ⟨4351171763685067503152815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23206249406320360016815013 4351171763685067503152815)
          ·
            refine ⟨6526757645527601254729223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4351171763685067503152815 6526757645527601254729223)
            ·
              refine ⟨9790136468291401882093835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6526757645527601254729223 9790136468291401882093835)
              ·
                refine ⟨14685204702437102823140753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9790136468291401882093835 14685204702437102823140753)
                ·
                  refine ⟨11013903526827827117355565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14685204702437102823140753 11013903526827827117355565)
                  ·
                    refine ⟨4130213822560435169008337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11013903526827827117355565 4130213822560435169008337)
                    ·
                      refine ⟨3097660366920326376756253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4130213822560435169008337 3097660366920326376756253)
                      ·
                        rfl

theorem cell23_6032672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 1, 1, 2, 3, 2].length) (baseStart_6032672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6032672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6032672 prefixEnd_6032672 := by exact prefixLift 6032672
  have htrace : WordTrace (prefixWord ++ tailWord_6032672) baseStart_6032672 baseEnd_6032672 := by
    simpa [prefixWord, tailWord_6032672, baseEnd_6032672] using wordTrace_append hprefix tailTrace_6032672
  have hstable : (prefixWord ++ tailWord_6032672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6032672).length < 2 ^ (prefixWord ++ tailWord_6032672).sum := by decide
  have hdescent : baseEnd_6032672 < baseStart_6032672 := by decide
  rcases family_descends (prefixWord ++ tailWord_6032672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6032685 : List Nat := [1, 5, 3, 1, 1, 2, 1, 3, 1, 1, 4]
def baseStart_6032685 : Nat := 118140960795 + 6032685 * 2 ^ 59
def prefixEnd_6032685 : Nat := 4983230072969 + 3 ^ 40 * 6032685 * 2
def baseEnd_6032685 : Nat := 3097667042168834825893693

theorem tailTrace_6032685 : CollatzResearch.WordTrace tailWord_6032685 prefixEnd_6032685 3097667042168834825893693 := by
  unfold tailWord_6032685
  simp only [CollatzResearch.WordTrace]
  refine ⟨220030098149620020416691509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146686732099746680277794339 220030098149620020416691509)
  ·
    refine ⟨20627821701526876914064829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 220030098149620020416691509 20627821701526876914064829)
    ·
      refine ⟨7735433138072578842774311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20627821701526876914064829 7735433138072578842774311)
      ·
        refine ⟨11603149707108868264161467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7735433138072578842774311 11603149707108868264161467)
        ·
          refine ⟨17404724560663302396242201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11603149707108868264161467 17404724560663302396242201)
          ·
            refine ⟨13053543420497476797181651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17404724560663302396242201 13053543420497476797181651)
            ·
              refine ⟨19580315130746215195772477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13053543420497476797181651 19580315130746215195772477)
              ·
                refine ⟨7342618174029830698414679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19580315130746215195772477 7342618174029830698414679)
                ·
                  refine ⟨11013927261044746047622019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7342618174029830698414679 11013927261044746047622019)
                  ·
                    refine ⟨16520890891567119071433029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11013927261044746047622019 16520890891567119071433029)
                    ·
                      refine ⟨3097667042168834825893693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16520890891567119071433029 3097667042168834825893693)
                      ·
                        rfl

theorem cell23_6032685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 1, 3, 1, 1, 4].length) (baseStart_6032685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6032685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6032685 prefixEnd_6032685 := by exact prefixLift 6032685
  have htrace : WordTrace (prefixWord ++ tailWord_6032685) baseStart_6032685 baseEnd_6032685 := by
    simpa [prefixWord, tailWord_6032685, baseEnd_6032685] using wordTrace_append hprefix tailTrace_6032685
  have hstable : (prefixWord ++ tailWord_6032685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6032685).length < 2 ^ (prefixWord ++ tailWord_6032685).sum := by decide
  have hdescent : baseEnd_6032685 < baseStart_6032685 := by decide
  rcases family_descends (prefixWord ++ tailWord_6032685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6032702 : List Nat := [4, 2, 1, 2, 1, 1, 1, 6, 1, 2, 2]
def baseStart_6032702 : Nat := 118140960795 + 6032702 * 2 ^ 59
def prefixEnd_6032702 : Nat := 4983230072969 + 3 ^ 40 * 6032702 * 2
def baseEnd_6032702 : Nat := 3097675771339961259381115

theorem tailTrace_6032702 : CollatzResearch.WordTrace tailWord_6032702 prefixEnd_6032702 3097675771339961259381115 := by
  unfold tailWord_6032702
  simp only [CollatzResearch.WordTrace]
  refine ⟨27503839773819804040007545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 146687145460372288213373573 27503839773819804040007545)
  ·
    refine ⟨20627879830364853030005659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27503839773819804040007545 20627879830364853030005659)
    ·
      refine ⟨30941819745547279545008489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20627879830364853030005659 30941819745547279545008489)
      ·
        refine ⟨23206364809160459658756367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30941819745547279545008489 23206364809160459658756367)
        ·
          refine ⟨34809547213740689488134551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23206364809160459658756367 34809547213740689488134551)
          ·
            refine ⟨52214320820611034232201827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34809547213740689488134551 52214320820611034232201827)
            ·
              refine ⟨78321481230916551348302741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52214320820611034232201827 78321481230916551348302741)
              ·
                refine ⟨3671319432699213344451691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 78321481230916551348302741 3671319432699213344451691)
                ·
                  refine ⟨5506979149048820016677537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3671319432699213344451691 5506979149048820016677537)
                  ·
                    refine ⟨4130234361786615012508153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5506979149048820016677537 4130234361786615012508153)
                    ·
                      refine ⟨3097675771339961259381115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4130234361786615012508153 3097675771339961259381115)
                      ·
                        rfl

theorem cell23_6032702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 6, 1, 2, 2].length) (baseStart_6032702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6032702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6032702 prefixEnd_6032702 := by exact prefixLift 6032702
  have htrace : WordTrace (prefixWord ++ tailWord_6032702) baseStart_6032702 baseEnd_6032702 := by
    simpa [prefixWord, tailWord_6032702, baseEnd_6032702] using wordTrace_append hprefix tailTrace_6032702
  have hstable : (prefixWord ++ tailWord_6032702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6032702).length < 2 ^ (prefixWord ++ tailWord_6032702).sum := by decide
  have hdescent : baseEnd_6032702 < baseStart_6032702 := by decide
  rcases family_descends (prefixWord ++ tailWord_6032702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6032714 : List Nat := [3, 1, 2, 1, 1, 1, 1, 2, 4, 2, 5]
def baseStart_6032714 : Nat := 118140960795 + 6032714 * 2 ^ 59
def prefixEnd_6032714 : Nat := 4983230072969 + 3 ^ 40 * 6032714 * 2
def baseEnd_6032714 : Nat := 3097681933107815212431059

theorem tailTrace_6032714 : CollatzResearch.WordTrace tailWord_6032714 prefixEnd_6032714 3097681933107815212431059 := by
  unfold tailWord_6032714
  simp only [CollatzResearch.WordTrace]
  refine ⟨55007788966628739592374299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146687437244343305579664797 55007788966628739592374299)
  ·
    refine ⟨82511683449943109388561449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55007788966628739592374299 82511683449943109388561449)
    ·
      refine ⟨61883762587457332041421087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82511683449943109388561449 61883762587457332041421087)
      ·
        refine ⟨92825643881185998062131631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61883762587457332041421087 92825643881185998062131631)
        ·
          refine ⟨139238465821778997093197447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92825643881185998062131631 139238465821778997093197447)
          ·
            refine ⟨208857698732668495639796171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139238465821778997093197447 208857698732668495639796171)
            ·
              refine ⟨313286548099002743459694257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 208857698732668495639796171 313286548099002743459694257)
              ·
                refine ⟨234964911074252057594770693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 313286548099002743459694257 234964911074252057594770693)
                ·
                  refine ⟨44055920826422260799019505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 234964911074252057594770693 44055920826422260799019505)
                  ·
                    refine ⟨33041940619816695599264629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 44055920826422260799019505 33041940619816695599264629)
                    ·
                      refine ⟨3097681933107815212431059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33041940619816695599264629 3097681933107815212431059)
                      ·
                        rfl

theorem cell23_6032714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 2, 4, 2, 5].length) (baseStart_6032714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6032714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6032714 prefixEnd_6032714 := by exact prefixLift 6032714
  have htrace : WordTrace (prefixWord ++ tailWord_6032714) baseStart_6032714 baseEnd_6032714 := by
    simpa [prefixWord, tailWord_6032714, baseEnd_6032714] using wordTrace_append hprefix tailTrace_6032714
  have hstable : (prefixWord ++ tailWord_6032714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6032714).length < 2 ^ (prefixWord ++ tailWord_6032714).sum := by decide
  have hdescent : baseEnd_6032714 < baseStart_6032714 := by decide
  rcases family_descends (prefixWord ++ tailWord_6032714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6032769 : List Nat := [1, 2, 4, 3, 2, 2, 2, 1, 2, 1, 3]
def baseStart_6032769 : Nat := 118140960795 + 6032769 * 2 ^ 59
def prefixEnd_6032769 : Nat := 4983230072969 + 3 ^ 40 * 6032769 * 2
def baseEnd_6032769 : Nat := 3097710174543812497243307

theorem tailTrace_6032769 : CollatzResearch.WordTrace tailWord_6032769 prefixEnd_6032769 3097710174543812497243307 := by
  unfold tailWord_6032769
  simp only [CollatzResearch.WordTrace]
  refine ⟨220033161881315702762749361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146688774587543801841832907 220033161881315702762749361)
  ·
    refine ⟨165024871410986777072062021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220033161881315702762749361 165024871410986777072062021)
    ·
      refine ⟨30942163389560020701011629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 165024871410986777072062021 30942163389560020701011629)
      ·
        refine ⟨11603311271085007762879361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30942163389560020701011629 11603311271085007762879361)
        ·
          refine ⟨8702483453313755822159521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11603311271085007762879361 8702483453313755822159521)
          ·
            refine ⟨6526862589985316866619641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8702483453313755822159521 6526862589985316866619641)
            ·
              refine ⟨4895146942488987649964731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6526862589985316866619641 4895146942488987649964731)
              ·
                refine ⟨7342720413733481474947097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4895146942488987649964731 7342720413733481474947097)
                ·
                  refine ⟨5507040310300111106210323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7342720413733481474947097 5507040310300111106210323)
                  ·
                    refine ⟨8260560465450166659315485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5507040310300111106210323 8260560465450166659315485)
                    ·
                      refine ⟨3097710174543812497243307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8260560465450166659315485 3097710174543812497243307)
                      ·
                        rfl

theorem cell23_6032769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 2, 1, 2, 1, 3].length) (baseStart_6032769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6032769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6032769 prefixEnd_6032769 := by exact prefixLift 6032769
  have htrace : WordTrace (prefixWord ++ tailWord_6032769) baseStart_6032769 baseEnd_6032769 := by
    simpa [prefixWord, tailWord_6032769, baseEnd_6032769] using wordTrace_append hprefix tailTrace_6032769
  have hstable : (prefixWord ++ tailWord_6032769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6032769).length < 2 ^ (prefixWord ++ tailWord_6032769).sum := by decide
  have hdescent : baseEnd_6032769 < baseStart_6032769 := by decide
  rcases family_descends (prefixWord ++ tailWord_6032769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6032791 : List Nat := [1, 1, 3, 3, 1, 1, 1, 2, 4, 3, 3]
def baseStart_6032791 : Nat := 118140960795 + 6032791 * 2 ^ 59
def prefixEnd_6032791 : Nat := 4983230072969 + 3 ^ 40 * 6032791 * 2
def baseEnd_6032791 : Nat := 3097721471118211411168205

theorem tailTrace_6032791 : CollatzResearch.WordTrace tailWord_6032791 prefixEnd_6032791 3097721471118211411168205 := by
  unfold tailWord_6032791
  simp only [CollatzResearch.WordTrace]
  refine ⟨220033964287236000520050227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146689309524824000346700151 220033964287236000520050227)
  ·
    refine ⟨330050946430854000780075341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220033964287236000520050227 330050946430854000780075341)
    ·
      refine ⟨123769104911570250292528253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 330050946430854000780075341 123769104911570250292528253)
      ·
        refine ⟨46413414341838843859698095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123769104911570250292528253 46413414341838843859698095)
        ·
          refine ⟨69620121512758265789547143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46413414341838843859698095 69620121512758265789547143)
          ·
            refine ⟨104430182269137398684320715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69620121512758265789547143 104430182269137398684320715)
            ·
              refine ⟨156645273403706098026481073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104430182269137398684320715 156645273403706098026481073)
              ·
                refine ⟨117483955052779573519860805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 156645273403706098026481073 117483955052779573519860805)
                ·
                  refine ⟨22028241572396170034973901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 117483955052779573519860805 22028241572396170034973901)
                  ·
                    refine ⟨8260590589648563763115213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22028241572396170034973901 8260590589648563763115213)
                    ·
                      refine ⟨3097721471118211411168205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8260590589648563763115213 3097721471118211411168205)
                      ·
                        rfl

theorem cell23_6032791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 2, 4, 3, 3].length) (baseStart_6032791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6032791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6032791 prefixEnd_6032791 := by exact prefixLift 6032791
  have htrace : WordTrace (prefixWord ++ tailWord_6032791) baseStart_6032791 baseEnd_6032791 := by
    simpa [prefixWord, tailWord_6032791, baseEnd_6032791] using wordTrace_append hprefix tailTrace_6032791
  have hstable : (prefixWord ++ tailWord_6032791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6032791).length < 2 ^ (prefixWord ++ tailWord_6032791).sum := by decide
  have hdescent : baseEnd_6032791 < baseStart_6032791 := by decide
  rcases family_descends (prefixWord ++ tailWord_6032791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6032831 : List Nat := [1, 1, 2, 2, 2, 1, 1, 4, 4, 1, 4]
def baseStart_6032831 : Nat := 118140960795 + 6032831 * 2 ^ 59
def prefixEnd_6032831 : Nat := 4983230072969 + 3 ^ 40 * 6032831 * 2
def baseEnd_6032831 : Nat := 3097742010344391254668021

theorem tailTrace_6032831 : CollatzResearch.WordTrace tailWord_6032831 prefixEnd_6032831 3097742010344391254668021 := by
  unfold tailWord_6032831
  simp only [CollatzResearch.WordTrace]
  refine ⟨220035423207091087351506347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146690282138060724901004231 220035423207091087351506347)
  ·
    refine ⟨330053134810636631027259521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220035423207091087351506347 330053134810636631027259521)
    ·
      refine ⟨247539851107977473270444641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 330053134810636631027259521 247539851107977473270444641)
      ·
        refine ⟨185654888330983104952833481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 247539851107977473270444641 185654888330983104952833481)
        ·
          refine ⟨139241166248237328714625111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 185654888330983104952833481 139241166248237328714625111)
          ·
            refine ⟨208861749372355993071937667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139241166248237328714625111 208861749372355993071937667)
            ·
              refine ⟨313292624058533989607906501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 208861749372355993071937667 313292624058533989607906501)
              ·
                refine ⟨58742367010975123051482469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 313292624058533989607906501 58742367010975123051482469)
                ·
                  refine ⟨11014193814557835572152963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 58742367010975123051482469 11014193814557835572152963)
                  ·
                    refine ⟨16521290721836753358229445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11014193814557835572152963 16521290721836753358229445)
                    ·
                      refine ⟨3097742010344391254668021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16521290721836753358229445 3097742010344391254668021)
                      ·
                        rfl

theorem cell23_6032831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 4, 4, 1, 4].length) (baseStart_6032831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6032831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6032831 prefixEnd_6032831 := by exact prefixLift 6032831
  have htrace : WordTrace (prefixWord ++ tailWord_6032831) baseStart_6032831 baseEnd_6032831 := by
    simpa [prefixWord, tailWord_6032831, baseEnd_6032831] using wordTrace_append hprefix tailTrace_6032831
  have hstable : (prefixWord ++ tailWord_6032831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6032831).length < 2 ^ (prefixWord ++ tailWord_6032831).sum := by decide
  have hdescent : baseEnd_6032831 < baseStart_6032831 := by decide
  rcases family_descends (prefixWord ++ tailWord_6032831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6032868 : List Nat := [2, 3, 1, 1, 1, 1, 1, 6, 2, 2, 3]
def baseStart_6032868 : Nat := 118140960795 + 6032868 * 2 ^ 59
def prefixEnd_6032868 : Nat := 4983230072969 + 3 ^ 40 * 6032868 * 2
def baseEnd_6032868 : Nat := 3097761009128607609905351

theorem tailTrace_6032868 : CollatzResearch.WordTrace tailWord_6032868 prefixEnd_6032868 3097761009128607609905351 := by
  unfold tailWord_6032868
  simp only [CollatzResearch.WordTrace]
  refine ⟨110018386353978521335301629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146691181805304695113735505 110018386353978521335301629)
  ·
    refine ⟨41256894882741945500738111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110018386353978521335301629 41256894882741945500738111)
    ·
      refine ⟨61885342324112918251107167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41256894882741945500738111 61885342324112918251107167)
      ·
        refine ⟨92828013486169377376660751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61885342324112918251107167 92828013486169377376660751)
        ·
          refine ⟨139242020229254066064991127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92828013486169377376660751 139242020229254066064991127)
          ·
            refine ⟨208863030343881099097486691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139242020229254066064991127 208863030343881099097486691)
            ·
              refine ⟨313294545515821648646230037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 208863030343881099097486691 313294545515821648646230037)
              ·
                refine ⟨14685681821054139780292033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 313294545515821648646230037 14685681821054139780292033)
                ·
                  refine ⟨11014261365790604835219025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14685681821054139780292033 11014261365790604835219025)
                  ·
                    refine ⟨8260696024342953626414269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11014261365790604835219025 8260696024342953626414269)
                    ·
                      refine ⟨3097761009128607609905351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8260696024342953626414269 3097761009128607609905351)
                      ·
                        rfl

theorem cell23_6032868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 6, 2, 2, 3].length) (baseStart_6032868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6032868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6032868 prefixEnd_6032868 := by exact prefixLift 6032868
  have htrace : WordTrace (prefixWord ++ tailWord_6032868) baseStart_6032868 baseEnd_6032868 := by
    simpa [prefixWord, tailWord_6032868, baseEnd_6032868] using wordTrace_append hprefix tailTrace_6032868
  have hstable : (prefixWord ++ tailWord_6032868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6032868).length < 2 ^ (prefixWord ++ tailWord_6032868).sum := by decide
  have hdescent : baseEnd_6032868 < baseStart_6032868 := by decide
  rcases family_descends (prefixWord ++ tailWord_6032868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6032885 : List Nat := [1, 3, 5, 1, 1, 1, 1, 2, 1, 4, 3]
def baseStart_6032885 : Nat := 118140960795 + 6032885 * 2 ^ 59
def prefixEnd_6032885 : Nat := 4983230072969 + 3 ^ 40 * 6032885 * 2
def baseEnd_6032885 : Nat := 3097769738299734043392773

theorem tailTrace_6032885 : CollatzResearch.WordTrace tailWord_6032885 prefixEnd_6032885 3097769738299734043392773 := by
  unfold tailWord_6032885
  simp only [CollatzResearch.WordTrace]
  refine ⟨220037392748895454573972109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146691595165930303049314739 220037392748895454573972109)
  ·
    refine ⟨82514022280835795465239541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 220037392748895454573972109 82514022280835795465239541)
    ·
      refine ⟨7735689588828355824866207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 82514022280835795465239541 7735689588828355824866207)
      ·
        refine ⟨11603534383242533737299311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7735689588828355824866207 11603534383242533737299311)
        ·
          refine ⟨17405301574863800605948967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11603534383242533737299311 17405301574863800605948967)
          ·
            refine ⟨26107952362295700908923451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17405301574863800605948967 26107952362295700908923451)
            ·
              refine ⟨39161928543443551363385177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26107952362295700908923451 39161928543443551363385177)
              ·
                refine ⟨29371446407582663522538883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39161928543443551363385177 29371446407582663522538883)
                ·
                  refine ⟨44057169611373995283808325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29371446407582663522538883 44057169611373995283808325)
                  ·
                    refine ⟨8260719302132624115714061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 44057169611373995283808325 8260719302132624115714061)
                    ·
                      refine ⟨3097769738299734043392773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8260719302132624115714061 3097769738299734043392773)
                      ·
                        rfl

theorem cell23_6032885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 2, 1, 4, 3].length) (baseStart_6032885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6032885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6032885 prefixEnd_6032885 := by exact prefixLift 6032885
  have htrace : WordTrace (prefixWord ++ tailWord_6032885) baseStart_6032885 baseEnd_6032885 := by
    simpa [prefixWord, tailWord_6032885, baseEnd_6032885] using wordTrace_append hprefix tailTrace_6032885
  have hstable : (prefixWord ++ tailWord_6032885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6032885).length < 2 ^ (prefixWord ++ tailWord_6032885).sum := by decide
  have hdescent : baseEnd_6032885 < baseStart_6032885 := by decide
  rcases family_descends (prefixWord ++ tailWord_6032885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6032972 : List Nat := [2, 2, 1, 3, 1, 4, 3, 1, 1, 1, 4]
def baseStart_6032972 : Nat := 118140960795 + 6032972 * 2 ^ 59
def prefixEnd_6032972 : Nat := 4983230072969 + 3 ^ 40 * 6032972 * 2
def baseEnd_6032972 : Nat := 3097814411116675203004873

theorem tailTrace_6032972 : CollatzResearch.WordTrace tailWord_6032972 prefixEnd_6032972 3097814411116675203004873 := by
  unfold tailWord_6032972
  simp only [CollatzResearch.WordTrace]
  refine ⟨110020282949790134216194585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146693710599720178954926113 110020282949790134216194585)
  ·
    refine ⟨82515212212342600662145939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110020282949790134216194585 82515212212342600662145939)
    ·
      refine ⟨123772818318513900993218909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82515212212342600662145939 123772818318513900993218909)
      ·
        refine ⟨46414806869442712872457091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123772818318513900993218909 46414806869442712872457091)
        ·
          refine ⟨69622210304164069308685637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46414806869442712872457091 69622210304164069308685637)
          ·
            refine ⟨13054164432030762995378557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 69622210304164069308685637 13054164432030762995378557)
            ·
              refine ⟨4895311662011536123266959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13054164432030762995378557 4895311662011536123266959)
              ·
                refine ⟨7342967493017304184900439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4895311662011536123266959 7342967493017304184900439)
                ·
                  refine ⟨11014451239525956277350659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7342967493017304184900439 11014451239525956277350659)
                  ·
                    refine ⟨16521676859288934416025989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11014451239525956277350659 16521676859288934416025989)
                    ·
                      refine ⟨3097814411116675203004873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16521676859288934416025989 3097814411116675203004873)
                      ·
                        rfl

theorem cell23_6032972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 3, 1, 1, 1, 4].length) (baseStart_6032972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6032972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6032972 prefixEnd_6032972 := by exact prefixLift 6032972
  have htrace : WordTrace (prefixWord ++ tailWord_6032972) baseStart_6032972 baseEnd_6032972 := by
    simpa [prefixWord, tailWord_6032972, baseEnd_6032972] using wordTrace_append hprefix tailTrace_6032972
  have hstable : (prefixWord ++ tailWord_6032972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6032972).length < 2 ^ (prefixWord ++ tailWord_6032972).sum := by decide
  have hdescent : baseEnd_6032972 < baseStart_6032972 := by decide
  rcases family_descends (prefixWord ++ tailWord_6032972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6033045 : List Nat := [1, 3, 2, 1, 1, 1, 1, 4, 3, 4, 2]
def baseStart_6033045 : Nat := 118140960795 + 6033045 * 2 ^ 59
def prefixEnd_6033045 : Nat := 4983230072969 + 3 ^ 40 * 6033045 * 2
def baseEnd_6033045 : Nat := 3097851895204453417392037

theorem tailTrace_6033045 : CollatzResearch.WordTrace tailWord_6033045 prefixEnd_6033045 3097851895204453417392037 := by
  unfold tailWord_6033045
  simp only [CollatzResearch.WordTrace]
  refine ⟨220043228428315801899796589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146695485618877201266531059 220043228428315801899796589)
  ·
    refine ⟨82516210660618425712423721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 220043228428315801899796589 82516210660618425712423721)
    ·
      refine ⟨61887157995463819284317791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82516210660618425712423721 61887157995463819284317791)
      ·
        refine ⟨92830736993195728926476687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61887157995463819284317791 92830736993195728926476687)
        ·
          refine ⟨139246105489793593389715031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92830736993195728926476687 139246105489793593389715031)
          ·
            refine ⟨208869158234690390084572547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139246105489793593389715031 208869158234690390084572547)
            ·
              refine ⟨313303737352035585126858821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 208869158234690390084572547 313303737352035585126858821)
              ·
                refine ⟨58744450753506672211286029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 313303737352035585126858821 58744450753506672211286029)
                ·
                  refine ⟨22029169032565002079232261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58744450753506672211286029 22029169032565002079232261)
                  ·
                    refine ⟨4130469193605937889856049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22029169032565002079232261 4130469193605937889856049)
                    ·
                      refine ⟨3097851895204453417392037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4130469193605937889856049 3097851895204453417392037)
                      ·
                        rfl

theorem cell23_6033045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 4, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 4, 3, 4, 2].length) (baseStart_6033045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6033045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6033045 prefixEnd_6033045 := by exact prefixLift 6033045
  have htrace : WordTrace (prefixWord ++ tailWord_6033045) baseStart_6033045 baseEnd_6033045 := by
    simpa [prefixWord, tailWord_6033045, baseEnd_6033045] using wordTrace_append hprefix tailTrace_6033045
  have hstable : (prefixWord ++ tailWord_6033045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6033045).length < 2 ^ (prefixWord ++ tailWord_6033045).sum := by decide
  have hdescent : baseEnd_6033045 < baseStart_6033045 := by decide
  rcases family_descends (prefixWord ++ tailWord_6033045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6033189 : List Nat := [1, 3, 1, 2, 3, 4, 1, 1, 2, 2, 3]
def baseStart_6033189 : Nat := 118140960795 + 6033189 * 2 ^ 59
def prefixEnd_6033189 : Nat := 4983230072969 + 3 ^ 40 * 6033189 * 2
def baseEnd_6033189 : Nat := 3097925836418700853991375

theorem tailTrace_6033189 : CollatzResearch.WordTrace tailWord_6033189 prefixEnd_6033189 3097925836418700853991375 := by
  unfold tailWord_6033189
  simp only [CollatzResearch.WordTrace]
  refine ⟨220048480539794114493038621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146698987026529409662025747 220048480539794114493038621)
  ·
    refine ⟨82518180202422792934889483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 220048480539794114493038621 82518180202422792934889483)
    ·
      refine ⟨123777270303634189402334225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82518180202422792934889483 123777270303634189402334225)
      ·
        refine ⟨92832952727725642051750669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123777270303634189402334225 92832952727725642051750669)
        ·
          refine ⟨34812357272897115769406501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92832952727725642051750669 34812357272897115769406501)
          ·
            refine ⟨6527316988668209206763719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34812357272897115769406501 6527316988668209206763719)
            ·
              refine ⟨9790975483002313810145579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6527316988668209206763719 9790975483002313810145579)
              ·
                refine ⟨14686463224503470715218369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9790975483002313810145579 14686463224503470715218369)
                ·
                  refine ⟨11014847418377603036413777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14686463224503470715218369 11014847418377603036413777)
                  ·
                    refine ⟨8261135563783202277310333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11014847418377603036413777 8261135563783202277310333)
                    ·
                      refine ⟨3097925836418700853991375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8261135563783202277310333 3097925836418700853991375)
                      ·
                        rfl

theorem cell23_6033189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 1, 1, 2, 2, 3].length) (baseStart_6033189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6033189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6033189 prefixEnd_6033189 := by exact prefixLift 6033189
  have htrace : WordTrace (prefixWord ++ tailWord_6033189) baseStart_6033189 baseEnd_6033189 := by
    simpa [prefixWord, tailWord_6033189, baseEnd_6033189] using wordTrace_append hprefix tailTrace_6033189
  have hstable : (prefixWord ++ tailWord_6033189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6033189).length < 2 ^ (prefixWord ++ tailWord_6033189).sum := by decide
  have hdescent : baseEnd_6033189 < baseStart_6033189 := by decide
  rcases family_descends (prefixWord ++ tailWord_6033189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6033219 : List Nat := [1, 1, 1, 3, 1, 6, 2, 1, 3, 1, 3]
def baseStart_6033219 : Nat := 118140960795 + 6033219 * 2 ^ 59
def prefixEnd_6033219 : Nat := 4983230072969 + 3 ^ 40 * 6033219 * 2
def baseEnd_6033219 : Nat := 3097941240838335736616237

theorem tailTrace_6033219 : CollatzResearch.WordTrace tailWord_6033219 prefixEnd_6033219 3097941240838335736616237 := by
  unfold tailWord_6033219
  simp only [CollatzResearch.WordTrace]
  refine ⟨220049574729685429616630711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146699716486456953077753807 220049574729685429616630711)
  ·
    refine ⟨330074362094528144424946067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220049574729685429616630711 330074362094528144424946067)
    ·
      refine ⟨495111543141792216637419101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 330074362094528144424946067 495111543141792216637419101)
      ·
        refine ⟨185666828678172081239032163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 495111543141792216637419101 185666828678172081239032163)
        ·
          refine ⟨278500243017258121858548245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185666828678172081239032163 278500243017258121858548245)
          ·
            refine ⟨13054698891433974462119449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 278500243017258121858548245 13054698891433974462119449)
            ·
              refine ⟨9791024168575480846589587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13054698891433974462119449 9791024168575480846589587)
              ·
                refine ⟨14686536252863221269884381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9791024168575480846589587 14686536252863221269884381)
                ·
                  refine ⟨5507451094823707976206643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14686536252863221269884381 5507451094823707976206643)
                  ·
                    refine ⟨8261176642235561964309965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5507451094823707976206643 8261176642235561964309965)
                    ·
                      refine ⟨3097941240838335736616237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8261176642235561964309965 3097941240838335736616237)
                      ·
                        rfl

theorem cell23_6033219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 2, 1, 3, 1, 3].length) (baseStart_6033219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6033219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6033219 prefixEnd_6033219 := by exact prefixLift 6033219
  have htrace : WordTrace (prefixWord ++ tailWord_6033219) baseStart_6033219 baseEnd_6033219 := by
    simpa [prefixWord, tailWord_6033219, baseEnd_6033219] using wordTrace_append hprefix tailTrace_6033219
  have hstable : (prefixWord ++ tailWord_6033219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6033219).length < 2 ^ (prefixWord ++ tailWord_6033219).sum := by decide
  have hdescent : baseEnd_6033219 < baseStart_6033219 := by decide
  rcases family_descends (prefixWord ++ tailWord_6033219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6033239 : List Nat := [1, 1, 3, 2, 5, 1, 2, 2, 1, 5]
def baseStart_6033239 : Nat := 118140960795 + 6033239 * 2 ^ 59
def prefixEnd_6033239 : Nat := 4983230072969 + 3 ^ 40 * 6033239 * 2
def baseEnd_6033239 : Nat := 1032650503483808552788715

theorem tailTrace_6033239 : CollatzResearch.WordTrace tailWord_6033239 prefixEnd_6033239 1032650503483808552788715 := by
  unfold tailWord_6033239
  simp only [CollatzResearch.WordTrace]
  refine ⟨220050304189612973032358771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146700202793075315354905847 220050304189612973032358771)
  ·
    refine ⟨330075456284419459548538157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220050304189612973032358771 330075456284419459548538157)
    ·
      refine ⟨123778296106657297330701809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 330075456284419459548538157 123778296106657297330701809)
      ·
        refine ⟨92833722079992972998026357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123778296106657297330701809 92833722079992972998026357)
        ·
          refine ⟨8703161444999341218564971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 92833722079992972998026357 8703161444999341218564971)
          ·
            refine ⟨13054742167499011827847457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8703161444999341218564971 13054742167499011827847457)
            ·
              refine ⟨9791056625624258870885593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13054742167499011827847457 9791056625624258870885593)
              ·
                refine ⟨7343292469218194153164195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9791056625624258870885593 7343292469218194153164195)
                ·
                  refine ⟨11014938703827291229746293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7343292469218194153164195 11014938703827291229746293)
                  ·
                    refine ⟨1032650503483808552788715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11014938703827291229746293 1032650503483808552788715)
                    ·
                      rfl

theorem cell23_6033239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 2, 2, 1, 5].length) (baseStart_6033239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6033239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6033239 prefixEnd_6033239 := by exact prefixLift 6033239
  have htrace : WordTrace (prefixWord ++ tailWord_6033239) baseStart_6033239 baseEnd_6033239 := by
    simpa [prefixWord, tailWord_6033239, baseEnd_6033239] using wordTrace_append hprefix tailTrace_6033239
  have hstable : (prefixWord ++ tailWord_6033239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6033239).length < 2 ^ (prefixWord ++ tailWord_6033239).sum := by decide
  have hdescent : baseEnd_6033239 < baseStart_6033239 := by decide
  rcases family_descends (prefixWord ++ tailWord_6033239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6033242 : List Nat := [3, 1, 1, 2, 1, 3, 1, 1, 2, 6, 2]
def baseStart_6033242 : Nat := 118140960795 + 6033242 * 2 ^ 59
def prefixEnd_6033242 : Nat := 4983230072969 + 3 ^ 40 * 6033242 * 2
def baseEnd_6033242 : Nat := 3097953050893389146628631

theorem tailTrace_6033242 : CollatzResearch.WordTrace tailWord_6033242 prefixEnd_6033242 3097953050893389146628631 := by
  unfold tailWord_6033242
  simp only [CollatzResearch.WordTrace]
  refine ⟨55012603402150526136179495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146700275739068069696478653 55012603402150526136179495)
  ·
    refine ⟨82518905103225789204269243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55012603402150526136179495 82518905103225789204269243)
    ·
      refine ⟨123778357654838683806403865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82518905103225789204269243 123778357654838683806403865)
      ·
        refine ⟨92833768241129012854802899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123778357654838683806403865 92833768241129012854802899)
        ·
          refine ⟨139250652361693519282204349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92833768241129012854802899 139250652361693519282204349)
          ·
            refine ⟨52218994635635069730826631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 139250652361693519282204349 52218994635635069730826631)
            ·
              refine ⟨78328491953452604596239947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52218994635635069730826631 78328491953452604596239947)
              ·
                refine ⟨117492737930178906894359921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78328491953452604596239947 117492737930178906894359921)
                ·
                  refine ⟨88119553447634180170769941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 117492737930178906894359921 88119553447634180170769941)
                  ·
                    refine ⟨4130604067857852195504841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 88119553447634180170769941 4130604067857852195504841)
                    ·
                      refine ⟨3097953050893389146628631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4130604067857852195504841 3097953050893389146628631)
                      ·
                        rfl

theorem cell23_6033242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 1, 2, 6, 2].length) (baseStart_6033242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6033242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6033242 prefixEnd_6033242 := by exact prefixLift 6033242
  have htrace : WordTrace (prefixWord ++ tailWord_6033242) baseStart_6033242 baseEnd_6033242 := by
    simpa [prefixWord, tailWord_6033242, baseEnd_6033242] using wordTrace_append hprefix tailTrace_6033242
  have hstable : (prefixWord ++ tailWord_6033242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6033242).length < 2 ^ (prefixWord ++ tailWord_6033242).sum := by decide
  have hdescent : baseEnd_6033242 < baseStart_6033242 := by decide
  rcases family_descends (prefixWord ++ tailWord_6033242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6033269 : List Nat := [1, 3, 4, 1, 1, 1, 2, 4, 2, 4]
def baseStart_6033269 : Nat := 118140960795 + 6033269 * 2 ^ 59
def prefixEnd_6033269 : Nat := 4983230072969 + 3 ^ 40 * 6033269 * 2
def baseEnd_6033269 : Nat := 1032655638290353513663669

theorem tailTrace_6033269 : CollatzResearch.WordTrace tailWord_6033269 prefixEnd_6033269 1032655638290353513663669 := by
  unfold tailWord_6033269
  simp only [CollatzResearch.WordTrace]
  refine ⟨220051398379504288155950861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146700932253002858770633907 220051398379504288155950861)
  ·
    refine ⟨82519274392314108058481573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 220051398379504288155950861 82519274392314108058481573)
    ·
      refine ⟨15472363948558895260965295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 82519274392314108058481573 15472363948558895260965295)
      ·
        refine ⟨23208545922838342891447943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15472363948558895260965295 23208545922838342891447943)
        ·
          refine ⟨34812818884257514337171915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23208545922838342891447943 34812818884257514337171915)
          ·
            refine ⟨52219228326386271505757873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34812818884257514337171915 52219228326386271505757873)
            ·
              refine ⟨39164421244789703629318405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52219228326386271505757873 39164421244789703629318405)
              ·
                refine ⟨7343328983398069430497201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39164421244789703629318405 7343328983398069430497201)
                ·
                  refine ⟨5507496737548552072872901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7343328983398069430497201 5507496737548552072872901)
                  ·
                    refine ⟨1032655638290353513663669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5507496737548552072872901 1032655638290353513663669)
                    ·
                      rfl

theorem cell23_6033269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 4, 2, 4].length) (baseStart_6033269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6033269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6033269 prefixEnd_6033269 := by exact prefixLift 6033269
  have htrace : WordTrace (prefixWord ++ tailWord_6033269) baseStart_6033269 baseEnd_6033269 := by
    simpa [prefixWord, tailWord_6033269, baseEnd_6033269] using wordTrace_append hprefix tailTrace_6033269
  have hstable : (prefixWord ++ tailWord_6033269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6033269).length < 2 ^ (prefixWord ++ tailWord_6033269).sum := by decide
  have hdescent : baseEnd_6033269 < baseStart_6033269 := by decide
  rcases family_descends (prefixWord ++ tailWord_6033269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6033270 : List Nat := [5, 1, 1, 3, 3, 1, 1, 1, 3, 1, 3]
def baseStart_6033270 : Nat := 118140960795 + 6033270 * 2 ^ 59
def prefixEnd_6033270 : Nat := 4983230072969 + 3 ^ 40 * 6033270 * 2
def baseEnd_6033270 : Nat := 3097967428351715037078503

theorem tailTrace_6033270 : CollatzResearch.WordTrace tailWord_6033270 prefixEnd_6033270 3097967428351715037078503 := by
  unfold tailWord_6033270
  simp only [CollatzResearch.WordTrace]
  refine ⟨13753214678281291582921079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 146700956568333776884491509 13753214678281291582921079)
  ·
    refine ⟨20629822017421937374381619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13753214678281291582921079 20629822017421937374381619)
    ·
      refine ⟨30944733026132906061572429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20629822017421937374381619 30944733026132906061572429)
      ·
        refine ⟨11604274884799839773089661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30944733026132906061572429 11604274884799839773089661)
        ·
          refine ⟨4351603081799939914908623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11604274884799839773089661 4351603081799939914908623)
          ·
            refine ⟨6527404622699909872362935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4351603081799939914908623 6527404622699909872362935)
            ·
              refine ⟨9791106934049864808544403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6527404622699909872362935 9791106934049864808544403)
              ·
                refine ⟨14686660401074797212816605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9791106934049864808544403 14686660401074797212816605)
                ·
                  refine ⟨5507497650403048954806227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14686660401074797212816605 5507497650403048954806227)
                  ·
                    refine ⟨8261246475604573432209341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5507497650403048954806227 8261246475604573432209341)
                    ·
                      refine ⟨3097967428351715037078503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8261246475604573432209341 3097967428351715037078503)
                      ·
                        rfl

theorem cell23_6033270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 1, 1, 3, 1, 3].length) (baseStart_6033270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6033270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6033270 prefixEnd_6033270 := by exact prefixLift 6033270
  have htrace : WordTrace (prefixWord ++ tailWord_6033270) baseStart_6033270 baseEnd_6033270 := by
    simpa [prefixWord, tailWord_6033270, baseEnd_6033270] using wordTrace_append hprefix tailTrace_6033270
  have hstable : (prefixWord ++ tailWord_6033270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6033270).length < 2 ^ (prefixWord ++ tailWord_6033270).sum := by decide
  have hdescent : baseEnd_6033270 < baseStart_6033270 := by decide
  rcases family_descends (prefixWord ++ tailWord_6033270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6033285 : List Nat := [1, 3, 1, 1, 3, 2, 1, 1, 2, 2, 6]
def baseStart_6033285 : Nat := 118140960795 + 6033285 * 2 ^ 59
def prefixEnd_6033285 : Nat := 4983230072969 + 3 ^ 40 * 6033285 * 2
def baseEnd_6033285 : Nat := 3097975130561532478390933

theorem tailTrace_6033285 : CollatzResearch.WordTrace tailWord_6033285 prefixEnd_6033285 3097975130561532478390933 := by
  unfold tailWord_6033285
  simp only [CollatzResearch.WordTrace]
  refine ⟨220051981947446322888533309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146701321298297548592355539 220051981947446322888533309)
  ·
    refine ⟨82519493230292371083199991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 220051981947446322888533309 82519493230292371083199991)
    ·
      refine ⟨123779239845438556624799987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82519493230292371083199991 123779239845438556624799987)
      ·
        refine ⟨185668859768157834937199981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123779239845438556624799987 185668859768157834937199981)
        ·
          refine ⟨69625822413059188101449993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 185668859768157834937199981 69625822413059188101449993)
          ·
            refine ⟨52219366809794391076087495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69625822413059188101449993 52219366809794391076087495)
            ·
              refine ⟨78329050214691586614131243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52219366809794391076087495 78329050214691586614131243)
              ·
                refine ⟨117493575322037379921196865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78329050214691586614131243 117493575322037379921196865)
                ·
                  refine ⟨88120181491528034940897649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 117493575322037379921196865 88120181491528034940897649)
                  ·
                    refine ⟨66090136118646026205673237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 88120181491528034940897649 66090136118646026205673237)
                    ·
                      refine ⟨3097975130561532478390933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 66090136118646026205673237 3097975130561532478390933)
                      ·
                        rfl

theorem cell23_6033285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 1, 2, 2, 6].length) (baseStart_6033285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6033285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6033285 prefixEnd_6033285 := by exact prefixLift 6033285
  have htrace : WordTrace (prefixWord ++ tailWord_6033285) baseStart_6033285 baseEnd_6033285 := by
    simpa [prefixWord, tailWord_6033285, baseEnd_6033285] using wordTrace_append hprefix tailTrace_6033285
  have hstable : (prefixWord ++ tailWord_6033285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6033285).length < 2 ^ (prefixWord ++ tailWord_6033285).sum := by decide
  have hdescent : baseEnd_6033285 < baseStart_6033285 := by decide
  rcases family_descends (prefixWord ++ tailWord_6033285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6033292 : List Nat := [2, 2, 1, 2, 1, 2, 1, 5, 1, 3, 3]
def baseStart_6033292 : Nat := 118140960795 + 6033292 * 2 ^ 59
def prefixEnd_6033292 : Nat := 4983230072969 + 3 ^ 40 * 6033292 * 2
def baseEnd_6033292 : Nat := 3097978724926113951003401

theorem tailTrace_6033292 : CollatzResearch.WordTrace tailWord_6033292 prefixEnd_6033292 3097978724926113951003401 := by
  unfold tailWord_6033292
  simp only [CollatzResearch.WordTrace]
  refine ⟨110026118629210481542019065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146701491505613975389358753 110026118629210481542019065)
  ·
    refine ⟨82519588971907861156514299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110026118629210481542019065 82519588971907861156514299)
    ·
      refine ⟨123779383457861791734771449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82519588971907861156514299 123779383457861791734771449)
      ·
        refine ⟨92834537593396343801078587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123779383457861791734771449 92834537593396343801078587)
        ·
          refine ⟨139251806390094515701617881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92834537593396343801078587 139251806390094515701617881)
          ·
            refine ⟨104438854792570886776213411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 139251806390094515701617881 104438854792570886776213411)
            ·
              refine ⟨156658282188856330164320117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104438854792570886776213411 156658282188856330164320117)
              ·
                refine ⟨14686713955205280952905011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 156658282188856330164320117 14686713955205280952905011)
                ·
                  refine ⟨22030070932807921429357517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14686713955205280952905011 22030070932807921429357517)
                  ·
                    refine ⟨8261276599802970536009069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22030070932807921429357517 8261276599802970536009069)
                    ·
                      refine ⟨3097978724926113951003401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8261276599802970536009069 3097978724926113951003401)
                      ·
                        rfl

theorem cell23_6033292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 5, 1, 3, 3].length) (baseStart_6033292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6033292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6033292 prefixEnd_6033292 := by exact prefixLift 6033292
  have htrace : WordTrace (prefixWord ++ tailWord_6033292) baseStart_6033292 baseEnd_6033292 := by
    simpa [prefixWord, tailWord_6033292, baseEnd_6033292] using wordTrace_append hprefix tailTrace_6033292
  have hstable : (prefixWord ++ tailWord_6033292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6033292).length < 2 ^ (prefixWord ++ tailWord_6033292).sum := by decide
  have hdescent : baseEnd_6033292 < baseStart_6033292 := by decide
  rcases family_descends (prefixWord ++ tailWord_6033292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6033305 : List Nat := [1, 2, 1, 2, 1, 3, 2, 1, 1, 4, 5]
def baseStart_6033305 : Nat := 118140960795 + 6033305 * 2 ^ 59
def prefixEnd_6033305 : Nat := 4983230072969 + 3 ^ 40 * 6033305 * 2
def baseEnd_6033305 : Nat := 3097985400174622400140841

theorem tailTrace_6033305 : CollatzResearch.WordTrace tailWord_6033305 prefixEnd_6033305 3097985400174622400140841 := by
  unfold tailWord_6033305
  simp only [CollatzResearch.WordTrace]
  refine ⟨220052711407373866304261369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146701807604915910869507579 220052711407373866304261369)
  ·
    refine ⟨165039533555530399728196027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220052711407373866304261369 165039533555530399728196027)
    ·
      refine ⟨247559300333295599592294041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165039533555530399728196027 247559300333295599592294041)
      ·
        refine ⟨185669475249971699694220531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 247559300333295599592294041 185669475249971699694220531)
        ·
          refine ⟨278504212874957549541330797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185669475249971699694220531 278504212874957549541330797)
          ·
            refine ⟨104439079828109081077999049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 278504212874957549541330797 104439079828109081077999049)
            ·
              refine ⟨78329309871081810808499287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104439079828109081077999049 78329309871081810808499287)
              ·
                refine ⟨117493964806622716212748931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78329309871081810808499287 117493964806622716212748931)
                ·
                  refine ⟨176240947209934074319123397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 117493964806622716212748931 176240947209934074319123397)
                  ·
                    refine ⟨33045177601862638934835637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 176240947209934074319123397 33045177601862638934835637)
                    ·
                      refine ⟨3097985400174622400140841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33045177601862638934835637 3097985400174622400140841)
                      ·
                        rfl

theorem cell23_6033305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 1, 1, 4, 5].length) (baseStart_6033305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6033305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6033305 prefixEnd_6033305 := by exact prefixLift 6033305
  have htrace : WordTrace (prefixWord ++ tailWord_6033305) baseStart_6033305 baseEnd_6033305 := by
    simpa [prefixWord, tailWord_6033305, baseEnd_6033305] using wordTrace_append hprefix tailTrace_6033305
  have hstable : (prefixWord ++ tailWord_6033305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6033305).length < 2 ^ (prefixWord ++ tailWord_6033305).sum := by decide
  have hdescent : baseEnd_6033305 < baseStart_6033305 := by decide
  rcases family_descends (prefixWord ++ tailWord_6033305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6033309 : List Nat := [1, 4, 2, 1, 2, 3, 1, 2, 1, 3, 3]
def baseStart_6033309 : Nat := 118140960795 + 6033309 * 2 ^ 59
def prefixEnd_6033309 : Nat := 4983230072969 + 3 ^ 40 * 6033309 * 2
def baseEnd_6033309 : Nat := 3097987454097240384490823

theorem tailTrace_6033309 : CollatzResearch.WordTrace tailWord_6033309 prefixEnd_6033309 3097987454097240384490823 := by
  unfold tailWord_6033309
  simp only [CollatzResearch.WordTrace]
  refine ⟨220052857299359374987406981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146701904866239583324937987 220052857299359374987406981)
  ·
    refine ⟨41259910743629882810138809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 220052857299359374987406981 41259910743629882810138809)
    ·
      refine ⟨30944933057722412107604107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41259910743629882810138809 30944933057722412107604107)
      ·
        refine ⟨46417399586583618161406161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30944933057722412107604107 46417399586583618161406161)
        ·
          refine ⟨34813049689937713621054621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46417399586583618161406161 34813049689937713621054621)
          ·
            refine ⟨13054893633726642607895483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34813049689937713621054621 13054893633726642607895483)
            ·
              refine ⟨19582340450589963911843225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13054893633726642607895483 19582340450589963911843225)
              ·
                refine ⟨14686755337942472933882419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19582340450589963911843225 14686755337942472933882419)
                ·
                  refine ⟨22030133006913709400823629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14686755337942472933882419 22030133006913709400823629)
                  ·
                    refine ⟨8261299877592641025308861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22030133006913709400823629 8261299877592641025308861)
                    ·
                      refine ⟨3097987454097240384490823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8261299877592641025308861 3097987454097240384490823)
                      ·
                        rfl

theorem cell23_6033309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 1, 2, 1, 3, 3].length) (baseStart_6033309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6033309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6033309 prefixEnd_6033309 := by exact prefixLift 6033309
  have htrace : WordTrace (prefixWord ++ tailWord_6033309) baseStart_6033309 baseEnd_6033309 := by
    simpa [prefixWord, tailWord_6033309, baseEnd_6033309] using wordTrace_append hprefix tailTrace_6033309
  have hstable : (prefixWord ++ tailWord_6033309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6033309).length < 2 ^ (prefixWord ++ tailWord_6033309).sum := by decide
  have hdescent : baseEnd_6033309 < baseStart_6033309 := by decide
  rcases family_descends (prefixWord ++ tailWord_6033309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
