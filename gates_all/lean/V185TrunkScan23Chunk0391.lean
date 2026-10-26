import V185TrunkScan23Chunk0390

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2310992 : List Nat := [2, 1, 1, 1, 1, 4, 2, 1, 2, 5, 3]
def baseStart_2310992 : Nat := 118140960795 + 2310992 * 2 ^ 59
def prefixEnd_2310992 : Nat := 4983230072969 + 3 ^ 40 * 2310992 * 2
def baseEnd_2310992 : Nat := 1186649684695327466871947

theorem tailTrace_2310992 : CollatzResearch.WordTrace tailWord_2310992 prefixEnd_2310992 1186649684695327466871947 := by
  unfold tailWord_2310992
  simp only [CollatzResearch.WordTrace]
  refine ⟨42144401421839072428075615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56192535229118763237434153 42144401421839072428075615)
  ·
    refine ⟨63216602132758608642113423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42144401421839072428075615 63216602132758608642113423)
    ·
      refine ⟨94824903199137912963170135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63216602132758608642113423 94824903199137912963170135)
      ·
        refine ⟨142237354798706869444755203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94824903199137912963170135 142237354798706869444755203)
        ·
          refine ⟨213356032198060304167132805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142237354798706869444755203 213356032198060304167132805)
          ·
            refine ⟨40004256037136307031337401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 213356032198060304167132805 40004256037136307031337401)
            ·
              refine ⟨30003192027852230273503051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40004256037136307031337401 30003192027852230273503051)
              ·
                refine ⟨45004788041778345410254577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30003192027852230273503051 45004788041778345410254577)
                ·
                  refine ⟨33753591031333759057690933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45004788041778345410254577 33753591031333759057690933)
                  ·
                    refine ⟨3164399159187539911658525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 33753591031333759057690933 3164399159187539911658525)
                    ·
                      refine ⟨1186649684695327466871947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3164399159187539911658525 1186649684695327466871947)
                      ·
                        rfl

theorem cell23_2310992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 1, 2, 5, 3].length) (baseStart_2310992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2310992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2310992 prefixEnd_2310992 := by exact prefixLift 2310992
  have htrace : WordTrace (prefixWord ++ tailWord_2310992) baseStart_2310992 baseEnd_2310992 := by
    simpa [prefixWord, tailWord_2310992, baseEnd_2310992] using wordTrace_append hprefix tailTrace_2310992
  have hstable : (prefixWord ++ tailWord_2310992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2310992).length < 2 ^ (prefixWord ++ tailWord_2310992).sum := by decide
  have hdescent : baseEnd_2310992 < baseStart_2310992 := by decide
  rcases family_descends (prefixWord ++ tailWord_2310992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2311009 : List Nat := [1, 2, 3, 1, 1, 1, 2, 1, 7, 1, 3]
def baseStart_2311009 : Nat := 118140960795 + 2311009 * 2 ^ 59
def prefixEnd_2311009 : Nat := 4983230072969 + 3 ^ 40 * 2311009 * 2
def baseEnd_2311009 : Nat := 1186658413866453900359369

theorem tailTrace_2311009 : CollatzResearch.WordTrace tailWord_2311009 prefixEnd_2311009 1186658413866453900359369 := by
  unfold tailWord_2311009
  simp only [CollatzResearch.WordTrace]
  refine ⟨84289422884616556759520081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56192948589744371173013387 84289422884616556759520081)
  ·
    refine ⟨63217067163462417569640061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84289422884616556759520081 63217067163462417569640061)
    ·
      refine ⟨23706400186298406588615023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63217067163462417569640061 23706400186298406588615023)
      ·
        refine ⟨35559600279447609882922535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23706400186298406588615023 35559600279447609882922535)
        ·
          refine ⟨53339400419171414824383803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35559600279447609882922535 53339400419171414824383803)
          ·
            refine ⟨80009100628757122236575705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53339400419171414824383803 80009100628757122236575705)
            ·
              refine ⟨60006825471567841677431779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80009100628757122236575705 60006825471567841677431779)
              ·
                refine ⟨90010238207351762516147669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60006825471567841677431779 90010238207351762516147669)
                ·
                  refine ⟨2109614957984806933972211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 90010238207351762516147669 2109614957984806933972211)
                  ·
                    refine ⟨3164422436977210400958317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2109614957984806933972211 3164422436977210400958317)
                    ·
                      refine ⟨1186658413866453900359369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3164422436977210400958317 1186658413866453900359369)
                      ·
                        rfl

theorem cell23_2311009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 1, 7, 1, 3].length) (baseStart_2311009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2311009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2311009 prefixEnd_2311009 := by exact prefixLift 2311009
  have htrace : WordTrace (prefixWord ++ tailWord_2311009) baseStart_2311009 baseEnd_2311009 := by
    simpa [prefixWord, tailWord_2311009, baseEnd_2311009] using wordTrace_append hprefix tailTrace_2311009
  have hstable : (prefixWord ++ tailWord_2311009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2311009).length < 2 ^ (prefixWord ++ tailWord_2311009).sum := by decide
  have hdescent : baseEnd_2311009 < baseStart_2311009 := by decide
  rcases family_descends (prefixWord ++ tailWord_2311009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2311029 : List Nat := [1, 3, 4, 1, 1, 2, 1, 2, 3, 5]
def baseStart_2311029 : Nat := 118140960795 + 2311029 * 2 ^ 59
def prefixEnd_2311029 : Nat := 4983230072969 + 3 ^ 40 * 2311029 * 2
def baseEnd_2311029 : Nat := 395556227826514607369759

theorem tailTrace_2311029 : CollatzResearch.WordTrace tailWord_2311029 prefixEnd_2311029 395556227826514607369759 := by
  unfold tailWord_2311029
  simp only [CollatzResearch.WordTrace]
  refine ⟨84290152344544100175248141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56193434896362733450165427 84290152344544100175248141)
  ·
    refine ⟨31608807129204037565718053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84290152344544100175248141 31608807129204037565718053)
    ·
      refine ⟨5926651336725757043572135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31608807129204037565718053 5926651336725757043572135)
      ·
        refine ⟨8889977005088635565358203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5926651336725757043572135 8889977005088635565358203)
        ·
          refine ⟨13334965507632953348037305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8889977005088635565358203 13334965507632953348037305)
          ·
            refine ⟨10001224130724715011027979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13334965507632953348037305 10001224130724715011027979)
            ·
              refine ⟨15001836196087072516541969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10001224130724715011027979 15001836196087072516541969)
              ·
                refine ⟨11251377147065304387406477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15001836196087072516541969 11251377147065304387406477)
                ·
                  refine ⟨4219266430149489145277429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11251377147065304387406477 4219266430149489145277429)
                  ·
                    refine ⟨395556227826514607369759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4219266430149489145277429 395556227826514607369759)
                    ·
                      rfl

theorem cell23_2311029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 2, 3, 5].length) (baseStart_2311029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2311029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2311029 prefixEnd_2311029 := by exact prefixLift 2311029
  have htrace : WordTrace (prefixWord ++ tailWord_2311029) baseStart_2311029 baseEnd_2311029 := by
    simpa [prefixWord, tailWord_2311029, baseEnd_2311029] using wordTrace_append hprefix tailTrace_2311029
  have hstable : (prefixWord ++ tailWord_2311029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2311029).length < 2 ^ (prefixWord ++ tailWord_2311029).sum := by decide
  have hdescent : baseEnd_2311029 < baseStart_2311029 := by decide
  rcases family_descends (prefixWord ++ tailWord_2311029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2311049 : List Nat := [1, 2, 1, 1, 5, 2, 2, 1, 3, 1, 4]
def baseStart_2311049 : Nat := 118140960795 + 2311049 * 2 ^ 59
def prefixEnd_2311049 : Nat := 4983230072969 + 3 ^ 40 * 2311049 * 2
def baseEnd_2311049 : Nat := 1186678953092633743859185

theorem tailTrace_2311049 : CollatzResearch.WordTrace tailWord_2311049 prefixEnd_2311049 1186678953092633743859185 := by
  unfold tailWord_2311049
  simp only [CollatzResearch.WordTrace]
  refine ⟨84290881804471643590976201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56193921202981095727317467 84290881804471643590976201)
  ·
    refine ⟨63218161353353732693232151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84290881804471643590976201 63218161353353732693232151)
    ·
      refine ⟨94827242030030599039848227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63218161353353732693232151 94827242030030599039848227)
      ·
        refine ⟨142240863045045898559772341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94827242030030599039848227 142240863045045898559772341)
        ·
          refine ⟨13335080910473052989978657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 142240863045045898559772341 13335080910473052989978657)
          ·
            refine ⟨10001310682854789742483993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13335080910473052989978657 10001310682854789742483993)
            ·
              refine ⟨7500983012141092306862995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10001310682854789742483993 7500983012141092306862995)
              ·
                refine ⟨11251474518211638460294493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7500983012141092306862995 11251474518211638460294493)
                ·
                  refine ⟨4219302944329364422610435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11251474518211638460294493 4219302944329364422610435)
                  ·
                    refine ⟨6328954416494046633915653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4219302944329364422610435 6328954416494046633915653)
                    ·
                      refine ⟨1186678953092633743859185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6328954416494046633915653 1186678953092633743859185)
                      ·
                        rfl

theorem cell23_2311049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 2, 1, 3, 1, 4].length) (baseStart_2311049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2311049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2311049 prefixEnd_2311049 := by exact prefixLift 2311049
  have htrace : WordTrace (prefixWord ++ tailWord_2311049) baseStart_2311049 baseEnd_2311049 := by
    simpa [prefixWord, tailWord_2311049, baseEnd_2311049] using wordTrace_append hprefix tailTrace_2311049
  have hstable : (prefixWord ++ tailWord_2311049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2311049).length < 2 ^ (prefixWord ++ tailWord_2311049).sum := by decide
  have hdescent : baseEnd_2311049 < baseStart_2311049 := by decide
  rcases family_descends (prefixWord ++ tailWord_2311049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2311060 : List Nat := [2, 4, 2, 1, 1, 1, 4, 3, 1, 1, 3]
def baseStart_2311060 : Nat := 118140960795 + 2311060 * 2 ^ 59
def prefixEnd_2311060 : Nat := 4983230072969 + 3 ^ 40 * 2311060 * 2
def baseEnd_2311060 : Nat := 1186684601379833200821635

theorem tailTrace_2311060 : CollatzResearch.WordTrace tailWord_2311060 prefixEnd_2311060 1186684601379833200821635 := by
  unfold tailWord_2311060
  simp only [CollatzResearch.WordTrace]
  refine ⟨42145641503715896234813317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56194188671621194979751089 42145641503715896234813317)
  ·
    refine ⟨7902307781946730544027497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42145641503715896234813317 7902307781946730544027497)
    ·
      refine ⟨5926730836460047908020623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7902307781946730544027497 5926730836460047908020623)
      ·
        refine ⟨8890096254690071862030935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5926730836460047908020623 8890096254690071862030935)
        ·
          refine ⟨13335144382035107793046403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8890096254690071862030935 13335144382035107793046403)
          ·
            refine ⟨20002716573052661689569605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13335144382035107793046403 20002716573052661689569605)
            ·
              refine ⟨3750509357447374066794301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20002716573052661689569605 3750509357447374066794301)
              ·
                refine ⟨1406441009042765275047863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3750509357447374066794301 1406441009042765275047863)
                ·
                  refine ⟨2109661513564147912571795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1406441009042765275047863 2109661513564147912571795)
                  ·
                    refine ⟨3164492270346221868857693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2109661513564147912571795 3164492270346221868857693)
                    ·
                      refine ⟨1186684601379833200821635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3164492270346221868857693 1186684601379833200821635)
                      ·
                        rfl

theorem cell23_2311060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 4, 3, 1, 1, 3].length) (baseStart_2311060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2311060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2311060 prefixEnd_2311060 := by exact prefixLift 2311060
  have htrace : WordTrace (prefixWord ++ tailWord_2311060) baseStart_2311060 baseEnd_2311060 := by
    simpa [prefixWord, tailWord_2311060, baseEnd_2311060] using wordTrace_append hprefix tailTrace_2311060
  have hstable : (prefixWord ++ tailWord_2311060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2311060).length < 2 ^ (prefixWord ++ tailWord_2311060).sum := by decide
  have hdescent : baseEnd_2311060 < baseStart_2311060 := by decide
  rcases family_descends (prefixWord ++ tailWord_2311060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2311069 : List Nat := [1, 4, 2, 1, 2, 1, 2, 3, 1, 1, 5]
def baseStart_2311069 : Nat := 118140960795 + 2311069 * 2 ^ 59
def prefixEnd_2311069 : Nat := 4983230072969 + 3 ^ 40 * 2311069 * 2
def baseEnd_2311069 : Nat := 1186689222705723665609093

theorem tailTrace_2311069 : CollatzResearch.WordTrace tailWord_2311069 prefixEnd_2311069 1186689222705723665609093 := by
  unfold tailWord_2311069
  simp only [CollatzResearch.WordTrace]
  refine ⟨84291611264399187006704261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56194407509599458004469507 84291611264399187006704261)
  ·
    refine ⟨15804677112074847563757049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 84291611264399187006704261 15804677112074847563757049)
    ·
      refine ⟨11853507834056135672817787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15804677112074847563757049 11853507834056135672817787)
      ·
        refine ⟨17780261751084203509226681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11853507834056135672817787 17780261751084203509226681)
        ·
          refine ⟨13335196313313152631920011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17780261751084203509226681 13335196313313152631920011)
          ·
            refine ⟨20002794469969728947880017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13335196313313152631920011 20002794469969728947880017)
            ·
              refine ⟨15002095852477296710910013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20002794469969728947880017 15002095852477296710910013)
              ·
                refine ⟨5625785944678986266591255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15002095852477296710910013 5625785944678986266591255)
                ·
                  refine ⟨8438678917018479399886883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5625785944678986266591255 8438678917018479399886883)
                  ·
                    refine ⟨12658018375527719099830325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8438678917018479399886883 12658018375527719099830325)
                    ·
                      refine ⟨1186689222705723665609093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12658018375527719099830325 1186689222705723665609093)
                      ·
                        rfl

theorem cell23_2311069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 3, 1, 1, 5].length) (baseStart_2311069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2311069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2311069 prefixEnd_2311069 := by exact prefixLift 2311069
  have htrace : WordTrace (prefixWord ++ tailWord_2311069) baseStart_2311069 baseEnd_2311069 := by
    simpa [prefixWord, tailWord_2311069, baseEnd_2311069] using wordTrace_append hprefix tailTrace_2311069
  have hstable : (prefixWord ++ tailWord_2311069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2311069).length < 2 ^ (prefixWord ++ tailWord_2311069).sum := by decide
  have hdescent : baseEnd_2311069 < baseStart_2311069 := by decide
  rcases family_descends (prefixWord ++ tailWord_2311069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2311093 : List Nat := [1, 3, 3, 2, 1, 1, 5, 1, 2, 4]
def baseStart_2311093 : Nat := 118140960795 + 2311093 * 2 ^ 59
def prefixEnd_2311093 : Nat := 4983230072969 + 3 ^ 40 * 2311093 * 2
def baseEnd_2311093 : Nat := 395567182080477190569661

theorem tailTrace_2311093 : CollatzResearch.WordTrace tailWord_2311093 prefixEnd_2311093 395567182080477190569661 := by
  unfold tailWord_2311093
  simp only [CollatzResearch.WordTrace]
  refine ⟨84292486616312239105577933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56194991077541492737051955 84292486616312239105577933)
  ·
    refine ⟨31609682481117089664591725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84292486616312239105577933 31609682481117089664591725)
    ·
      refine ⟨11853630930418908624221897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31609682481117089664591725 11853630930418908624221897)
      ·
        refine ⟨8890223197814181468166423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11853630930418908624221897 8890223197814181468166423)
        ·
          refine ⟨13335334796721272202249635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8890223197814181468166423 13335334796721272202249635)
          ·
            refine ⟨20003002195081908303374453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13335334796721272202249635 20003002195081908303374453)
            ·
              refine ⟨1875281455788928903441355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20003002195081908303374453 1875281455788928903441355)
              ·
                refine ⟨2812922183683393355162033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1875281455788928903441355 2812922183683393355162033)
                ·
                  refine ⟨2109691637762545016371525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2812922183683393355162033 2109691637762545016371525)
                  ·
                    refine ⟨395567182080477190569661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2109691637762545016371525 395567182080477190569661)
                    ·
                      rfl

theorem cell23_2311093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 5, 1, 2, 4].length) (baseStart_2311093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2311093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2311093 prefixEnd_2311093 := by exact prefixLift 2311093
  have htrace : WordTrace (prefixWord ++ tailWord_2311093) baseStart_2311093 baseEnd_2311093 := by
    simpa [prefixWord, tailWord_2311093, baseEnd_2311093] using wordTrace_append hprefix tailTrace_2311093
  have hstable : (prefixWord ++ tailWord_2311093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2311093).length < 2 ^ (prefixWord ++ tailWord_2311093).sum := by decide
  have hdescent : baseEnd_2311093 < baseStart_2311093 := by decide
  rcases family_descends (prefixWord ++ tailWord_2311093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2311096 : List Nat := [2, 1, 2, 1, 2, 6, 1, 1, 1, 2, 4]
def baseStart_2311096 : Nat := 118140960795 + 2311096 * 2 ^ 59
def prefixEnd_2311096 : Nat := 4983230072969 + 3 ^ 40 * 2311096 * 2
def baseEnd_2311096 : Nat := 1186703086683395059971469

theorem tailTrace_2311096 : CollatzResearch.WordTrace tailWord_2311096 prefixEnd_2311096 1186703086683395059971469 := by
  unfold tailWord_2311096
  simp only [CollatzResearch.WordTrace]
  refine ⟨42146298017650685308968571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56195064023534247078624761 42146298017650685308968571)
  ·
    refine ⟨63219447026476027963452857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42146298017650685308968571 63219447026476027963452857)
    ·
      refine ⟨47414585269857020972589643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63219447026476027963452857 47414585269857020972589643)
      ·
        refine ⟨71121877904785531458884465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47414585269857020972589643 71121877904785531458884465)
        ·
          refine ⟨53341408428589148594163349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71121877904785531458884465 53341408428589148594163349)
          ·
            refine ⟨2500378520090116340351407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 53341408428589148594163349 2500378520090116340351407)
            ·
              refine ⟨3750567780135174510527111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2500378520090116340351407 3750567780135174510527111)
              ·
                refine ⟨5625851670202761765790667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3750567780135174510527111 5625851670202761765790667)
                ·
                  refine ⟨8438777505304142648686001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5625851670202761765790667 8438777505304142648686001)
                  ·
                    refine ⟨6329083128978106986514501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8438777505304142648686001 6329083128978106986514501)
                    ·
                      refine ⟨1186703086683395059971469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6329083128978106986514501 1186703086683395059971469)
                      ·
                        rfl

theorem cell23_2311096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 1, 1, 1, 2, 4].length) (baseStart_2311096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2311096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2311096 prefixEnd_2311096 := by exact prefixLift 2311096
  have htrace : WordTrace (prefixWord ++ tailWord_2311096) baseStart_2311096 baseEnd_2311096 := by
    simpa [prefixWord, tailWord_2311096, baseEnd_2311096] using wordTrace_append hprefix tailTrace_2311096
  have hstable : (prefixWord ++ tailWord_2311096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2311096).length < 2 ^ (prefixWord ++ tailWord_2311096).sum := by decide
  have hdescent : baseEnd_2311096 < baseStart_2311096 := by decide
  rcases family_descends (prefixWord ++ tailWord_2311096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2311116 : List Nat := [2, 2, 1, 4, 1, 1, 1, 1, 6, 1, 3]
def baseStart_2311116 : Nat := 118140960795 + 2311116 * 2 ^ 59
def prefixEnd_2311116 : Nat := 4983230072969 + 3 ^ 40 * 2311116 * 2
def baseEnd_2311116 : Nat := 1186713356296484981721377

theorem tailTrace_2311116 : CollatzResearch.WordTrace tailWord_2311116 prefixEnd_2311116 1186713356296484981721377 := by
  unfold tailWord_2311116
  simp only [CollatzResearch.WordTrace]
  refine ⟨42146662747614457016832601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56195550330152609355776801 42146662747614457016832601)
  ·
    refine ⟨31609997060710842762624451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42146662747614457016832601 31609997060710842762624451)
    ·
      refine ⟨47414995591066264143936677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31609997060710842762624451 47414995591066264143936677)
      ·
        refine ⟨8890311673324924526988127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47414995591066264143936677 8890311673324924526988127)
        ·
          refine ⟨13335467509987386790482191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8890311673324924526988127 13335467509987386790482191)
          ·
            refine ⟨20003201264981080185723287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13335467509987386790482191 20003201264981080185723287)
            ·
              refine ⟨30004801897471620278584931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20003201264981080185723287 30004801897471620278584931)
              ·
                refine ⟨45007202846207430417877397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30004801897471620278584931 45007202846207430417877397)
                ·
                  refine ⟨2109712633415973300838003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 45007202846207430417877397 2109712633415973300838003)
                  ·
                    refine ⟨3164568950123959951257005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2109712633415973300838003 3164568950123959951257005)
                    ·
                      refine ⟨1186713356296484981721377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3164568950123959951257005 1186713356296484981721377)
                      ·
                        rfl

theorem cell23_2311116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 1, 6, 1, 3].length) (baseStart_2311116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2311116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2311116 prefixEnd_2311116 := by exact prefixLift 2311116
  have htrace : WordTrace (prefixWord ++ tailWord_2311116) baseStart_2311116 baseEnd_2311116 := by
    simpa [prefixWord, tailWord_2311116, baseEnd_2311116] using wordTrace_append hprefix tailTrace_2311116
  have hstable : (prefixWord ++ tailWord_2311116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2311116).length < 2 ^ (prefixWord ++ tailWord_2311116).sum := by decide
  have hdescent : baseEnd_2311116 < baseStart_2311116 := by decide
  rcases family_descends (prefixWord ++ tailWord_2311116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2311133 : List Nat := [1, 4, 3, 1, 2, 1, 2, 1, 4, 1, 3]
def baseStart_2311133 : Nat := 118140960795 + 2311133 * 2 ^ 59
def prefixEnd_2311133 : Nat := 4983230072969 + 3 ^ 40 * 2311133 * 2
def baseEnd_2311133 : Nat := 1186722085467611415208799

theorem tailTrace_2311133 : CollatzResearch.WordTrace tailWord_2311133 prefixEnd_2311133 1186722085467611415208799 := by
  unfold tailWord_2311133
  simp only [CollatzResearch.WordTrace]
  refine ⟨84293945536167325937034053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56195963690778217291356035 84293945536167325937034053)
  ·
    refine ⟨15805114788031373613193885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 84293945536167325937034053 15805114788031373613193885)
    ·
      refine ⟨5926918045511765104947707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15805114788031373613193885 5926918045511765104947707)
      ·
        refine ⟨8890377068267647657421561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5926918045511765104947707 8890377068267647657421561)
        ·
          refine ⟨6667782801200735743066171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8890377068267647657421561 6667782801200735743066171)
          ·
            refine ⟨10001674201801103614599257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6667782801200735743066171 10001674201801103614599257)
            ·
              refine ⟨7501255651350827710949443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10001674201801103614599257 7501255651350827710949443)
              ·
                refine ⟨11251883477026241566424165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7501255651350827710949443 11251883477026241566424165)
                ·
                  refine ⟨2109728151942420293704531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11251883477026241566424165 2109728151942420293704531)
                  ·
                    refine ⟨3164592227913630440556797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2109728151942420293704531 3164592227913630440556797)
                    ·
                      refine ⟨1186722085467611415208799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3164592227913630440556797 1186722085467611415208799)
                      ·
                        rfl

theorem cell23_2311133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 2, 1, 4, 1, 3].length) (baseStart_2311133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2311133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2311133 prefixEnd_2311133 := by exact prefixLift 2311133
  have htrace : WordTrace (prefixWord ++ tailWord_2311133) baseStart_2311133 baseEnd_2311133 := by
    simpa [prefixWord, tailWord_2311133, baseEnd_2311133] using wordTrace_append hprefix tailTrace_2311133
  have hstable : (prefixWord ++ tailWord_2311133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2311133).length < 2 ^ (prefixWord ++ tailWord_2311133).sum := by decide
  have hdescent : baseEnd_2311133 < baseStart_2311133 := by decide
  rcases family_descends (prefixWord ++ tailWord_2311133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2311139 : List Nat := [1, 1, 1, 6, 1, 1, 2, 1, 2, 3, 4]
def baseStart_2311139 : Nat := 118140960795 + 2311139 * 2 ^ 59
def prefixEnd_2311139 : Nat := 4983230072969 + 3 ^ 40 * 2311139 * 2
def baseEnd_2311139 : Nat := 1186725166351538391733771

theorem tailTrace_2311139 : CollatzResearch.WordTrace tailWord_2311139 prefixEnd_2311139 1186725166351538391733771 := by
  unfold tailWord_2311139
  simp only [CollatzResearch.WordTrace]
  refine ⟨84294164374145588961752471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56196109582763725974501647 84294164374145588961752471)
  ·
    refine ⟨126441246561218383442628707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84294164374145588961752471 126441246561218383442628707)
    ·
      refine ⟨189661869841827575163943061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126441246561218383442628707 189661869841827575163943061)
      ·
        refine ⟨8890400148835667585809831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 189661869841827575163943061 8890400148835667585809831)
        ·
          refine ⟨13335600223253501378714747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8890400148835667585809831 13335600223253501378714747)
          ·
            refine ⟨20003400334880252068072121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13335600223253501378714747 20003400334880252068072121)
            ·
              refine ⟨15002550251160189051054091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20003400334880252068072121 15002550251160189051054091)
              ·
                refine ⟨22503825376740283576581137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15002550251160189051054091 22503825376740283576581137)
                ·
                  refine ⟨16877869032555212682435853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22503825376740283576581137 16877869032555212682435853)
                  ·
                    refine ⟨6329200887208204755913445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16877869032555212682435853 6329200887208204755913445)
                    ·
                      refine ⟨1186725166351538391733771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6329200887208204755913445 1186725166351538391733771)
                      ·
                        rfl

theorem cell23_2311139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 1, 2, 3, 4].length) (baseStart_2311139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2311139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2311139 prefixEnd_2311139 := by exact prefixLift 2311139
  have htrace : WordTrace (prefixWord ++ tailWord_2311139) baseStart_2311139 baseEnd_2311139 := by
    simpa [prefixWord, tailWord_2311139, baseEnd_2311139] using wordTrace_append hprefix tailTrace_2311139
  have hstable : (prefixWord ++ tailWord_2311139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2311139).length < 2 ^ (prefixWord ++ tailWord_2311139).sum := by decide
  have hdescent : baseEnd_2311139 < baseStart_2311139 := by decide
  rcases family_descends (prefixWord ++ tailWord_2311139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2311150 : List Nat := [4, 1, 2, 1, 4, 1, 1, 3, 2, 1, 3]
def baseStart_2311150 : Nat := 118140960795 + 2311150 * 2 ^ 59
def prefixEnd_2311150 : Nat := 4983230072969 + 3 ^ 40 * 2311150 * 2
def baseEnd_2311150 : Nat := 1186730814638737848696221

theorem tailTrace_2311150 : CollatzResearch.WordTrace tailWord_2311150 prefixEnd_2311150 1186730814638737848696221 := by
  unfold tailWord_2311150
  simp only [CollatzResearch.WordTrace]
  refine ⟨10536820697138217230050363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56196377051403825226935269 10536820697138217230050363)
  ·
    refine ⟨15805231045707325845075545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10536820697138217230050363 15805231045707325845075545)
    ·
      refine ⟨11853923284280494383806659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15805231045707325845075545 11853923284280494383806659)
      ·
        refine ⟨17780884926420741575709989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11853923284280494383806659 17780884926420741575709989)
        ·
          refine ⟨3333915923703889045445623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17780884926420741575709989 3333915923703889045445623)
          ·
            refine ⟨5000873885555833568168435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3333915923703889045445623 5000873885555833568168435)
            ·
              refine ⟨7501310828333750352252653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5000873885555833568168435 7501310828333750352252653)
              ·
                refine ⟨2812991560625156382094745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7501310828333750352252653 2812991560625156382094745)
                ·
                  refine ⟨2109743670468867286571059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2812991560625156382094745 2109743670468867286571059)
                  ·
                    refine ⟨3164615505703300929856589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2109743670468867286571059 3164615505703300929856589)
                    ·
                      refine ⟨1186730814638737848696221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3164615505703300929856589 1186730814638737848696221)
                      ·
                        rfl

theorem cell23_2311150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 1, 3, 2, 1, 3].length) (baseStart_2311150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2311150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2311150 prefixEnd_2311150 := by exact prefixLift 2311150
  have htrace : WordTrace (prefixWord ++ tailWord_2311150) baseStart_2311150 baseEnd_2311150 := by
    simpa [prefixWord, tailWord_2311150, baseEnd_2311150] using wordTrace_append hprefix tailTrace_2311150
  have hstable : (prefixWord ++ tailWord_2311150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2311150).length < 2 ^ (prefixWord ++ tailWord_2311150).sum := by decide
  have hdescent : baseEnd_2311150 < baseStart_2311150 := by decide
  rcases family_descends (prefixWord ++ tailWord_2311150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2311207 : List Nat := [1, 1, 7, 1, 1, 1, 2, 3, 2, 2, 2]
def baseStart_2311207 : Nat := 118140960795 + 2311207 * 2 ^ 59
def prefixEnd_2311207 : Nat := 4983230072969 + 3 ^ 40 * 2311207 * 2
def baseEnd_2311207 : Nat := 1186760083036044125683459

theorem tailTrace_2311207 : CollatzResearch.WordTrace tailWord_2311207 prefixEnd_2311207 1186760083036044125683459 := by
  unfold tailWord_2311207
  simp only [CollatzResearch.WordTrace]
  refine ⟨84296644537899236575227875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56197763025266157716818583 84296644537899236575227875)
  ·
    refine ⟨126444966806848854862841813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84296644537899236575227875 126444966806848854862841813)
    ·
      refine ⟨2963553909535520035847855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 126444966806848854862841813 2963553909535520035847855)
      ·
        refine ⟨4445330864303280053771783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2963553909535520035847855 4445330864303280053771783)
        ·
          refine ⟨6667996296454920080657675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4445330864303280053771783 6667996296454920080657675)
          ·
            refine ⟨10001994444682380120986513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6667996296454920080657675 10001994444682380120986513)
            ·
              refine ⟨7501495833511785090739885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10001994444682380120986513 7501495833511785090739885)
              ·
                refine ⟨2813060937566919409027457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7501495833511785090739885 2813060937566919409027457)
                ·
                  refine ⟨2109795703175189556770593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2813060937566919409027457 2109795703175189556770593)
                  ·
                    refine ⟨1582346777381392167577945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2109795703175189556770593 1582346777381392167577945)
                    ·
                      refine ⟨1186760083036044125683459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1582346777381392167577945 1186760083036044125683459)
                      ·
                        rfl

theorem cell23_2311207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 2, 3, 2, 2, 2].length) (baseStart_2311207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2311207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2311207 prefixEnd_2311207 := by exact prefixLift 2311207
  have htrace : WordTrace (prefixWord ++ tailWord_2311207) baseStart_2311207 baseEnd_2311207 := by
    simpa [prefixWord, tailWord_2311207, baseEnd_2311207] using wordTrace_append hprefix tailTrace_2311207
  have hstable : (prefixWord ++ tailWord_2311207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2311207).length < 2 ^ (prefixWord ++ tailWord_2311207).sum := by decide
  have hdescent : baseEnd_2311207 < baseStart_2311207 := by decide
  rcases family_descends (prefixWord ++ tailWord_2311207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2311216 : List Nat := [2, 1, 1, 1, 2, 4, 1, 2, 2, 5, 2]
def baseStart_2311216 : Nat := 118140960795 + 2311216 * 2 ^ 59
def prefixEnd_2311216 : Nat := 4983230072969 + 3 ^ 40 * 2311216 * 2
def baseEnd_2311216 : Nat := 1186764704361934590470917

theorem tailTrace_2311216 : CollatzResearch.WordTrace tailWord_2311216 prefixEnd_2311216 1186764704361934590470917 := by
  unfold tailWord_2311216
  simp only [CollatzResearch.WordTrace]
  refine ⟨42148486397433315556152751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56197981863244420741537001 42148486397433315556152751)
  ·
    refine ⟨63222729596149973334229127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42148486397433315556152751 63222729596149973334229127)
    ·
      refine ⟨94834094394224960001343691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63222729596149973334229127 94834094394224960001343691)
      ·
        refine ⟨142251141591337440002015537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94834094394224960001343691 142251141591337440002015537)
        ·
          refine ⟨106688356193503080001511653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 142251141591337440002015537 106688356193503080001511653)
          ·
            refine ⟨20004066786281827500283435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 106688356193503080001511653 20004066786281827500283435)
            ·
              refine ⟨30006100179422741250425153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20004066786281827500283435 30006100179422741250425153)
              ·
                refine ⟨22504575134567055937818865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30006100179422741250425153 22504575134567055937818865)
                ·
                  refine ⟨16878431350925291953364149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22504575134567055937818865 16878431350925291953364149)
                  ·
                    refine ⟨1582352939149246120627889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 16878431350925291953364149 1582352939149246120627889)
                    ·
                      refine ⟨1186764704361934590470917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1582352939149246120627889 1186764704361934590470917)
                      ·
                        rfl

theorem cell23_2311216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 2, 2, 5, 2].length) (baseStart_2311216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2311216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2311216 prefixEnd_2311216 := by exact prefixLift 2311216
  have htrace : WordTrace (prefixWord ++ tailWord_2311216) baseStart_2311216 baseEnd_2311216 := by
    simpa [prefixWord, tailWord_2311216, baseEnd_2311216] using wordTrace_append hprefix tailTrace_2311216
  have hstable : (prefixWord ++ tailWord_2311216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2311216).length < 2 ^ (prefixWord ++ tailWord_2311216).sum := by decide
  have hdescent : baseEnd_2311216 < baseStart_2311216 := by decide
  rcases family_descends (prefixWord ++ tailWord_2311216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2311226 : List Nat := [3, 1, 1, 1, 3, 1, 5, 1, 2, 5]
def baseStart_2311226 : Nat := 118140960795 + 2311226 * 2 ^ 59
def prefixEnd_2311226 : Nat := 4983230072969 + 3 ^ 40 * 2311226 * 2
def baseEnd_2311226 : Nat := 395589946389493183781957

theorem tailTrace_2311226 : CollatzResearch.WordTrace tailWord_2311226 prefixEnd_2311226 395589946389493183781957 := by
  unfold tailWord_2311226
  simp only [CollatzResearch.WordTrace]
  refine ⟨21074334381207600705042383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56198225016553601880113021 21074334381207600705042383)
  ·
    refine ⟨31611501571811401057563575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21074334381207600705042383 31611501571811401057563575)
    ·
      refine ⟨47417252357717101586345363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31611501571811401057563575 47417252357717101586345363)
      ·
        refine ⟨71125878536575652379518045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47417252357717101586345363 71125878536575652379518045)
        ·
          refine ⟨26672204451215869642319267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71125878536575652379518045 26672204451215869642319267)
          ·
            refine ⟨40008306676823804463478901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26672204451215869642319267 40008306676823804463478901)
            ·
              refine ⟨3750778750952231668451147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 40008306676823804463478901 3750778750952231668451147)
              ·
                refine ⟨5626168126428347502676721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3750778750952231668451147 5626168126428347502676721)
                ·
                  refine ⟨4219626094821260627007541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5626168126428347502676721 4219626094821260627007541)
                  ·
                    refine ⟨395589946389493183781957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4219626094821260627007541 395589946389493183781957)
                    ·
                      rfl

theorem cell23_2311226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 5, 1, 2, 5].length) (baseStart_2311226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2311226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2311226 prefixEnd_2311226 := by exact prefixLift 2311226
  have htrace : WordTrace (prefixWord ++ tailWord_2311226) baseStart_2311226 baseEnd_2311226 := by
    simpa [prefixWord, tailWord_2311226, baseEnd_2311226] using wordTrace_append hprefix tailTrace_2311226
  have hstable : (prefixWord ++ tailWord_2311226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2311226).length < 2 ^ (prefixWord ++ tailWord_2311226).sum := by decide
  have hdescent : baseEnd_2311226 < baseStart_2311226 := by decide
  rcases family_descends (prefixWord ++ tailWord_2311226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2311230 : List Nat := [4, 2, 1, 3, 1, 2, 2, 3, 5]
def baseStart_2311230 : Nat := 118140960795 + 2311230 * 2 ^ 59
def prefixEnd_2311230 : Nat := 4983230072969 + 3 ^ 40 * 2311230 * 2
def baseEnd_2311230 : Nat := 131863543676788615077317

theorem tailTrace_2311230 : CollatzResearch.WordTrace tailWord_2311230 prefixEnd_2311230 131863543676788615077317 := by
  unfold tailWord_2311230
  simp only [CollatzResearch.WordTrace]
  refine ⟨10537185427101988937914393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56198322277877274335543429 10537185427101988937914393)
  ·
    refine ⟨7902889070326491703435795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10537185427101988937914393 7902889070326491703435795)
    ·
      refine ⟨11854333605489737555153693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7902889070326491703435795 11854333605489737555153693)
      ·
        refine ⟨4445375102058651583182635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11854333605489737555153693 4445375102058651583182635)
        ·
          refine ⟨6668062653087977374773953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4445375102058651583182635 6668062653087977374773953)
          ·
            refine ⟨5001046989815983031080465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6668062653087977374773953 5001046989815983031080465)
            ·
              refine ⟨3750785242361987273310349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5001046989815983031080465 3750785242361987273310349)
              ·
                refine ⟨1406544465885745227491381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3750785242361987273310349 1406544465885745227491381)
                ·
                  refine ⟨131863543676788615077317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1406544465885745227491381 131863543676788615077317)
                  ·
                    rfl

theorem cell23_2311230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 2, 3, 5].length) (baseStart_2311230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2311230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2311230 prefixEnd_2311230 := by exact prefixLift 2311230
  have htrace : WordTrace (prefixWord ++ tailWord_2311230) baseStart_2311230 baseEnd_2311230 := by
    simpa [prefixWord, tailWord_2311230, baseEnd_2311230] using wordTrace_append hprefix tailTrace_2311230
  have hstable : (prefixWord ++ tailWord_2311230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2311230).length < 2 ^ (prefixWord ++ tailWord_2311230).sum := by decide
  have hdescent : baseEnd_2311230 < baseStart_2311230 := by decide
  rcases family_descends (prefixWord ++ tailWord_2311230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2311246 : List Nat := [4, 1, 1, 1, 1, 3, 2, 1, 4, 1, 4]
def baseStart_2311246 : Nat := 118140960795 + 2311246 * 2 ^ 59
def prefixEnd_2311246 : Nat := 4983230072969 + 3 ^ 40 * 2311246 * 2
def baseEnd_2311246 : Nat := 1186780108781569473095779

theorem tailTrace_2311246 : CollatzResearch.WordTrace tailWord_2311246 prefixEnd_2311246 1186780108781569473095779 := by
  unfold tailWord_2311246
  simp only [CollatzResearch.WordTrace]
  refine ⟨10537258373094743279487199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56198711323171964157265061 10537258373094743279487199)
  ·
    refine ⟨15805887559642114919230799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10537258373094743279487199 15805887559642114919230799)
    ·
      refine ⟨23708831339463172378846199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15805887559642114919230799 23708831339463172378846199)
      ·
        refine ⟨35563247009194758568269299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23708831339463172378846199 35563247009194758568269299)
        ·
          refine ⟨53344870513792137852403949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35563247009194758568269299 53344870513792137852403949)
          ·
            refine ⟨20004326442672051694651481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53344870513792137852403949 20004326442672051694651481)
            ·
              refine ⟨15003244832004038770988611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20004326442672051694651481 15003244832004038770988611)
              ·
                refine ⟨22504867248006058156482917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15003244832004038770988611 22504867248006058156482917)
                ·
                  refine ⟨4219662609001135904340547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22504867248006058156482917 4219662609001135904340547)
                  ·
                    refine ⟨6329493913501703856510821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4219662609001135904340547 6329493913501703856510821)
                    ·
                      refine ⟨1186780108781569473095779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6329493913501703856510821 1186780108781569473095779)
                      ·
                        rfl

theorem cell23_2311246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 1, 4, 1, 4].length) (baseStart_2311246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2311246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2311246 prefixEnd_2311246 := by exact prefixLift 2311246
  have htrace : WordTrace (prefixWord ++ tailWord_2311246) baseStart_2311246 baseEnd_2311246 := by
    simpa [prefixWord, tailWord_2311246, baseEnd_2311246] using wordTrace_append hprefix tailTrace_2311246
  have hstable : (prefixWord ++ tailWord_2311246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2311246).length < 2 ^ (prefixWord ++ tailWord_2311246).sum := by decide
  have hdescent : baseEnd_2311246 < baseStart_2311246 := by decide
  rcases family_descends (prefixWord ++ tailWord_2311246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2311249 : List Nat := [1, 2, 2, 1, 3, 1, 2, 1, 2, 3, 5]
def baseStart_2311249 : Nat := 118140960795 + 2311249 * 2 ^ 59
def prefixEnd_2311249 : Nat := 4983230072969 + 3 ^ 40 * 2311249 * 2
def baseEnd_2311249 : Nat := 1186781649223532961358265

theorem tailTrace_2311249 : CollatzResearch.WordTrace tailWord_2311249 prefixEnd_2311249 1186781649223532961358265 := by
  unfold tailWord_2311249
  simp only [CollatzResearch.WordTrace]
  refine ⟨84298176403747077748256801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56198784269164718498837867 84298176403747077748256801)
  ·
    refine ⟨63223632302810308311192601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84298176403747077748256801 63223632302810308311192601)
    ·
      refine ⟨47417724227107731233394451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63223632302810308311192601 47417724227107731233394451)
      ·
        refine ⟨71126586340661596850091677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47417724227107731233394451 71126586340661596850091677)
        ·
          refine ⟨26672469877748098818784379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71126586340661596850091677 26672469877748098818784379)
          ·
            refine ⟨40008704816622148228176569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26672469877748098818784379 40008704816622148228176569)
            ·
              refine ⟨30006528612466611171132427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40008704816622148228176569 30006528612466611171132427)
              ·
                refine ⟨45009792918699916756698641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30006528612466611171132427 45009792918699916756698641)
                ·
                  refine ⟨33757344689024937567523981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45009792918699916756698641 33757344689024937567523981)
                  ·
                    refine ⟨12659004258384351587821493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 33757344689024937567523981 12659004258384351587821493)
                    ·
                      refine ⟨1186781649223532961358265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12659004258384351587821493 1186781649223532961358265)
                      ·
                        rfl

theorem cell23_2311249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 1, 2, 3, 5].length) (baseStart_2311249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2311249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2311249 prefixEnd_2311249 := by exact prefixLift 2311249
  have htrace : WordTrace (prefixWord ++ tailWord_2311249) baseStart_2311249 baseEnd_2311249 := by
    simpa [prefixWord, tailWord_2311249, baseEnd_2311249] using wordTrace_append hprefix tailTrace_2311249
  have hstable : (prefixWord ++ tailWord_2311249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2311249).length < 2 ^ (prefixWord ++ tailWord_2311249).sum := by decide
  have hdescent : baseEnd_2311249 < baseStart_2311249 := by decide
  rcases family_descends (prefixWord ++ tailWord_2311249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2311286 : List Nat := [5, 1, 1, 2, 1, 1, 1, 1, 10]
def baseStart_2311286 : Nat := 118140960795 + 2311286 * 2 ^ 59
def prefixEnd_2311286 : Nat := 4983230072969 + 3 ^ 40 * 2311286 * 2
def baseEnd_2311286 : Nat := 131866738667527701843955

theorem tailTrace_2311286 : CollatzResearch.WordTrace tailWord_2311286 prefixEnd_2311286 131866738667527701843955 := by
  unfold tailWord_2311286
  simp only [CollatzResearch.WordTrace]
  refine ⟨5268720369038314566709607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 56199683936408688711569141 5268720369038314566709607)
  ·
    refine ⟨7903080553557471850064411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5268720369038314566709607 7903080553557471850064411)
    ·
      refine ⟨11854620830336207775096617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7903080553557471850064411 11854620830336207775096617)
      ·
        refine ⟨8890965622752155831322463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11854620830336207775096617 8890965622752155831322463)
        ·
          refine ⟨13336448434128233746983695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8890965622752155831322463 13336448434128233746983695)
          ·
            refine ⟨20004672651192350620475543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13336448434128233746983695 20004672651192350620475543)
            ·
              refine ⟨30007008976788525930713315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20004672651192350620475543 30007008976788525930713315)
              ·
                refine ⟨45010513465182788896069973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30007008976788525930713315 45010513465182788896069973)
                ·
                  refine ⟨131866738667527701843955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 45010513465182788896069973 131866738667527701843955)
                  ·
                    rfl

theorem cell23_2311286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 1, 10].length) (baseStart_2311286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2311286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2311286 prefixEnd_2311286 := by exact prefixLift 2311286
  have htrace : WordTrace (prefixWord ++ tailWord_2311286) baseStart_2311286 baseEnd_2311286 := by
    simpa [prefixWord, tailWord_2311286, baseEnd_2311286] using wordTrace_append hprefix tailTrace_2311286
  have hstable : (prefixWord ++ tailWord_2311286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2311286).length < 2 ^ (prefixWord ++ tailWord_2311286).sum := by decide
  have hdescent : baseEnd_2311286 < baseStart_2311286 := by decide
  rcases family_descends (prefixWord ++ tailWord_2311286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2311320 : List Nat := [2, 1, 2, 4, 2, 3, 2, 1, 6]
def baseStart_2311320 : Nat := 118140960795 + 2311320 * 2 ^ 59
def prefixEnd_2311320 : Nat := 4983230072969 + 3 ^ 40 * 2311320 * 2
def baseEnd_2311320 : Nat := 131868678483333575952271

theorem tailTrace_2311320 : CollatzResearch.WordTrace tailWord_2311320 prefixEnd_2311320 131868678483333575952271 := by
  unfold tailWord_2311320
  simp only [CollatzResearch.WordTrace]
  refine ⟨42150382993244928437045707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56200510657659904582727609 42150382993244928437045707)
  ·
    refine ⟨63225574489867392655568561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42150382993244928437045707 63225574489867392655568561)
    ·
      refine ⟨47419180867400544491676421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63225574489867392655568561 47419180867400544491676421)
      ·
        refine ⟨8891096412637602092189329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47419180867400544491676421 8891096412637602092189329)
        ·
          refine ⟨6668322309478201569141997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8891096412637602092189329 6668322309478201569141997)
          ·
            refine ⟨2500620866054325588428249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6668322309478201569141997 2500620866054325588428249)
            ·
              refine ⟨1875465649540744191321187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2500620866054325588428249 1875465649540744191321187)
              ·
                refine ⟨2813198474311116286981781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1875465649540744191321187 2813198474311116286981781)
                ·
                  refine ⟨131868678483333575952271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2813198474311116286981781 131868678483333575952271)
                  ·
                    rfl

theorem cell23_2311320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 2, 1, 6].length) (baseStart_2311320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2311320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2311320 prefixEnd_2311320 := by exact prefixLift 2311320
  have htrace : WordTrace (prefixWord ++ tailWord_2311320) baseStart_2311320 baseEnd_2311320 := by
    simpa [prefixWord, tailWord_2311320, baseEnd_2311320] using wordTrace_append hprefix tailTrace_2311320
  have hstable : (prefixWord ++ tailWord_2311320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2311320).length < 2 ^ (prefixWord ++ tailWord_2311320).sum := by decide
  have hdescent : baseEnd_2311320 < baseStart_2311320 := by decide
  rcases family_descends (prefixWord ++ tailWord_2311320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2311333 : List Nat := [1, 3, 1, 2, 1, 4, 3, 2, 1, 5]
def baseStart_2311333 : Nat := 118140960795 + 2311333 * 2 ^ 59
def prefixEnd_2311333 : Nat := 4983230072969 + 3 ^ 40 * 2311333 * 2
def baseEnd_2311333 : Nat := 395608260532836877569293

theorem tailTrace_2311333 : CollatzResearch.WordTrace tailWord_2311333 prefixEnd_2311333 395608260532836877569293 := by
  unfold tailWord_2311333
  simp only [CollatzResearch.WordTrace]
  refine ⟨84301240135442760094314653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56200826756961840062876435 84301240135442760094314653)
  ·
    refine ⟨31612965050791035035367995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84301240135442760094314653 31612965050791035035367995)
    ·
      refine ⟨47419447576186552553051993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31612965050791035035367995 47419447576186552553051993)
      ·
        refine ⟨35564585682139914414788995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47419447576186552553051993 35564585682139914414788995)
        ·
          refine ⟨53346878523209871622183493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35564585682139914414788995 53346878523209871622183493)
          ·
            refine ⟨10002539723101850929159405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 53346878523209871622183493 10002539723101850929159405)
            ·
              refine ⟨3750952396163194098434777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10002539723101850929159405 3750952396163194098434777)
              ·
                refine ⟨2813214297122395573826083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3750952396163194098434777 2813214297122395573826083)
                ·
                  refine ⟨4219821445683593360739125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2813214297122395573826083 4219821445683593360739125)
                  ·
                    refine ⟨395608260532836877569293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4219821445683593360739125 395608260532836877569293)
                    ·
                      rfl

theorem cell23_2311333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 3, 2, 1, 5].length) (baseStart_2311333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2311333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2311333 prefixEnd_2311333 := by exact prefixLift 2311333
  have htrace : WordTrace (prefixWord ++ tailWord_2311333) baseStart_2311333 baseEnd_2311333 := by
    simpa [prefixWord, tailWord_2311333, baseEnd_2311333] using wordTrace_append hprefix tailTrace_2311333
  have hstable : (prefixWord ++ tailWord_2311333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2311333).length < 2 ^ (prefixWord ++ tailWord_2311333).sum := by decide
  have hdescent : baseEnd_2311333 < baseStart_2311333 := by decide
  rcases family_descends (prefixWord ++ tailWord_2311333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2311339 : List Nat := [1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 11]
def baseStart_2311339 : Nat := 118140960795 + 2311339 * 2 ^ 59
def prefixEnd_2311339 : Nat := 4983230072969 + 3 ^ 40 * 2311339 * 2
def baseEnd_2311339 : Nat := 1186827862482437609232851

theorem tailTrace_2311339 : CollatzResearch.WordTrace tailWord_2311339 prefixEnd_2311339 1186827862482437609232851 := by
  unfold tailWord_2311339
  simp only [CollatzResearch.WordTrace]
  refine ⟨84301458973421023119033071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56200972648947348746022047 84301458973421023119033071)
  ·
    refine ⟨126452188460131534678549607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84301458973421023119033071 126452188460131534678549607)
    ·
      refine ⟨189678282690197302017824411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126452188460131534678549607 189678282690197302017824411)
      ·
        refine ⟨284517424035295953026736617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 189678282690197302017824411 284517424035295953026736617)
        ·
          refine ⟨213388068026471964770052463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 284517424035295953026736617 213388068026471964770052463)
          ·
            refine ⟨320082102039707947155078695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 213388068026471964770052463 320082102039707947155078695)
            ·
              refine ⟨480123153059561920732618043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 320082102039707947155078695 480123153059561920732618043)
              ·
                refine ⟨720184729589342881098927065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 480123153059561920732618043 720184729589342881098927065)
                ·
                  refine ⟨540138547192007160824195299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 720184729589342881098927065 540138547192007160824195299)
                  ·
                    refine ⟨810207820788010741236292949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 540138547192007160824195299 810207820788010741236292949)
                    ·
                      refine ⟨1186827862482437609232851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 11 810207820788010741236292949 1186827862482437609232851)
                      ·
                        rfl

theorem cell23_2311339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 11].length) (baseStart_2311339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2311339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2311339 prefixEnd_2311339 := by exact prefixLift 2311339
  have htrace : WordTrace (prefixWord ++ tailWord_2311339) baseStart_2311339 baseEnd_2311339 := by
    simpa [prefixWord, tailWord_2311339, baseEnd_2311339] using wordTrace_append hprefix tailTrace_2311339
  have hstable : (prefixWord ++ tailWord_2311339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2311339).length < 2 ^ (prefixWord ++ tailWord_2311339).sum := by decide
  have hdescent : baseEnd_2311339 < baseStart_2311339 := by decide
  rcases family_descends (prefixWord ++ tailWord_2311339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2311346 : List Nat := [3, 2, 1, 1, 1, 4, 1, 1, 3, 6]
def baseStart_2311346 : Nat := 118140960795 + 2311346 * 2 ^ 59
def prefixEnd_2311346 : Nat := 4983230072969 + 3 ^ 40 * 2311346 * 2
def baseEnd_2311346 : Nat := 395610485615673027281773

theorem tailTrace_2311346 : CollatzResearch.WordTrace tailWord_2311346 prefixEnd_2311346 395610485615673027281773 := by
  unfold tailWord_2311346
  simp only [CollatzResearch.WordTrace]
  refine ⟨21075428571098915828634473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56201142856263775543025261 21075428571098915828634473)
  ·
    refine ⟨15806571428324186871475855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21075428571098915828634473 15806571428324186871475855)
    ·
      refine ⟨23709857142486280307213783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15806571428324186871475855 23709857142486280307213783)
      ·
        refine ⟨35564785713729420460820675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23709857142486280307213783 35564785713729420460820675)
        ·
          refine ⟨53347178570594130691231013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35564785713729420460820675 53347178570594130691231013)
          ·
            refine ⟨10002595981986399504605815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 53347178570594130691231013 10002595981986399504605815)
            ·
              refine ⟨15003893972979599256908723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10002595981986399504605815 15003893972979599256908723)
              ·
                refine ⟨22505840959469398885363085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15003893972979599256908723 22505840959469398885363085)
                ·
                  refine ⟨8439690359801024582011157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22505840959469398885363085 8439690359801024582011157)
                  ·
                    refine ⟨395610485615673027281773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8439690359801024582011157 395610485615673027281773)
                    ·
                      rfl

theorem cell23_2311346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 1, 3, 6].length) (baseStart_2311346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2311346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2311346 prefixEnd_2311346 := by exact prefixLift 2311346
  have htrace : WordTrace (prefixWord ++ tailWord_2311346) baseStart_2311346 baseEnd_2311346 := by
    simpa [prefixWord, tailWord_2311346, baseEnd_2311346] using wordTrace_append hprefix tailTrace_2311346
  have hstable : (prefixWord ++ tailWord_2311346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2311346).length < 2 ^ (prefixWord ++ tailWord_2311346).sum := by decide
  have hdescent : baseEnd_2311346 < baseStart_2311346 := by decide
  rcases family_descends (prefixWord ++ tailWord_2311346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2311364 : List Nat := [2, 3, 3, 1, 3, 1, 1, 4, 1, 1, 3]
def baseStart_2311364 : Nat := 118140960795 + 2311364 * 2 ^ 59
def prefixEnd_2311364 : Nat := 4983230072969 + 3 ^ 40 * 2311364 * 2
def baseEnd_2311364 : Nat := 1186840699498800011420237

theorem tailTrace_2311364 : CollatzResearch.WordTrace tailWord_2311364 prefixEnd_2311364 1186840699498800011420237 := by
  unfold tailWord_2311364
  simp only [CollatzResearch.WordTrace]
  refine ⟨42151185399165226194346573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56201580532220301592462097 42151185399165226194346573)
  ·
    refine ⟨15806694524686959822879965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42151185399165226194346573 15806694524686959822879965)
    ·
      refine ⟨5927510446757609933579987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15806694524686959822879965 5927510446757609933579987)
      ·
        refine ⟨8891265670136414900369981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5927510446757609933579987 8891265670136414900369981)
        ·
          refine ⟨3334224626301155587638743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8891265670136414900369981 3334224626301155587638743)
          ·
            refine ⟨5001336939451733381458115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3334224626301155587638743 5001336939451733381458115)
            ·
              refine ⟨7502005409177600072187173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5001336939451733381458115 7502005409177600072187173)
              ·
                refine ⟨1406626014220800013535095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7502005409177600072187173 1406626014220800013535095)
                ·
                  refine ⟨2109939021331200020302643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1406626014220800013535095 2109939021331200020302643)
                  ·
                    refine ⟨3164908531996800030453965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2109939021331200020302643 3164908531996800030453965)
                    ·
                      refine ⟨1186840699498800011420237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3164908531996800030453965 1186840699498800011420237)
                      ·
                        rfl

theorem cell23_2311364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 1, 4, 1, 1, 3].length) (baseStart_2311364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2311364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2311364 prefixEnd_2311364 := by exact prefixLift 2311364
  have htrace : WordTrace (prefixWord ++ tailWord_2311364) baseStart_2311364 baseEnd_2311364 := by
    simpa [prefixWord, tailWord_2311364, baseEnd_2311364] using wordTrace_append hprefix tailTrace_2311364
  have hstable : (prefixWord ++ tailWord_2311364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2311364).length < 2 ^ (prefixWord ++ tailWord_2311364).sum := by decide
  have hdescent : baseEnd_2311364 < baseStart_2311364 := by decide
  rcases family_descends (prefixWord ++ tailWord_2311364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2311393 : List Nat := [1, 2, 3, 1, 3, 3, 3, 7]
def baseStart_2311393 : Nat := 118140960795 + 2311393 * 2 ^ 59
def prefixEnd_2311393 : Nat := 4983230072969 + 3 ^ 40 * 2311393 * 2
def baseEnd_2311393 : Nat := 43957614460658533257689

theorem tailTrace_2311393 : CollatzResearch.WordTrace tailWord_2311393 prefixEnd_2311393 43957614460658533257689 := by
  unfold tailWord_2311393
  simp only [CollatzResearch.WordTrace]
  refine ⟨84303428515225390341498833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56202285676816926894332555 84303428515225390341498833)
  ·
    refine ⟨63227571386419042756124125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84303428515225390341498833 63227571386419042756124125)
    ·
      refine ⟨23710339269907141033546547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63227571386419042756124125 23710339269907141033546547)
      ·
        refine ⟨35565508904860711550319821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23710339269907141033546547 35565508904860711550319821)
        ·
          refine ⟨13337065839322766831369933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35565508904860711550319821 13337065839322766831369933)
          ·
            refine ⟨5001399689746037561763725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13337065839322766831369933 5001399689746037561763725)
            ·
              refine ⟨1875524883654764085661397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5001399689746037561763725 1875524883654764085661397)
              ·
                refine ⟨43957614460658533257689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1875524883654764085661397 43957614460658533257689)
                ·
                  rfl

theorem cell23_2311393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 3, 7].length) (baseStart_2311393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2311393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2311393 prefixEnd_2311393 := by exact prefixLift 2311393
  have htrace : WordTrace (prefixWord ++ tailWord_2311393) baseStart_2311393 baseEnd_2311393 := by
    simpa [prefixWord, tailWord_2311393, baseEnd_2311393] using wordTrace_append hprefix tailTrace_2311393
  have hstable : (prefixWord ++ tailWord_2311393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2311393).length < 2 ^ (prefixWord ++ tailWord_2311393).sum := by decide
  have hdescent : baseEnd_2311393 < baseStart_2311393 := by decide
  rcases family_descends (prefixWord ++ tailWord_2311393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2311403 : List Nat := [1, 1, 1, 1, 2, 6, 2, 2, 1, 3, 3]
def baseStart_2311403 : Nat := 118140960795 + 2311403 * 2 ^ 59
def prefixEnd_2311403 : Nat := 4983230072969 + 3 ^ 40 * 2311403 * 2
def baseEnd_2311403 : Nat := 1186860725244325358832557

theorem tailTrace_2311403 : CollatzResearch.WordTrace tailWord_2311403 prefixEnd_2311403 1186860725244325358832557 := by
  unfold tailWord_2311403
  simp only [CollatzResearch.WordTrace]
  refine ⟨84303793245189162049362863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56202528830126108032908575 84303793245189162049362863)
  ·
    refine ⟨126455689867783743074044295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84303793245189162049362863 126455689867783743074044295)
    ·
      refine ⟨189683534801675614611066443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126455689867783743074044295 189683534801675614611066443)
      ·
        refine ⟨284525302202513421916599665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 189683534801675614611066443 284525302202513421916599665)
        ·
          refine ⟨213393976651885066437449749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 284525302202513421916599665 213393976651885066437449749)
          ·
            refine ⟨10002842655557112489255457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 213393976651885066437449749 10002842655557112489255457)
            ·
              refine ⟨7502131991667834366941593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10002842655557112489255457 7502131991667834366941593)
              ·
                refine ⟨5626598993750875775206195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7502131991667834366941593 5626598993750875775206195)
                ·
                  refine ⟨8439898490626313662809293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5626598993750875775206195 8439898490626313662809293)
                  ·
                    refine ⟨3164961933984867623553485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8439898490626313662809293 3164961933984867623553485)
                    ·
                      refine ⟨1186860725244325358832557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3164961933984867623553485 1186860725244325358832557)
                      ·
                        rfl

theorem cell23_2311403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 2, 2, 1, 3, 3].length) (baseStart_2311403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2311403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2311403 prefixEnd_2311403 := by exact prefixLift 2311403
  have htrace : WordTrace (prefixWord ++ tailWord_2311403) baseStart_2311403 baseEnd_2311403 := by
    simpa [prefixWord, tailWord_2311403, baseEnd_2311403] using wordTrace_append hprefix tailTrace_2311403
  have hstable : (prefixWord ++ tailWord_2311403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2311403).length < 2 ^ (prefixWord ++ tailWord_2311403).sum := by decide
  have hdescent : baseEnd_2311403 < baseStart_2311403 := by decide
  rcases family_descends (prefixWord ++ tailWord_2311403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2311404 : List Nat := [2, 2, 1, 1, 2, 5, 2, 3, 1, 2, 2]
def baseStart_2311404 : Nat := 118140960795 + 2311404 * 2 ^ 59
def prefixEnd_2311404 : Nat := 4983230072969 + 3 ^ 40 * 2311404 * 2
def baseEnd_2311404 : Nat := 1186861238724979854920053

theorem tailTrace_2311404 : CollatzResearch.WordTrace tailWord_2311404 prefixEnd_2311404 1186861238724979854920053 := by
  unfold tailWord_2311404
  simp only [CollatzResearch.WordTrace]
  refine ⟨42151914859092769610074633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56202553145457026146766177 42151914859092769610074633)
  ·
    refine ⟨31613936144319577207555975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42151914859092769610074633 31613936144319577207555975)
    ·
      refine ⟨47420904216479365811333963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31613936144319577207555975 47420904216479365811333963)
      ·
        refine ⟨71131356324719048717000945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47420904216479365811333963 71131356324719048717000945)
        ·
          refine ⟨53348517243539286537750709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71131356324719048717000945 53348517243539286537750709)
          ·
            refine ⟨5001423491581808112914129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 53348517243539286537750709 5001423491581808112914129)
            ·
              refine ⟨3751067618686356084685597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5001423491581808112914129 3751067618686356084685597)
              ·
                refine ⟨1406650357007383531757099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3751067618686356084685597 1406650357007383531757099)
                ·
                  refine ⟨2109975535511075297635649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1406650357007383531757099 2109975535511075297635649)
                  ·
                    refine ⟨1582481651633306473226737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2109975535511075297635649 1582481651633306473226737)
                    ·
                      refine ⟨1186861238724979854920053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1582481651633306473226737 1186861238724979854920053)
                      ·
                        rfl

theorem cell23_2311404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 2, 3, 1, 2, 2].length) (baseStart_2311404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2311404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2311404 prefixEnd_2311404 := by exact prefixLift 2311404
  have htrace : WordTrace (prefixWord ++ tailWord_2311404) baseStart_2311404 baseEnd_2311404 := by
    simpa [prefixWord, tailWord_2311404, baseEnd_2311404] using wordTrace_append hprefix tailTrace_2311404
  have hstable : (prefixWord ++ tailWord_2311404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2311404).length < 2 ^ (prefixWord ++ tailWord_2311404).sum := by decide
  have hdescent : baseEnd_2311404 < baseStart_2311404 := by decide
  rcases family_descends (prefixWord ++ tailWord_2311404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2311447 : List Nat := [1, 1, 3, 4, 1, 1, 4, 2, 1, 3, 2]
def baseStart_2311447 : Nat := 118140960795 + 2311447 * 2 ^ 59
def prefixEnd_2311447 : Nat := 4983230072969 + 3 ^ 40 * 2311447 * 2
def baseEnd_2311447 : Nat := 1186883318393123186682355

theorem tailTrace_2311447 : CollatzResearch.WordTrace tailWord_2311447 prefixEnd_2311447 1186883318393123186682355 := by
  unfold tailWord_2311447
  simp only [CollatzResearch.WordTrace]
  refine ⟨84305398057029757563964595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56203598704686505042643063 84305398057029757563964595)
  ·
    refine ⟨126458097085544636345946893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84305398057029757563964595 126458097085544636345946893)
    ·
      refine ⟨47421786407079238629730085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 126458097085544636345946893 47421786407079238629730085)
      ·
        refine ⟨8891584951327357243074391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47421786407079238629730085 8891584951327357243074391)
        ·
          refine ⟨13337377426991035864611587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8891584951327357243074391 13337377426991035864611587)
          ·
            refine ⟨20006066140486553796917381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13337377426991035864611587 20006066140486553796917381)
            ·
              refine ⟨3751137401341228836922009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20006066140486553796917381 3751137401341228836922009)
              ·
                refine ⟨2813353051005921627691507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3751137401341228836922009 2813353051005921627691507)
                ·
                  refine ⟨4220029576508882441537261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2813353051005921627691507 4220029576508882441537261)
                  ·
                    refine ⟨1582511091190830915576473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4220029576508882441537261 1582511091190830915576473)
                    ·
                      refine ⟨1186883318393123186682355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1582511091190830915576473 1186883318393123186682355)
                      ·
                        rfl

theorem cell23_2311447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 4, 2, 1, 3, 2].length) (baseStart_2311447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2311447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2311447 prefixEnd_2311447 := by exact prefixLift 2311447
  have htrace : WordTrace (prefixWord ++ tailWord_2311447) baseStart_2311447 baseEnd_2311447 := by
    simpa [prefixWord, tailWord_2311447, baseEnd_2311447] using wordTrace_append hprefix tailTrace_2311447
  have hstable : (prefixWord ++ tailWord_2311447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2311447).length < 2 ^ (prefixWord ++ tailWord_2311447).sum := by decide
  have hdescent : baseEnd_2311447 < baseStart_2311447 := by decide
  rcases family_descends (prefixWord ++ tailWord_2311447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2311460 : List Nat := [2, 3, 1, 3, 1, 1, 2, 1, 3, 4, 2]
def baseStart_2311460 : Nat := 118140960795 + 2311460 * 2 ^ 59
def prefixEnd_2311460 : Nat := 4983230072969 + 3 ^ 40 * 2311460 * 2
def baseEnd_2311460 : Nat := 1186889993641631635819795

theorem tailTrace_2311460 : CollatzResearch.WordTrace tailWord_2311460 prefixEnd_2311460 1186889993641631635819795 := by
  unfold tailWord_2311460
  simp only [CollatzResearch.WordTrace]
  refine ⟨42152936102991330392093917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56203914803988440522791889 42152936102991330392093917)
  ·
    refine ⟨15807351038621748897035219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42152936102991330392093917 15807351038621748897035219)
    ·
      refine ⟨23711026557932623345552829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15807351038621748897035219 23711026557932623345552829)
      ·
        refine ⟨8891634959224733754582311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23711026557932623345552829 8891634959224733754582311)
        ·
          refine ⟨13337452438837100631873467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8891634959224733754582311 13337452438837100631873467)
          ·
            refine ⟨20006178658255650947810201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13337452438837100631873467 20006178658255650947810201)
            ·
              refine ⟨15004633993691738210857651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20006178658255650947810201 15004633993691738210857651)
              ·
                refine ⟨22506950990537607316286477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15004633993691738210857651 22506950990537607316286477)
                ·
                  refine ⟨8440106621451602743607429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22506950990537607316286477 8440106621451602743607429)
                  ·
                    refine ⟨1582519991522175514426393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8440106621451602743607429 1582519991522175514426393)
                    ·
                      refine ⟨1186889993641631635819795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1582519991522175514426393 1186889993641631635819795)
                      ·
                        rfl

theorem cell23_2311460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 1, 3, 4, 2].length) (baseStart_2311460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2311460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2311460 prefixEnd_2311460 := by exact prefixLift 2311460
  have htrace : WordTrace (prefixWord ++ tailWord_2311460) baseStart_2311460 baseEnd_2311460 := by
    simpa [prefixWord, tailWord_2311460, baseEnd_2311460] using wordTrace_append hprefix tailTrace_2311460
  have hstable : (prefixWord ++ tailWord_2311460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2311460).length < 2 ^ (prefixWord ++ tailWord_2311460).sum := by decide
  have hdescent : baseEnd_2311460 < baseStart_2311460 := by decide
  rcases family_descends (prefixWord ++ tailWord_2311460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2311477 : List Nat := [1, 3, 3, 1, 2, 2, 2, 1, 4, 2, 2]
def baseStart_2311477 : Nat := 118140960795 + 2311477 * 2 ^ 59
def prefixEnd_2311477 : Nat := 4983230072969 + 3 ^ 40 * 2311477 * 2
def baseEnd_2311477 : Nat := 1186898722812758069307217

theorem tailTrace_2311477 : CollatzResearch.WordTrace tailWord_2311477 prefixEnd_2311477 1186898722812758069307217 := by
  unfold tailWord_2311477
  simp only [CollatzResearch.WordTrace]
  refine ⟨84306492246921072687556685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56204328164614048458371123 84306492246921072687556685)
  ·
    refine ⟨31614934592595402257833757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84306492246921072687556685 31614934592595402257833757)
    ·
      refine ⟨11855600472223275846687659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31614934592595402257833757 11855600472223275846687659)
      ·
        refine ⟨17783400708334913770031489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11855600472223275846687659 17783400708334913770031489)
        ·
          refine ⟨13337550531251185327523617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17783400708334913770031489 13337550531251185327523617)
          ·
            refine ⟨10003162898438388995642713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13337550531251185327523617 10003162898438388995642713)
            ·
              refine ⟨7502372173828791746732035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10003162898438388995642713 7502372173828791746732035)
              ·
                refine ⟨11253558260743187620098053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7502372173828791746732035 11253558260743187620098053)
                ·
                  refine ⟨2110042173889347678768385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11253558260743187620098053 2110042173889347678768385)
                  ·
                    refine ⟨1582531630417010759076289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2110042173889347678768385 1582531630417010759076289)
                    ·
                      refine ⟨1186898722812758069307217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1582531630417010759076289 1186898722812758069307217)
                      ·
                        rfl

theorem cell23_2311477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 2, 1, 4, 2, 2].length) (baseStart_2311477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2311477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2311477 prefixEnd_2311477 := by exact prefixLift 2311477
  have htrace : WordTrace (prefixWord ++ tailWord_2311477) baseStart_2311477 baseEnd_2311477 := by
    simpa [prefixWord, tailWord_2311477, baseEnd_2311477] using wordTrace_append hprefix tailTrace_2311477
  have hstable : (prefixWord ++ tailWord_2311477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2311477).length < 2 ^ (prefixWord ++ tailWord_2311477).sum := by decide
  have hdescent : baseEnd_2311477 < baseStart_2311477 := by decide
  rcases family_descends (prefixWord ++ tailWord_2311477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2311493 : List Nat := [1, 3, 1, 1, 1, 2, 1, 5, 2, 3, 3]
def baseStart_2311493 : Nat := 118140960795 + 2311493 * 2 ^ 59
def prefixEnd_2311493 : Nat := 4983230072969 + 3 ^ 40 * 2311493 * 2
def baseEnd_2311493 : Nat := 1186906938503230006707143

theorem tailTrace_2311493 : CollatzResearch.WordTrace tailWord_2311493 prefixEnd_2311493 1186906938503230006707143 := by
  unfold tailWord_2311493
  simp only [CollatzResearch.WordTrace]
  refine ⟨84307075814863107420139133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56204717209908738280092755 84307075814863107420139133)
  ·
    refine ⟨31615153430573665282552175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84307075814863107420139133 31615153430573665282552175)
    ·
      refine ⟨47422730145860497923828263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31615153430573665282552175 47422730145860497923828263)
      ·
        refine ⟨71134095218790746885742395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47422730145860497923828263 71134095218790746885742395)
        ·
          refine ⟨106701142828186120328613593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71134095218790746885742395 106701142828186120328613593)
          ·
            refine ⟨80025857121139590246460195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 106701142828186120328613593 80025857121139590246460195)
            ·
              refine ⟨120038785681709385369690293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80025857121139590246460195 120038785681709385369690293)
              ·
                refine ⟨11253636157660254878408465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 120038785681709385369690293 11253636157660254878408465)
                ·
                  refine ⟨8440227118245191158806349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11253636157660254878408465 8440227118245191158806349)
                  ·
                    refine ⟨3165085169341946684552381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8440227118245191158806349 3165085169341946684552381)
                    ·
                      refine ⟨1186906938503230006707143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3165085169341946684552381 1186906938503230006707143)
                      ·
                        rfl

theorem cell23_2311493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 5, 2, 3, 3].length) (baseStart_2311493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2311493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2311493 prefixEnd_2311493 := by exact prefixLift 2311493
  have htrace : WordTrace (prefixWord ++ tailWord_2311493) baseStart_2311493 baseEnd_2311493 := by
    simpa [prefixWord, tailWord_2311493, baseEnd_2311493] using wordTrace_append hprefix tailTrace_2311493
  have hstable : (prefixWord ++ tailWord_2311493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2311493).length < 2 ^ (prefixWord ++ tailWord_2311493).sum := by decide
  have hdescent : baseEnd_2311493 < baseStart_2311493 := by decide
  rcases family_descends (prefixWord ++ tailWord_2311493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2311513 : List Nat := [1, 2, 1, 2, 2, 2, 3, 3, 2, 5]
def baseStart_2311513 : Nat := 118140960795 + 2311513 * 2 ^ 59
def prefixEnd_2311513 : Nat := 4983230072969 + 3 ^ 40 * 2311513 * 2
def baseEnd_2311513 : Nat := 395639069372106642819017

theorem tailTrace_2311513 : CollatzResearch.WordTrace tailWord_2311513 prefixEnd_2311513 395639069372106642819017 := by
  unfold tailWord_2311513
  simp only [CollatzResearch.WordTrace]
  refine ⟨84307805274790650835867193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56205203516527100557244795 84307805274790650835867193)
  ·
    refine ⟨63230853956092988126900395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84307805274790650835867193 63230853956092988126900395)
    ·
      refine ⟨94846280934139482190350593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63230853956092988126900395 94846280934139482190350593)
      ·
        refine ⟨71134710700604611642762945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94846280934139482190350593 71134710700604611642762945)
        ·
          refine ⟨53351033025453458732072209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71134710700604611642762945 53351033025453458732072209)
          ·
            refine ⟨40013274769090094049054157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53351033025453458732072209 40013274769090094049054157)
            ·
              refine ⟨15004978038408785268395309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40013274769090094049054157 15004978038408785268395309)
              ·
                refine ⟨5626866764403294475648241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15004978038408785268395309 5626866764403294475648241)
                ·
                  refine ⟨4220150073302470856736181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5626866764403294475648241 4220150073302470856736181)
                  ·
                    refine ⟨395639069372106642819017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4220150073302470856736181 395639069372106642819017)
                    ·
                      rfl

theorem cell23_2311513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 3, 2, 5].length) (baseStart_2311513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2311513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2311513 prefixEnd_2311513 := by exact prefixLift 2311513
  have htrace : WordTrace (prefixWord ++ tailWord_2311513) baseStart_2311513 baseEnd_2311513 := by
    simpa [prefixWord, tailWord_2311513, baseEnd_2311513] using wordTrace_append hprefix tailTrace_2311513
  have hstable : (prefixWord ++ tailWord_2311513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2311513).length < 2 ^ (prefixWord ++ tailWord_2311513).sum := by decide
  have hdescent : baseEnd_2311513 < baseStart_2311513 := by decide
  rcases family_descends (prefixWord ++ tailWord_2311513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2311523 : List Nat := [1, 1, 1, 5, 2, 2, 1, 2, 1, 2, 5]
def baseStart_2311523 : Nat := 118140960795 + 2311523 * 2 ^ 59
def prefixEnd_2311523 : Nat := 4983230072969 + 3 ^ 40 * 2311523 * 2
def baseEnd_2311523 : Nat := 1186922342922864889332005

theorem tailTrace_2311523 : CollatzResearch.WordTrace tailWord_2311523 prefixEnd_2311523 1186922342922864889332005 := by
  unfold tailWord_2311523
  simp only [CollatzResearch.WordTrace]
  refine ⟨84308170004754422543731223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56205446669836281695820815 84308170004754422543731223)
  ·
    refine ⟨126462255007131633815596835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84308170004754422543731223 126462255007131633815596835)
    ·
      refine ⟨189693382510697450723395253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126462255007131633815596835 189693382510697450723395253)
      ·
        refine ⟨17783754610377886005318305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 189693382510697450723395253 17783754610377886005318305)
        ·
          refine ⟨13337815957783414503988729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17783754610377886005318305 13337815957783414503988729)
          ·
            refine ⟨10003361968337560877991547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13337815957783414503988729 10003361968337560877991547)
            ·
              refine ⟨15005042952506341316987321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10003361968337560877991547 15005042952506341316987321)
              ·
                refine ⟨11253782214379755987740491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15005042952506341316987321 11253782214379755987740491)
                ·
                  refine ⟨16880673321569633981610737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11253782214379755987740491 16880673321569633981610737)
                  ·
                    refine ⟨12660504991177225486208053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16880673321569633981610737 12660504991177225486208053)
                    ·
                      refine ⟨1186922342922864889332005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12660504991177225486208053 1186922342922864889332005)
                      ·
                        rfl

theorem cell23_2311523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 2, 1, 2, 5].length) (baseStart_2311523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2311523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2311523 prefixEnd_2311523 := by exact prefixLift 2311523
  have htrace : WordTrace (prefixWord ++ tailWord_2311523) baseStart_2311523 baseEnd_2311523 := by
    simpa [prefixWord, tailWord_2311523, baseEnd_2311523] using wordTrace_append hprefix tailTrace_2311523
  have hstable : (prefixWord ++ tailWord_2311523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2311523).length < 2 ^ (prefixWord ++ tailWord_2311523).sum := by decide
  have hdescent : baseEnd_2311523 < baseStart_2311523 := by decide
  rcases family_descends (prefixWord ++ tailWord_2311523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2311534 : List Nat := [4, 1, 2, 4, 1, 1, 1, 4, 5]
def baseStart_2311534 : Nat := 118140960795 + 2311534 * 2 ^ 59
def prefixEnd_2311534 : Nat := 4983230072969 + 3 ^ 40 * 2311534 * 2
def baseEnd_2311534 : Nat := 131880887912229371810495

theorem tailTrace_2311534 : CollatzResearch.WordTrace tailWord_2311534 prefixEnd_2311534 131880887912229371810495 := by
  unfold tailWord_2311534
  simp only [CollatzResearch.WordTrace]
  refine ⟨10538571400964321427797707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56205714138476380948254437 10538571400964321427797707)
  ·
    refine ⟨15807857101446482141696561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10538571400964321427797707 15807857101446482141696561)
    ·
      refine ⟨11855892826084861606272421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15807857101446482141696561 11855892826084861606272421)
      ·
        refine ⟨2222979904890911551176079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11855892826084861606272421 2222979904890911551176079)
        ·
          refine ⟨3334469857336367326764119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2222979904890911551176079 3334469857336367326764119)
          ·
            refine ⟨5001704786004550990146179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3334469857336367326764119 5001704786004550990146179)
            ·
              refine ⟨7502557179006826485219269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5001704786004550990146179 7502557179006826485219269)
              ·
                refine ⟨1406729471063779965978613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7502557179006826485219269 1406729471063779965978613)
                ·
                  refine ⟨131880887912229371810495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1406729471063779965978613 131880887912229371810495)
                  ·
                    rfl

theorem cell23_2311534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 1, 4, 5].length) (baseStart_2311534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2311534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2311534 prefixEnd_2311534 := by exact prefixLift 2311534
  have htrace : WordTrace (prefixWord ++ tailWord_2311534) baseStart_2311534 baseEnd_2311534 := by
    simpa [prefixWord, tailWord_2311534, baseEnd_2311534] using wordTrace_append hprefix tailTrace_2311534
  have hstable : (prefixWord ++ tailWord_2311534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2311534).length < 2 ^ (prefixWord ++ tailWord_2311534).sum := by decide
  have hdescent : baseEnd_2311534 < baseStart_2311534 := by decide
  rcases family_descends (prefixWord ++ tailWord_2311534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2311560 : List Nat := [2, 1, 3, 3, 1, 2, 1, 1, 5, 4]
def baseStart_2311560 : Nat := 118140960795 + 2311560 * 2 ^ 59
def prefixEnd_2311560 : Nat := 4983230072969 + 3 ^ 40 * 2311560 * 2
def baseEnd_2311560 : Nat := 395647113902360414856445

theorem tailTrace_2311560 : CollatzResearch.WordTrace tailWord_2311560 prefixEnd_2311560 395647113902360414856445 := by
  unfold tailWord_2311560
  simp only [CollatzResearch.WordTrace]
  refine ⟨42154759752810188931414067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56206346337080251908552089 42154759752810188931414067)
  ·
    refine ⟨63232139629215283397121101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42154759752810188931414067 63232139629215283397121101)
    ·
      refine ⟨23712052360955731273920413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63232139629215283397121101 23712052360955731273920413)
      ·
        refine ⟨8892019635358399227720155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23712052360955731273920413 8892019635358399227720155)
        ·
          refine ⟨13338029453037598841580233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8892019635358399227720155 13338029453037598841580233)
          ·
            refine ⟨10003522089778199131185175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13338029453037598841580233 10003522089778199131185175)
            ·
              refine ⟨15005283134667298696777763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10003522089778199131185175 15005283134667298696777763)
              ·
                refine ⟨22507924702000948045166645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15005283134667298696777763 22507924702000948045166645)
                ·
                  refine ⟨2110117940812588879234373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 22507924702000948045166645 2110117940812588879234373)
                  ·
                    refine ⟨395647113902360414856445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2110117940812588879234373 395647113902360414856445)
                    ·
                      rfl

theorem cell23_2311560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 1, 5, 4].length) (baseStart_2311560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2311560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2311560 prefixEnd_2311560 := by exact prefixLift 2311560
  have htrace : WordTrace (prefixWord ++ tailWord_2311560) baseStart_2311560 baseEnd_2311560 := by
    simpa [prefixWord, tailWord_2311560, baseEnd_2311560] using wordTrace_append hprefix tailTrace_2311560
  have hstable : (prefixWord ++ tailWord_2311560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2311560).length < 2 ^ (prefixWord ++ tailWord_2311560).sum := by decide
  have hdescent : baseEnd_2311560 < baseStart_2311560 := by decide
  rcases family_descends (prefixWord ++ tailWord_2311560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2311577 : List Nat := [1, 2, 1, 2, 1, 5, 1, 5, 1, 4]
def baseStart_2311577 : Nat := 118140960795 + 2311577 * 2 ^ 59
def prefixEnd_2311577 : Nat := 4983230072969 + 3 ^ 40 * 2311577 * 2
def baseEnd_2311577 : Nat := 395650023626069226018919

theorem tailTrace_2311577 : CollatzResearch.WordTrace tailWord_2311577 prefixEnd_2311577 395650023626069226018919 := by
  unfold tailWord_2311577
  simp only [CollatzResearch.WordTrace]
  refine ⟨84310139546558789766196985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56206759697705859844131323 84310139546558789766196985)
  ·
    refine ⟨63232604659919092324647739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84310139546558789766196985 63232604659919092324647739)
    ·
      refine ⟨94848906989878638486971609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63232604659919092324647739 94848906989878638486971609)
      ·
        refine ⟨71136680242408978865228707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94848906989878638486971609 71136680242408978865228707)
        ·
          refine ⟨106705020363613468297843061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71136680242408978865228707 106705020363613468297843061)
          ·
            refine ⟨10003595659088762652922787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 106705020363613468297843061 10003595659088762652922787)
            ·
              refine ⟨15005393488633143979384181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10003595659088762652922787 15005393488633143979384181)
              ·
                refine ⟨1406755639559357248067267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15005393488633143979384181 1406755639559357248067267)
                ·
                  refine ⟨2110133459339035872100901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1406755639559357248067267 2110133459339035872100901)
                  ·
                    refine ⟨395650023626069226018919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2110133459339035872100901 395650023626069226018919)
                    ·
                      rfl

theorem cell23_2311577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 5, 1, 4].length) (baseStart_2311577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2311577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2311577 prefixEnd_2311577 := by exact prefixLift 2311577
  have htrace : WordTrace (prefixWord ++ tailWord_2311577) baseStart_2311577 baseEnd_2311577 := by
    simpa [prefixWord, tailWord_2311577, baseEnd_2311577] using wordTrace_append hprefix tailTrace_2311577
  have hstable : (prefixWord ++ tailWord_2311577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2311577).length < 2 ^ (prefixWord ++ tailWord_2311577).sum := by decide
  have hdescent : baseEnd_2311577 < baseStart_2311577 := by decide
  rcases family_descends (prefixWord ++ tailWord_2311577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2311603 : List Nat := [1, 1, 1, 2, 3, 1, 1, 3, 5, 5]
def baseStart_2311603 : Nat := 118140960795 + 2311603 * 2 ^ 59
def prefixEnd_2311603 : Nat := 4983230072969 + 3 ^ 40 * 2311603 * 2
def baseEnd_2311603 : Nat := 395654473791741525443879

theorem tailTrace_2311603 : CollatzResearch.WordTrace tailWord_2311603 prefixEnd_2311603 395654473791741525443879 := by
  unfold tailWord_2311603
  simp only [CollatzResearch.WordTrace]
  refine ⟨84311087844464596206643463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56207391896309730804428975 84311087844464596206643463)
  ·
    refine ⟨126466631766696894309965195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84311087844464596206643463 126466631766696894309965195)
    ·
      refine ⟨189699947650045341464947793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126466631766696894309965195 189699947650045341464947793)
      ·
        refine ⟨142274960737534006098710845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 189699947650045341464947793 142274960737534006098710845)
        ·
          refine ⟨53353110276575252287016567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 142274960737534006098710845 53353110276575252287016567)
          ·
            refine ⟨80029665414862878430524851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53353110276575252287016567 80029665414862878430524851)
            ·
              refine ⟨120044498122294317645787277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80029665414862878430524851 120044498122294317645787277)
              ·
                refine ⟨45016686795860369117170229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 120044498122294317645787277 45016686795860369117170229)
                ·
                  refine ⟨4220314387111909604734709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 45016686795860369117170229 4220314387111909604734709)
                  ·
                    refine ⟨395654473791741525443879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4220314387111909604734709 395654473791741525443879)
                    ·
                      rfl

theorem cell23_2311603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 3, 5, 5].length) (baseStart_2311603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2311603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2311603 prefixEnd_2311603 := by exact prefixLift 2311603
  have htrace : WordTrace (prefixWord ++ tailWord_2311603) baseStart_2311603 baseEnd_2311603 := by
    simpa [prefixWord, tailWord_2311603, baseEnd_2311603] using wordTrace_append hprefix tailTrace_2311603
  have hstable : (prefixWord ++ tailWord_2311603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2311603).length < 2 ^ (prefixWord ++ tailWord_2311603).sum := by decide
  have hdescent : baseEnd_2311603 < baseStart_2311603 := by decide
  rcases family_descends (prefixWord ++ tailWord_2311603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2311663 : List Nat := [1, 1, 2, 1, 4, 1, 3, 10]
def baseStart_2311663 : Nat := 118140960795 + 2311663 * 2 ^ 59
def prefixEnd_2311663 : Nat := 4983230072969 + 3 ^ 40 * 2311663 * 2
def baseEnd_2311663 : Nat := 43962749267203494132643

theorem tailTrace_2311663 : CollatzResearch.WordTrace tailWord_2311663 prefixEnd_2311663 43962749267203494132643 := by
  unfold tailWord_2311663
  simp only [CollatzResearch.WordTrace]
  refine ⟨84313276224247226453827643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56208850816164817635885095 84313276224247226453827643)
  ·
    refine ⟨126469914336370839680741465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84313276224247226453827643 126469914336370839680741465)
    ·
      refine ⟨94852435752278129760556099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126469914336370839680741465 94852435752278129760556099)
      ·
        refine ⟨142278653628417194640834149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94852435752278129760556099 142278653628417194640834149)
        ·
          refine ⟨26677247555328223995156403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 142278653628417194640834149 26677247555328223995156403)
          ·
            refine ⟨40015871332992335992734605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26677247555328223995156403 40015871332992335992734605)
            ·
              refine ⟨15005951749872125997275477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40015871332992335992734605 15005951749872125997275477)
              ·
                refine ⟨43962749267203494132643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 15005951749872125997275477 43962749267203494132643)
                ·
                  rfl

theorem cell23_2311663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 10].length) (baseStart_2311663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2311663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2311663 prefixEnd_2311663 := by exact prefixLift 2311663
  have htrace : WordTrace (prefixWord ++ tailWord_2311663) baseStart_2311663 baseEnd_2311663 := by
    simpa [prefixWord, tailWord_2311663, baseEnd_2311663] using wordTrace_append hprefix tailTrace_2311663
  have hstable : (prefixWord ++ tailWord_2311663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2311663).length < 2 ^ (prefixWord ++ tailWord_2311663).sum := by decide
  have hdescent : baseEnd_2311663 < baseStart_2311663 := by decide
  rcases family_descends (prefixWord ++ tailWord_2311663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2311677 : List Nat := [1, 4, 1, 1, 1, 5, 1, 1, 3, 2, 3]
def baseStart_2311677 : Nat := 118140960795 + 2311677 * 2 ^ 59
def prefixEnd_2311677 : Nat := 4983230072969 + 3 ^ 40 * 2311677 * 2
def baseEnd_2311677 : Nat := 1187001418943657286806297

theorem tailTrace_2311677 : CollatzResearch.WordTrace tailWord_2311677 prefixEnd_2311677 1187001418943657286806297 := by
  unfold tailWord_2311677
  simp only [CollatzResearch.WordTrace]
  refine ⟨84313786846196506844837285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56209191230797671229891523 84313786846196506844837285)
  ·
    refine ⟨15808835033661845033406991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 84313786846196506844837285 15808835033661845033406991)
    ·
      refine ⟨23713252550492767550110487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15808835033661845033406991 23713252550492767550110487)
      ·
        refine ⟨35569878825739151325165731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23713252550492767550110487 35569878825739151325165731)
        ·
          refine ⟨53354818238608726987748597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35569878825739151325165731 53354818238608726987748597)
          ·
            refine ⟨5002014209869568155101431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 53354818238608726987748597 5002014209869568155101431)
            ·
              refine ⟨7503021314804352232652147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5002014209869568155101431 7503021314804352232652147)
              ·
                refine ⟨11254531972206528348978221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7503021314804352232652147 11254531972206528348978221)
                ·
                  refine ⟨4220449489577448130866833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11254531972206528348978221 4220449489577448130866833)
                  ·
                    refine ⟨3165337117183086098150125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4220449489577448130866833 3165337117183086098150125)
                    ·
                      refine ⟨1187001418943657286806297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3165337117183086098150125 1187001418943657286806297)
                      ·
                        rfl

theorem cell23_2311677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 1, 1, 3, 2, 3].length) (baseStart_2311677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2311677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2311677 prefixEnd_2311677 := by exact prefixLift 2311677
  have htrace : WordTrace (prefixWord ++ tailWord_2311677) baseStart_2311677 baseEnd_2311677 := by
    simpa [prefixWord, tailWord_2311677, baseEnd_2311677] using wordTrace_append hprefix tailTrace_2311677
  have hstable : (prefixWord ++ tailWord_2311677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2311677).length < 2 ^ (prefixWord ++ tailWord_2311677).sum := by decide
  have hdescent : baseEnd_2311677 < baseStart_2311677 := by decide
  rcases family_descends (prefixWord ++ tailWord_2311677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2311678 : List Nat := [4, 2, 2, 3, 1, 1, 2, 1, 2, 3, 2]
def baseStart_2311678 : Nat := 118140960795 + 2311678 * 2 ^ 59
def prefixEnd_2311678 : Nat := 4983230072969 + 3 ^ 40 * 2311678 * 2
def baseEnd_2311678 : Nat := 1187001932424311782893793

theorem tailTrace_2311678 : CollatzResearch.WordTrace tailWord_2311678 prefixEnd_2311678 1187001932424311782893793 := by
  unfold tailWord_2311678
  simp only [CollatzResearch.WordTrace]
  refine ⟨10539227914899110501952961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56209215546128589343749125 10539227914899110501952961)
  ·
    refine ⟨7904420936174332876464721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10539227914899110501952961 7904420936174332876464721)
    ·
      refine ⟨5928315702130749657348541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7904420936174332876464721 5928315702130749657348541)
      ·
        refine ⟨2223118388299031121505703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5928315702130749657348541 2223118388299031121505703)
        ·
          refine ⟨3334677582448546682258555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2223118388299031121505703 3334677582448546682258555)
          ·
            refine ⟨5002016373672820023387833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3334677582448546682258555 5002016373672820023387833)
            ·
              refine ⟨3751512280254615017540875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5002016373672820023387833 3751512280254615017540875)
              ·
                refine ⟨5627268420381922526311313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3751512280254615017540875 5627268420381922526311313)
                ·
                  refine ⟨4220451315286441894733485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5627268420381922526311313 4220451315286441894733485)
                  ·
                    refine ⟨1582669243232415710525057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4220451315286441894733485 1582669243232415710525057)
                    ·
                      refine ⟨1187001932424311782893793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1582669243232415710525057 1187001932424311782893793)
                      ·
                        rfl

theorem cell23_2311678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 2, 1, 2, 3, 2].length) (baseStart_2311678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2311678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2311678 prefixEnd_2311678 := by exact prefixLift 2311678
  have htrace : WordTrace (prefixWord ++ tailWord_2311678) baseStart_2311678 baseEnd_2311678 := by
    simpa [prefixWord, tailWord_2311678, baseEnd_2311678] using wordTrace_append hprefix tailTrace_2311678
  have hstable : (prefixWord ++ tailWord_2311678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2311678).length < 2 ^ (prefixWord ++ tailWord_2311678).sum := by decide
  have hdescent : baseEnd_2311678 < baseStart_2311678 := by decide
  rcases family_descends (prefixWord ++ tailWord_2311678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2311687 : List Nat := [1, 1, 4, 3, 2, 2, 1, 2, 1, 2, 4]
def baseStart_2311687 : Nat := 118140960795 + 2311687 * 2 ^ 59
def prefixEnd_2311687 : Nat := 4983230072969 + 3 ^ 40 * 2311687 * 2
def baseEnd_2311687 : Nat := 1187006553750202247681251

theorem tailTrace_2311687 : CollatzResearch.WordTrace tailWord_2311687 prefixEnd_2311687 1187006553750202247681251 := by
  unfold tailWord_2311687
  simp only [CollatzResearch.WordTrace]
  refine ⟨84314151576160278552701315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56209434384106852368467543 84314151576160278552701315)
  ·
    refine ⟨126471227364240417829051973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84314151576160278552701315 126471227364240417829051973)
    ·
      refine ⟨23713355130795078342947245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 126471227364240417829051973 23713355130795078342947245)
      ·
        refine ⟨8892508174048154378605217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23713355130795078342947245 8892508174048154378605217)
        ·
          refine ⟨6669381130536115783953913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8892508174048154378605217 6669381130536115783953913)
          ·
            refine ⟨5002035847902086837965435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6669381130536115783953913 5002035847902086837965435)
            ·
              refine ⟨7503053771853130256948153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5002035847902086837965435 7503053771853130256948153)
              ·
                refine ⟨5627290328889847692711115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7503053771853130256948153 5627290328889847692711115)
                ·
                  refine ⟨8440935493334771539066673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5627290328889847692711115 8440935493334771539066673)
                  ·
                    refine ⟨6330701620001078654300005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8440935493334771539066673 6330701620001078654300005)
                    ·
                      refine ⟨1187006553750202247681251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6330701620001078654300005 1187006553750202247681251)
                      ·
                        rfl

theorem cell23_2311687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 1, 2, 1, 2, 4].length) (baseStart_2311687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2311687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2311687 prefixEnd_2311687 := by exact prefixLift 2311687
  have htrace : WordTrace (prefixWord ++ tailWord_2311687) baseStart_2311687 baseEnd_2311687 := by
    simpa [prefixWord, tailWord_2311687, baseEnd_2311687] using wordTrace_append hprefix tailTrace_2311687
  have hstable : (prefixWord ++ tailWord_2311687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2311687).length < 2 ^ (prefixWord ++ tailWord_2311687).sum := by decide
  have hdescent : baseEnd_2311687 < baseStart_2311687 := by decide
  rcases family_descends (prefixWord ++ tailWord_2311687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2311694 : List Nat := [4, 1, 1, 2, 4, 2, 1, 1, 1, 1, 5]
def baseStart_2311694 : Nat := 118140960795 + 2311694 * 2 ^ 59
def prefixEnd_2311694 : Nat := 4983230072969 + 3 ^ 40 * 2311694 * 2
def baseEnd_2311694 : Nat := 1187010148114783720293719

theorem tailTrace_2311694 : CollatzResearch.WordTrace tailWord_2311694 prefixEnd_2311694 1187010148114783720293719 := by
  unfold tailWord_2311694
  simp only [CollatzResearch.WordTrace]
  refine ⟨10539300860891864843525767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56209604591423279165470757 10539300860891864843525767)
  ·
    refine ⟨15808951291337797265288651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10539300860891864843525767 15808951291337797265288651)
    ·
      refine ⟨23713426937006695897932977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15808951291337797265288651 23713426937006695897932977)
      ·
        refine ⟨17785070202755021923449733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23713426937006695897932977 17785070202755021923449733)
        ·
          refine ⟨3334700663016566610646825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17785070202755021923449733 3334700663016566610646825)
          ·
            refine ⟨2501025497262424957985119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3334700663016566610646825 2501025497262424957985119)
            ·
              refine ⟨3751538245893637436977679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2501025497262424957985119 3751538245893637436977679)
              ·
                refine ⟨5627307368840456155466519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3751538245893637436977679 5627307368840456155466519)
                ·
                  refine ⟨8440961053260684233199779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5627307368840456155466519 8440961053260684233199779)
                  ·
                    refine ⟨12661441579891026349799669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8440961053260684233199779 12661441579891026349799669)
                    ·
                      refine ⟨1187010148114783720293719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12661441579891026349799669 1187010148114783720293719)
                      ·
                        rfl

theorem cell23_2311694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 1, 1, 1, 1, 5].length) (baseStart_2311694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2311694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2311694 prefixEnd_2311694 := by exact prefixLift 2311694
  have htrace : WordTrace (prefixWord ++ tailWord_2311694) baseStart_2311694 baseEnd_2311694 := by
    simpa [prefixWord, tailWord_2311694, baseEnd_2311694] using wordTrace_append hprefix tailTrace_2311694
  have hstable : (prefixWord ++ tailWord_2311694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2311694).length < 2 ^ (prefixWord ++ tailWord_2311694).sum := by decide
  have hdescent : baseEnd_2311694 < baseStart_2311694 := by decide
  rcases family_descends (prefixWord ++ tailWord_2311694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2311730 : List Nat := [3, 2, 1, 1, 2, 1, 1, 1, 4, 3, 4]
def baseStart_2311730 : Nat := 118140960795 + 2311730 * 2 ^ 59
def prefixEnd_2311730 : Nat := 4983230072969 + 3 ^ 40 * 2311730 * 2
def baseEnd_2311730 : Nat := 1187028633418345579443553

theorem tailTrace_2311730 : CollatzResearch.WordTrace tailWord_2311730 prefixEnd_2311730 1187028633418345579443553 := by
  unfold tailWord_2311730
  simp only [CollatzResearch.WordTrace]
  refine ⟨21078929978751124224129161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56210479943336331264344429 21078929978751124224129161)
  ·
    refine ⟨15809197484063343168096871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21078929978751124224129161 15809197484063343168096871)
    ·
      refine ⟨23713796226095014752145307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15809197484063343168096871 23713796226095014752145307)
      ·
        refine ⟨35570694339142522128217961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23713796226095014752145307 35570694339142522128217961)
        ·
          refine ⟨26678020754356891596163471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35570694339142522128217961 26678020754356891596163471)
          ·
            refine ⟨40017031131535337394245207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26678020754356891596163471 40017031131535337394245207)
            ·
              refine ⟨60025546697303006091367811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40017031131535337394245207 60025546697303006091367811)
              ·
                refine ⟨90038320045954509137051717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60025546697303006091367811 90038320045954509137051717)
                ·
                  refine ⟨16882185008616470463197197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 90038320045954509137051717 16882185008616470463197197)
                  ·
                    refine ⟨6330819378231176423698949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16882185008616470463197197 6330819378231176423698949)
                    ·
                      refine ⟨1187028633418345579443553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6330819378231176423698949 1187028633418345579443553)
                      ·
                        rfl

theorem cell23_2311730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 1, 4, 3, 4].length) (baseStart_2311730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2311730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2311730 prefixEnd_2311730 := by exact prefixLift 2311730
  have htrace : WordTrace (prefixWord ++ tailWord_2311730) baseStart_2311730 baseEnd_2311730 := by
    simpa [prefixWord, tailWord_2311730, baseEnd_2311730] using wordTrace_append hprefix tailTrace_2311730
  have hstable : (prefixWord ++ tailWord_2311730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2311730).length < 2 ^ (prefixWord ++ tailWord_2311730).sum := by decide
  have hdescent : baseEnd_2311730 < baseStart_2311730 := by decide
  rcases family_descends (prefixWord ++ tailWord_2311730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2311751 : List Nat := [1, 1, 4, 1, 5, 1, 1, 3, 1, 3, 2]
def baseStart_2311751 : Nat := 118140960795 + 2311751 * 2 ^ 59
def prefixEnd_2311751 : Nat := 4983230072969 + 3 ^ 40 * 2311751 * 2
def baseEnd_2311751 : Nat := 1187039416512089997280957

theorem tailTrace_2311751 : CollatzResearch.WordTrace tailWord_2311751 prefixEnd_2311751 1187039416512089997280957 := by
  unfold tailWord_2311751
  simp only [CollatzResearch.WordTrace]
  refine ⟨84316485847928417483031107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56210990565285611655354071 84316485847928417483031107)
  ·
    refine ⟨126474728771892626224546661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84316485847928417483031107 126474728771892626224546661)
    ·
      refine ⟨23714011644729867417102499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 126474728771892626224546661 23714011644729867417102499)
      ·
        refine ⟨35571017467094801125653749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23714011644729867417102499 35571017467094801125653749)
        ·
          refine ⟨3334782887540137605530039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 35571017467094801125653749 3334782887540137605530039)
          ·
            refine ⟨5002174331310206408295059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3334782887540137605530039 5002174331310206408295059)
            ·
              refine ⟨7503261496965309612442589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5002174331310206408295059 7503261496965309612442589)
              ·
                refine ⟨2813723061361991104665971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7503261496965309612442589 2813723061361991104665971)
                ·
                  refine ⟨4220584592042986656998957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2813723061361991104665971 4220584592042986656998957)
                  ·
                    refine ⟨1582719222016119996374609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4220584592042986656998957 1582719222016119996374609)
                    ·
                      refine ⟨1187039416512089997280957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1582719222016119996374609 1187039416512089997280957)
                      ·
                        rfl

theorem cell23_2311751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 1, 3, 1, 3, 2].length) (baseStart_2311751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2311751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2311751 prefixEnd_2311751 := by exact prefixLift 2311751
  have htrace : WordTrace (prefixWord ++ tailWord_2311751) baseStart_2311751 baseEnd_2311751 := by
    simpa [prefixWord, tailWord_2311751, baseEnd_2311751] using wordTrace_append hprefix tailTrace_2311751
  have hstable : (prefixWord ++ tailWord_2311751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2311751).length < 2 ^ (prefixWord ++ tailWord_2311751).sum := by decide
  have hdescent : baseEnd_2311751 < baseStart_2311751 := by decide
  rcases family_descends (prefixWord ++ tailWord_2311751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2311760 : List Nat := [2, 1, 1, 1, 1, 3, 3, 1, 4, 2, 4]
def baseStart_2311760 : Nat := 118140960795 + 2311760 * 2 ^ 59
def prefixEnd_2311760 : Nat := 4983230072969 + 3 ^ 40 * 2311760 * 2
def baseEnd_2311760 : Nat := 1187044037837980462068415

theorem tailTrace_2311760 : CollatzResearch.WordTrace tailWord_2311760 prefixEnd_2311760 1187044037837980462068415 := by
  unfold tailWord_2311760
  simp only [CollatzResearch.WordTrace]
  refine ⟨42158407052447906010054367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56211209403263874680072489 42158407052447906010054367)
  ·
    refine ⟨63237610578671859015081551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42158407052447906010054367 63237610578671859015081551)
    ·
      refine ⟨94856415868007788522622327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63237610578671859015081551 94856415868007788522622327)
      ·
        refine ⟨142284623802011682783933491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94856415868007788522622327 142284623802011682783933491)
        ·
          refine ⟨213426935703017524175900237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142284623802011682783933491 213426935703017524175900237)
          ·
            refine ⟨80035100888631571565962589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 213426935703017524175900237 80035100888631571565962589)
            ·
              refine ⟨30013162833236839337235971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 80035100888631571565962589 30013162833236839337235971)
              ·
                refine ⟨45019744249855259005853957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30013162833236839337235971 45019744249855259005853957)
                ·
                  refine ⟨8441202046847861063597617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45019744249855259005853957 8441202046847861063597617)
                  ·
                    refine ⟨6330901535135895797698213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8441202046847861063597617 6330901535135895797698213)
                    ·
                      refine ⟨1187044037837980462068415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6330901535135895797698213 1187044037837980462068415)
                      ·
                        rfl

theorem cell23_2311760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 1, 4, 2, 4].length) (baseStart_2311760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2311760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2311760 prefixEnd_2311760 := by exact prefixLift 2311760
  have htrace : WordTrace (prefixWord ++ tailWord_2311760) baseStart_2311760 baseEnd_2311760 := by
    simpa [prefixWord, tailWord_2311760, baseEnd_2311760] using wordTrace_append hprefix tailTrace_2311760
  have hstable : (prefixWord ++ tailWord_2311760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2311760).length < 2 ^ (prefixWord ++ tailWord_2311760).sum := by decide
  have hdescent : baseEnd_2311760 < baseStart_2311760 := by decide
  rcases family_descends (prefixWord ++ tailWord_2311760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2311781 : List Nat := [1, 3, 1, 3, 3, 3, 1, 1, 1, 4, 2]
def baseStart_2311781 : Nat := 118140960795 + 2311781 * 2 ^ 59
def prefixEnd_2311781 : Nat := 4983230072969 + 3 ^ 40 * 2311781 * 2
def baseEnd_2311781 : Nat := 1187054820931724879905819

theorem tailTrace_2311781 : CollatzResearch.WordTrace tailWord_2311781 prefixEnd_2311781 1187054820931724879905819 := by
  unfold tailWord_2311781
  simp only [CollatzResearch.WordTrace]
  refine ⟨84317580037819732606623197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56211720025213155071082131 84317580037819732606623197)
  ·
    refine ⟨31619092514182399727483699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84317580037819732606623197 31619092514182399727483699)
    ·
      refine ⟨47428638771273599591225549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31619092514182399727483699 47428638771273599591225549)
      ·
        refine ⟨17785739539227599846709581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47428638771273599591225549 17785739539227599846709581)
        ·
          refine ⟨6669652327210349942516093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17785739539227599846709581 6669652327210349942516093)
          ·
            refine ⟨2501119622703881228443535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6669652327210349942516093 2501119622703881228443535)
            ·
              refine ⟨3751679434055821842665303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2501119622703881228443535 3751679434055821842665303)
              ·
                refine ⟨5627519151083732763997955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3751679434055821842665303 5627519151083732763997955)
                ·
                  refine ⟨8441278726625599145996933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5627519151083732763997955 8441278726625599145996933)
                  ·
                    refine ⟨1582739761242299839874425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8441278726625599145996933 1582739761242299839874425)
                    ·
                      refine ⟨1187054820931724879905819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1582739761242299839874425 1187054820931724879905819)
                      ·
                        rfl

theorem cell23_2311781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 1, 1, 1, 4, 2].length) (baseStart_2311781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2311781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2311781 prefixEnd_2311781 := by exact prefixLift 2311781
  have htrace : WordTrace (prefixWord ++ tailWord_2311781) baseStart_2311781 baseEnd_2311781 := by
    simpa [prefixWord, tailWord_2311781, baseEnd_2311781] using wordTrace_append hprefix tailTrace_2311781
  have hstable : (prefixWord ++ tailWord_2311781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2311781).length < 2 ^ (prefixWord ++ tailWord_2311781).sum := by decide
  have hdescent : baseEnd_2311781 < baseStart_2311781 := by decide
  rcases family_descends (prefixWord ++ tailWord_2311781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2311837 : List Nat := [1, 4, 2, 1, 1, 1, 1, 1, 6, 1, 4]
def baseStart_2311837 : Nat := 118140960795 + 2311837 * 2 ^ 59
def prefixEnd_2311837 : Nat := 4983230072969 + 3 ^ 40 * 2311837 * 2
def baseEnd_2311837 : Nat := 1187083575848376660805561

theorem tailTrace_2311837 : CollatzResearch.WordTrace tailWord_2311837 prefixEnd_2311837 1187083575848376660805561 := by
  unfold tailWord_2311837
  simp only [CollatzResearch.WordTrace]
  refine ⟨84319622525616854170661765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56213081683744569447107843 84319622525616854170661765)
  ·
    refine ⟨15809929223553160156999081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 84319622525616854170661765 15809929223553160156999081)
    ·
      refine ⟨11857446917664870117749311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15809929223553160156999081 11857446917664870117749311)
      ·
        refine ⟨17786170376497305176623967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11857446917664870117749311 17786170376497305176623967)
        ·
          refine ⟨26679255564745957764935951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17786170376497305176623967 26679255564745957764935951)
          ·
            refine ⟨40018883347118936647403927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26679255564745957764935951 40018883347118936647403927)
            ·
              refine ⟨60028325020678404971105891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40018883347118936647403927 60028325020678404971105891)
              ·
                refine ⟨90042487531017607456658837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60028325020678404971105891 90042487531017607456658837)
                ·
                  refine ⟨4220741603016450349530883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 90042487531017607456658837 4220741603016450349530883)
                  ·
                    refine ⟨6331112404524675524296325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4220741603016450349530883 6331112404524675524296325)
                    ·
                      refine ⟨1187083575848376660805561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6331112404524675524296325 1187083575848376660805561)
                      ·
                        rfl

theorem cell23_2311837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 1, 6, 1, 4].length) (baseStart_2311837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2311837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2311837 prefixEnd_2311837 := by exact prefixLift 2311837
  have htrace : WordTrace (prefixWord ++ tailWord_2311837) baseStart_2311837 baseEnd_2311837 := by
    simpa [prefixWord, tailWord_2311837, baseEnd_2311837] using wordTrace_append hprefix tailTrace_2311837
  have hstable : (prefixWord ++ tailWord_2311837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2311837).length < 2 ^ (prefixWord ++ tailWord_2311837).sum := by decide
  have hdescent : baseEnd_2311837 < baseStart_2311837 := by decide
  rcases family_descends (prefixWord ++ tailWord_2311837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2311904 : List Nat := [2, 1, 1, 3, 1, 2, 3, 1, 5, 1, 3]
def baseStart_2311904 : Nat := 118140960795 + 2311904 * 2 ^ 59
def prefixEnd_2311904 : Nat := 4983230072969 + 3 ^ 40 * 2311904 * 2
def baseEnd_2311904 : Nat := 1187117979052227898667753

theorem tailTrace_2311904 : CollatzResearch.WordTrace tailWord_2311904 prefixEnd_2311904 1187117979052227898667753 := by
  unfold tailWord_2311904
  simp only [CollatzResearch.WordTrace]
  refine ⟨42161033108187062306675383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56214710810916083075567177 42161033108187062306675383)
  ·
    refine ⟨63241549662280593460013075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42161033108187062306675383 63241549662280593460013075)
    ·
      refine ⟨94862324493420890190019613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63241549662280593460013075 94862324493420890190019613)
      ·
        refine ⟨35573371685032833821257355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 94862324493420890190019613 35573371685032833821257355)
        ·
          refine ⟨53360057527549250731886033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35573371685032833821257355 53360057527549250731886033)
          ·
            refine ⟨40020043145661938048914525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53360057527549250731886033 40020043145661938048914525)
            ·
              refine ⟨15007516179623226768342947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40020043145661938048914525 15007516179623226768342947)
              ·
                refine ⟨22511274269434840152514421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15007516179623226768342947 22511274269434840152514421)
                ·
                  refine ⟨2110431962759516264298227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 22511274269434840152514421 2110431962759516264298227)
                  ·
                    refine ⟨3165647944139274396447341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2110431962759516264298227 3165647944139274396447341)
                    ·
                      refine ⟨1187117979052227898667753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3165647944139274396447341 1187117979052227898667753)
                      ·
                        rfl

theorem cell23_2311904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 1, 5, 1, 3].length) (baseStart_2311904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2311904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2311904 prefixEnd_2311904 := by exact prefixLift 2311904
  have htrace : WordTrace (prefixWord ++ tailWord_2311904) baseStart_2311904 baseEnd_2311904 := by
    simpa [prefixWord, tailWord_2311904, baseEnd_2311904] using wordTrace_append hprefix tailTrace_2311904
  have hstable : (prefixWord ++ tailWord_2311904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2311904).length < 2 ^ (prefixWord ++ tailWord_2311904).sum := by decide
  have hdescent : baseEnd_2311904 < baseStart_2311904 := by decide
  rcases family_descends (prefixWord ++ tailWord_2311904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2311937 : List Nat := [1, 2, 4, 1, 1, 1, 2, 2, 3, 6]
def baseStart_2311937 : Nat := 118140960795 + 2311937 * 2 ^ 59
def prefixEnd_2311937 : Nat := 4983230072969 + 3 ^ 40 * 2311937 * 2
def baseEnd_2311937 : Nat := 395711641304608756518367

theorem tailTrace_2311937 : CollatzResearch.WordTrace tailWord_2311937 prefixEnd_2311937 395711641304608756518367 := by
  unfold tailWord_2311937
  simp only [CollatzResearch.WordTrace]
  refine ⟨84323269825254571249302065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56215513216836380832868043 84323269825254571249302065)
  ·
    refine ⟨63242452368940928436976549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84323269825254571249302065 63242452368940928436976549)
    ·
      refine ⟨11857959819176424081933103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 63242452368940928436976549 11857959819176424081933103)
      ·
        refine ⟨17786939728764636122899655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11857959819176424081933103 17786939728764636122899655)
        ·
          refine ⟨26680409593146954184349483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17786939728764636122899655 26680409593146954184349483)
          ·
            refine ⟨40020614389720431276524225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26680409593146954184349483 40020614389720431276524225)
            ·
              refine ⟨30015460792290323457393169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40020614389720431276524225 30015460792290323457393169)
              ·
                refine ⟨22511595594217742593044877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30015460792290323457393169 22511595594217742593044877)
                ·
                  refine ⟨8441848347831653472391829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22511595594217742593044877 8441848347831653472391829)
                  ·
                    refine ⟨395711641304608756518367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8441848347831653472391829 395711641304608756518367)
                    ·
                      rfl

theorem cell23_2311937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 2, 3, 6].length) (baseStart_2311937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2311937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2311937 prefixEnd_2311937 := by exact prefixLift 2311937
  have htrace : WordTrace (prefixWord ++ tailWord_2311937) baseStart_2311937 baseEnd_2311937 := by
    simpa [prefixWord, tailWord_2311937, baseEnd_2311937] using wordTrace_append hprefix tailTrace_2311937
  have hstable : (prefixWord ++ tailWord_2311937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2311937).length < 2 ^ (prefixWord ++ tailWord_2311937).sum := by decide
  have hdescent : baseEnd_2311937 < baseStart_2311937 := by decide
  rcases family_descends (prefixWord ++ tailWord_2311937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2311938 : List Nat := [3, 4, 1, 1, 1, 1, 4, 1, 3, 1, 3]
def baseStart_2311938 : Nat := 118140960795 + 2311938 * 2 ^ 59
def prefixEnd_2311938 : Nat := 4983230072969 + 3 ^ 40 * 2311938 * 2
def baseEnd_2311938 : Nat := 1187135437394480765642597

theorem tailTrace_2311938 : CollatzResearch.WordTrace tailWord_2311938 prefixEnd_2311938 1187135437394480765642597 := by
  unfold tailWord_2311938
  simp only [CollatzResearch.WordTrace]
  refine ⟨21080826574562737105022117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56215537532167298946725645 21080826574562737105022117)
  ·
    refine ⟨3952654982730513207191647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21080826574562737105022117 3952654982730513207191647)
    ·
      refine ⟨5928982474095769810787471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3952654982730513207191647 5928982474095769810787471)
      ·
        refine ⟨8893473711143654716181207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5928982474095769810787471 8893473711143654716181207)
        ·
          refine ⟨13340210566715482074271811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8893473711143654716181207 13340210566715482074271811)
          ·
            refine ⟨20010315850073223111407717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13340210566715482074271811 20010315850073223111407717)
            ·
              refine ⟨3751934221888729333388947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20010315850073223111407717 3751934221888729333388947)
              ·
                refine ⟨5627901332833094000083421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3751934221888729333388947 5627901332833094000083421)
                ·
                  refine ⟨2110462999812410250031283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5627901332833094000083421 2110462999812410250031283)
                  ·
                    refine ⟨3165694499718615375046925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2110462999812410250031283 3165694499718615375046925)
                    ·
                      refine ⟨1187135437394480765642597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3165694499718615375046925 1187135437394480765642597)
                      ·
                        rfl

theorem cell23_2311938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 4, 1, 3, 1, 3].length) (baseStart_2311938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2311938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2311938 prefixEnd_2311938 := by exact prefixLift 2311938
  have htrace : WordTrace (prefixWord ++ tailWord_2311938) baseStart_2311938 baseEnd_2311938 := by
    simpa [prefixWord, tailWord_2311938, baseEnd_2311938] using wordTrace_append hprefix tailTrace_2311938
  have hstable : (prefixWord ++ tailWord_2311938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2311938).length < 2 ^ (prefixWord ++ tailWord_2311938).sum := by decide
  have hdescent : baseEnd_2311938 < baseStart_2311938 := by decide
  rcases family_descends (prefixWord ++ tailWord_2311938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2311947 : List Nat := [1, 1, 1, 1, 5, 1, 3, 1, 3, 1, 5]
def baseStart_2311947 : Nat := 118140960795 + 2311947 * 2 ^ 59
def prefixEnd_2311947 : Nat := 4983230072969 + 3 ^ 40 * 2311947 * 2
def baseEnd_2311947 : Nat := 1187140058720371230430055

theorem tailTrace_2311947 : CollatzResearch.WordTrace tailWord_2311947 prefixEnd_2311947 1187140058720371230430055 := by
  unfold tailWord_2311947
  simp only [CollatzResearch.WordTrace]
  refine ⟨84323634555218342957166095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56215756370145561971444063 84323634555218342957166095)
  ·
    refine ⟨126485451832827514435749143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84323634555218342957166095 126485451832827514435749143)
    ·
      refine ⟨189728177749241271653623715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126485451832827514435749143 189728177749241271653623715)
      ·
        refine ⟨284592266623861907480435573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 189728177749241271653623715 284592266623861907480435573)
        ·
          refine ⟨26680524995987053826290835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 284592266623861907480435573 26680524995987053826290835)
          ·
            refine ⟨40020787493980580739436253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26680524995987053826290835 40020787493980580739436253)
            ·
              refine ⟨15007795310242717777288595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40020787493980580739436253 15007795310242717777288595)
              ·
                refine ⟨22511692965364076665932893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15007795310242717777288595 22511692965364076665932893)
                ·
                  refine ⟨8441884862011528749724835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22511692965364076665932893 8441884862011528749724835)
                  ·
                    refine ⟨12662827293017293124587253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8441884862011528749724835 12662827293017293124587253)
                    ·
                      refine ⟨1187140058720371230430055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12662827293017293124587253 1187140058720371230430055)
                      ·
                        rfl

theorem cell23_2311947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 1, 3, 1, 5].length) (baseStart_2311947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2311947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2311947 prefixEnd_2311947 := by exact prefixLift 2311947
  have htrace : WordTrace (prefixWord ++ tailWord_2311947) baseStart_2311947 baseEnd_2311947 := by
    simpa [prefixWord, tailWord_2311947, baseEnd_2311947] using wordTrace_append hprefix tailTrace_2311947
  have hstable : (prefixWord ++ tailWord_2311947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2311947).length < 2 ^ (prefixWord ++ tailWord_2311947).sum := by decide
  have hdescent : baseEnd_2311947 < baseStart_2311947 := by decide
  rcases family_descends (prefixWord ++ tailWord_2311947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2311967 : List Nat := [1, 1, 2, 4, 2, 1, 3, 9]
def baseStart_2311967 : Nat := 118140960795 + 2311967 * 2 ^ 59
def prefixEnd_2311967 : Nat := 4983230072969 + 3 ^ 40 * 2311967 * 2
def baseEnd_2311967 : Nat := 43968530679017079710369

theorem tailTrace_2311967 : CollatzResearch.WordTrace tailWord_2311967 prefixEnd_2311967 43968530679017079710369 := by
  unfold tailWord_2311967
  simp only [CollatzResearch.WordTrace]
  refine ⟨84324364015145886372894155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56216242676763924248596103 84324364015145886372894155)
  ·
    refine ⟨126486546022718829559341233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84324364015145886372894155 126486546022718829559341233)
    ·
      refine ⟨94864909517039122169505925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126486546022718829559341233 94864909517039122169505925)
      ·
        refine ⟨17787170534444835406782361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 94864909517039122169505925 17787170534444835406782361)
        ·
          refine ⟨13340377900833626555086771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17787170534444835406782361 13340377900833626555086771)
          ·
            refine ⟨20010566851250439832630157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13340377900833626555086771 20010566851250439832630157)
            ·
              refine ⟨7503962569218914937236309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20010566851250439832630157 7503962569218914937236309)
              ·
                refine ⟨43968530679017079710369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 7503962569218914937236309 43968530679017079710369)
                ·
                  rfl

theorem cell23_2311967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 3, 9].length) (baseStart_2311967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2311967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2311967 prefixEnd_2311967 := by exact prefixLift 2311967
  have htrace : WordTrace (prefixWord ++ tailWord_2311967) baseStart_2311967 baseEnd_2311967 := by
    simpa [prefixWord, tailWord_2311967, baseEnd_2311967] using wordTrace_append hprefix tailTrace_2311967
  have hstable : (prefixWord ++ tailWord_2311967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2311967).length < 2 ^ (prefixWord ++ tailWord_2311967).sum := by decide
  have hdescent : baseEnd_2311967 < baseStart_2311967 := by decide
  rcases family_descends (prefixWord ++ tailWord_2311967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2312028 : List Nat := [2, 2, 4, 2, 2, 1, 1, 2, 1, 3, 3]
def baseStart_2312028 : Nat := 118140960795 + 2312028 * 2 ^ 59
def prefixEnd_2312028 : Nat := 4983230072969 + 3 ^ 40 * 2312028 * 2
def baseEnd_2312028 : Nat := 1187181650653385413517183

theorem tailTrace_2312028 : CollatzResearch.WordTrace tailWord_2312028 prefixEnd_2312028 1187181650653385413517183 := by
  unfold tailWord_2312028
  simp only [CollatzResearch.WordTrace]
  refine ⟨42163294433962446895432369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56217725911949929193909825 42163294433962446895432369)
  ·
    refine ⟨31622470825471835171574277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42163294433962446895432369 31622470825471835171574277)
    ·
      refine ⟨5929213279775969094670177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31622470825471835171574277 5929213279775969094670177)
      ·
        refine ⟨4446909959831976821002633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5929213279775969094670177 4446909959831976821002633)
        ·
          refine ⟨3335182469873982615751975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4446909959831976821002633 3335182469873982615751975)
          ·
            refine ⟨5002773704810973923627963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3335182469873982615751975 5002773704810973923627963)
            ·
              refine ⟨7504160557216460885441945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5002773704810973923627963 7504160557216460885441945)
              ·
                refine ⟨5628120417912345664081459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7504160557216460885441945 5628120417912345664081459)
                ·
                  refine ⟨8442180626868518496122189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5628120417912345664081459 8442180626868518496122189)
                  ·
                    refine ⟨3165817735075694436045821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8442180626868518496122189 3165817735075694436045821)
                    ·
                      refine ⟨1187181650653385413517183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3165817735075694436045821 1187181650653385413517183)
                      ·
                        rfl

theorem cell23_2312028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 1, 2, 1, 3, 3].length) (baseStart_2312028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2312028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2312028 prefixEnd_2312028 := by exact prefixLift 2312028
  have htrace : WordTrace (prefixWord ++ tailWord_2312028) baseStart_2312028 baseEnd_2312028 := by
    simpa [prefixWord, tailWord_2312028, baseEnd_2312028] using wordTrace_append hprefix tailTrace_2312028
  have hstable : (prefixWord ++ tailWord_2312028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2312028).length < 2 ^ (prefixWord ++ tailWord_2312028).sum := by decide
  have hdescent : baseEnd_2312028 < baseStart_2312028 := by decide
  rcases family_descends (prefixWord ++ tailWord_2312028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2312047 : List Nat := [1, 1, 2, 1, 3, 1, 1, 1, 1, 5, 6]
def baseStart_2312047 : Nat := 118140960795 + 2312047 * 2 ^ 59
def prefixEnd_2312047 : Nat := 4983230072969 + 3 ^ 40 * 2312047 * 2
def baseEnd_2312047 : Nat := 1187191406785820839179595

theorem tailTrace_2312047 : CollatzResearch.WordTrace tailWord_2312047 prefixEnd_2312047 1187191406785820839179595 := by
  unfold tailWord_2312047
  simp only [CollatzResearch.WordTrace]
  refine ⟨84327281854856060035806395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56218187903237373357204263 84327281854856060035806395)
  ·
    refine ⟨126490922782284090053709593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84327281854856060035806395 126490922782284090053709593)
    ·
      refine ⟨94868192086713067540282195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126490922782284090053709593 94868192086713067540282195)
      ·
        refine ⟨142302288130069601310423293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94868192086713067540282195 142302288130069601310423293)
        ·
          refine ⟨53363358048776100491408735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 142302288130069601310423293 53363358048776100491408735)
          ·
            refine ⟨80045037073164150737113103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53363358048776100491408735 80045037073164150737113103)
            ·
              refine ⟨120067555609746226105669655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80045037073164150737113103 120067555609746226105669655)
              ·
                refine ⟨180101333414619339158504483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 120067555609746226105669655 180101333414619339158504483)
                ·
                  refine ⟨270152000121929008737756725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 180101333414619339158504483 270152000121929008737756725)
                  ·
                    refine ⟨25326750011430844569164693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 270152000121929008737756725 25326750011430844569164693)
                    ·
                      refine ⟨1187191406785820839179595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 25326750011430844569164693 1187191406785820839179595)
                      ·
                        rfl

theorem cell23_2312047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 5, 6].length) (baseStart_2312047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2312047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2312047 prefixEnd_2312047 := by exact prefixLift 2312047
  have htrace : WordTrace (prefixWord ++ tailWord_2312047) baseStart_2312047 baseEnd_2312047 := by
    simpa [prefixWord, tailWord_2312047, baseEnd_2312047] using wordTrace_append hprefix tailTrace_2312047
  have hstable : (prefixWord ++ tailWord_2312047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2312047).length < 2 ^ (prefixWord ++ tailWord_2312047).sum := by decide
  have hdescent : baseEnd_2312047 < baseStart_2312047 := by decide
  rcases family_descends (prefixWord ++ tailWord_2312047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2312064 : List Nat := [2, 1, 1, 2, 1, 2, 5, 1, 2, 2, 4]
def baseStart_2312064 : Nat := 118140960795 + 2312064 * 2 ^ 59
def prefixEnd_2312064 : Nat := 4983230072969 + 3 ^ 40 * 2312064 * 2
def baseEnd_2312064 : Nat := 1187200135956947272667017

theorem tailTrace_2312064 : CollatzResearch.WordTrace tailWord_2312064 prefixEnd_2312064 1187200135956947272667017 := by
  unfold tailWord_2312064
  simp only [CollatzResearch.WordTrace]
  refine ⟨42163950947897235969587623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56218601263862981292783497 42163950947897235969587623)
  ·
    refine ⟨63245926421845853954381435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42163950947897235969587623 63245926421845853954381435)
    ·
      refine ⟨94868889632768780931572153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63245926421845853954381435 94868889632768780931572153)
      ·
        refine ⟨71151667224576585698679115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94868889632768780931572153 71151667224576585698679115)
        ·
          refine ⟨106727500836864878548018673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71151667224576585698679115 106727500836864878548018673)
          ·
            refine ⟨80045625627648658911014005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 106727500836864878548018673 80045625627648658911014005)
            ·
              refine ⟨7504277402592061772907563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 80045625627648658911014005 7504277402592061772907563)
              ·
                refine ⟨11256416103888092659361345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7504277402592061772907563 11256416103888092659361345)
                ·
                  refine ⟨8442312077916069494521009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11256416103888092659361345 8442312077916069494521009)
                  ·
                    refine ⟨6331734058437052120890757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8442312077916069494521009 6331734058437052120890757)
                    ·
                      refine ⟨1187200135956947272667017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6331734058437052120890757 1187200135956947272667017)
                      ·
                        rfl

theorem cell23_2312064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5, 1, 2, 2, 4].length) (baseStart_2312064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2312064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2312064 prefixEnd_2312064 := by exact prefixLift 2312064
  have htrace : WordTrace (prefixWord ++ tailWord_2312064) baseStart_2312064 baseEnd_2312064 := by
    simpa [prefixWord, tailWord_2312064, baseEnd_2312064] using wordTrace_append hprefix tailTrace_2312064
  have hstable : (prefixWord ++ tailWord_2312064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2312064).length < 2 ^ (prefixWord ++ tailWord_2312064).sum := by decide
  have hdescent : baseEnd_2312064 < baseStart_2312064 := by decide
  rcases family_descends (prefixWord ++ tailWord_2312064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2312114 : List Nat := [3, 2, 1, 1, 1, 1, 1, 5, 1, 2, 5]
def baseStart_2312114 : Nat := 118140960795 + 2312114 * 2 ^ 59
def prefixEnd_2312114 : Nat := 4983230072969 + 3 ^ 40 * 2312114 * 2
def baseEnd_2312114 : Nat := 1187225809989672077041787

theorem tailTrace_2312114 : CollatzResearch.WordTrace tailWord_2312114 prefixEnd_2312114 1187225809989672077041787 := by
  unfold tailWord_2312114
  simp only [CollatzResearch.WordTrace]
  refine ⟨21082431386403332619623849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56219817030408886985663597 21082431386403332619623849)
  ·
    refine ⟨15811823539802499464717887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21082431386403332619623849 15811823539802499464717887)
    ·
      refine ⟨23717735309703749197076831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15811823539802499464717887 23717735309703749197076831)
      ·
        refine ⟨35576602964555623795615247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23717735309703749197076831 35576602964555623795615247)
        ·
          refine ⟨53364904446833435693422871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35576602964555623795615247 53364904446833435693422871)
          ·
            refine ⟨80047356670250153540134307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53364904446833435693422871 80047356670250153540134307)
            ·
              refine ⟨120071035005375230310201461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80047356670250153540134307 120071035005375230310201461)
              ·
                refine ⟨11256659531753927841581387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 120071035005375230310201461 11256659531753927841581387)
                ·
                  refine ⟨16884989297630891762372081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11256659531753927841581387 16884989297630891762372081)
                  ·
                    refine ⟨12663741973223168821779061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16884989297630891762372081 12663741973223168821779061)
                    ·
                      refine ⟨1187225809989672077041787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12663741973223168821779061 1187225809989672077041787)
                      ·
                        rfl

theorem cell23_2312114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 5, 1, 2, 5].length) (baseStart_2312114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2312114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2312114 prefixEnd_2312114 := by exact prefixLift 2312114
  have htrace : WordTrace (prefixWord ++ tailWord_2312114) baseStart_2312114 baseEnd_2312114 := by
    simpa [prefixWord, tailWord_2312114, baseEnd_2312114] using wordTrace_append hprefix tailTrace_2312114
  have hstable : (prefixWord ++ tailWord_2312114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2312114).length < 2 ^ (prefixWord ++ tailWord_2312114).sum := by decide
  have hdescent : baseEnd_2312114 < baseStart_2312114 := by decide
  rcases family_descends (prefixWord ++ tailWord_2312114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2312161 : List Nat := [1, 2, 3, 1, 2, 1, 3, 1, 4, 2, 3]
def baseStart_2312161 : Nat := 118140960795 + 2312161 * 2 ^ 59
def prefixEnd_2312161 : Nat := 4983230072969 + 3 ^ 40 * 2312161 * 2
def baseEnd_2312161 : Nat := 1187249943580433393154071

theorem tailTrace_2312161 : CollatzResearch.WordTrace tailWord_2312161 prefixEnd_2312161 1187249943580433393154071 := by
  unfold tailWord_2312161
  simp only [CollatzResearch.WordTrace]
  refine ⟨84331439776443057505456337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56220959850962038336970891 84331439776443057505456337)
  ·
    refine ⟨63248579832332293129092253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84331439776443057505456337 63248579832332293129092253)
    ·
      refine ⟨23718217437124609923409595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63248579832332293129092253 23718217437124609923409595)
      ·
        refine ⟨35577326155686914885114393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23718217437124609923409595 35577326155686914885114393)
        ·
          refine ⟨26682994616765186163835795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35577326155686914885114393 26682994616765186163835795)
          ·
            refine ⟨40024491925147779245753693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26682994616765186163835795 40024491925147779245753693)
            ·
              refine ⟨15009184471930417217157635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40024491925147779245753693 15009184471930417217157635)
              ·
                refine ⟨22513776707895625825736453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15009184471930417217157635 22513776707895625825736453)
                ·
                  refine ⟨4221333132730429842325585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22513776707895625825736453 4221333132730429842325585)
                  ·
                    refine ⟨3165999849547822381744189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4221333132730429842325585 3165999849547822381744189)
                    ·
                      refine ⟨1187249943580433393154071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3165999849547822381744189 1187249943580433393154071)
                      ·
                        rfl

theorem cell23_2312161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 1, 4, 2, 3].length) (baseStart_2312161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2312161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2312161 prefixEnd_2312161 := by exact prefixLift 2312161
  have htrace : WordTrace (prefixWord ++ tailWord_2312161) baseStart_2312161 baseEnd_2312161 := by
    simpa [prefixWord, tailWord_2312161, baseEnd_2312161] using wordTrace_append hprefix tailTrace_2312161
  have hstable : (prefixWord ++ tailWord_2312161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2312161).length < 2 ^ (prefixWord ++ tailWord_2312161).sum := by decide
  have hdescent : baseEnd_2312161 < baseStart_2312161 := by decide
  rcases family_descends (prefixWord ++ tailWord_2312161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2312164 : List Nat := [2, 3, 1, 1, 1, 1, 3, 3, 8]
def baseStart_2312164 : Nat := 118140960795 + 2312164 * 2 ^ 59
def prefixEnd_2312164 : Nat := 4983230072969 + 3 ^ 40 * 2312164 * 2
def baseEnd_2312164 : Nat := 131916831558044097935173

theorem tailTrace_2312164 : CollatzResearch.WordTrace tailWord_2312164 prefixEnd_2312164 131916831558044097935173 := by
  unfold tailWord_2312164
  simp only [CollatzResearch.WordTrace]
  refine ⟨42165774597716094508907773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56221032796954792678543697 42165774597716094508907773)
  ·
    refine ⟨15812165474143535440840415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42165774597716094508907773 15812165474143535440840415)
    ·
      refine ⟨23718248211215303161260623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15812165474143535440840415 23718248211215303161260623)
      ·
        refine ⟨35577372316822954741890935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23718248211215303161260623 35577372316822954741890935)
        ·
          refine ⟨53366058475234432112836403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35577372316822954741890935 53366058475234432112836403)
          ·
            refine ⟨80049087712851648169254605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53366058475234432112836403 80049087712851648169254605)
            ·
              refine ⟨30018407892319368063470477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 80049087712851648169254605 30018407892319368063470477)
              ·
                refine ⟨11256902959619763023801429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30018407892319368063470477 11256902959619763023801429)
                ·
                  refine ⟨131916831558044097935173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 11256902959619763023801429 131916831558044097935173)
                  ·
                    rfl

theorem cell23_2312164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 3, 8].length) (baseStart_2312164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2312164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2312164 prefixEnd_2312164 := by exact prefixLift 2312164
  have htrace : WordTrace (prefixWord ++ tailWord_2312164) baseStart_2312164 baseEnd_2312164 := by
    simpa [prefixWord, tailWord_2312164, baseEnd_2312164] using wordTrace_append hprefix tailTrace_2312164
  have hstable : (prefixWord ++ tailWord_2312164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2312164).length < 2 ^ (prefixWord ++ tailWord_2312164).sum := by decide
  have hdescent : baseEnd_2312164 < baseStart_2312164 := by decide
  rcases family_descends (prefixWord ++ tailWord_2312164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2312184 : List Nat := [2, 1, 2, 1, 1, 3, 2, 2, 1, 2, 6]
def baseStart_2312184 : Nat := 118140960795 + 2312184 * 2 ^ 59
def prefixEnd_2312184 : Nat := 4983230072969 + 3 ^ 40 * 2312184 * 2
def baseEnd_2312184 : Nat := 1187261753635486803166465

theorem tailTrace_2312184 : CollatzResearch.WordTrace tailWord_2312184 prefixEnd_2312184 1187261753635486803166465 := by
  unfold tailWord_2312184
  simp only [CollatzResearch.WordTrace]
  refine ⟨42166139327679866216771803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56221519103573154955695737 42166139327679866216771803)
  ·
    refine ⟨63249208991519799325157705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42166139327679866216771803 63249208991519799325157705)
    ·
      refine ⟨47436906743639849493868279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63249208991519799325157705 47436906743639849493868279)
      ·
        refine ⟨71155360115459774240802419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47436906743639849493868279 71155360115459774240802419)
        ·
          refine ⟨106733040173189661361203629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71155360115459774240802419 106733040173189661361203629)
          ·
            refine ⟨40024890064946123010451361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 106733040173189661361203629 40024890064946123010451361)
            ·
              refine ⟨30018667548709592257838521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40024890064946123010451361 30018667548709592257838521)
              ·
                refine ⟨22514000661532194193378891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30018667548709592257838521 22514000661532194193378891)
                ·
                  refine ⟨33771000992298291290068337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22514000661532194193378891 33771000992298291290068337)
                  ·
                    refine ⟨25328250744223718467551253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 33771000992298291290068337 25328250744223718467551253)
                    ·
                      refine ⟨1187261753635486803166465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 25328250744223718467551253 1187261753635486803166465)
                      ·
                        rfl

theorem cell23_2312184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 2, 1, 2, 6].length) (baseStart_2312184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2312184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2312184 prefixEnd_2312184 := by exact prefixLift 2312184
  have htrace : WordTrace (prefixWord ++ tailWord_2312184) baseStart_2312184 baseEnd_2312184 := by
    simpa [prefixWord, tailWord_2312184, baseEnd_2312184] using wordTrace_append hprefix tailTrace_2312184
  have hstable : (prefixWord ++ tailWord_2312184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2312184).length < 2 ^ (prefixWord ++ tailWord_2312184).sum := by decide
  have hdescent : baseEnd_2312184 < baseStart_2312184 := by decide
  rcases family_descends (prefixWord ++ tailWord_2312184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2312211 : List Nat := [1, 1, 1, 2, 1, 4, 2, 5, 1, 5]
def baseStart_2312211 : Nat := 118140960795 + 2312211 * 2 ^ 59
def prefixEnd_2312211 : Nat := 4983230072969 + 3 ^ 40 * 2312211 * 2
def baseEnd_2312211 : Nat := 395758539204386065842947

theorem tailTrace_2312211 : CollatzResearch.WordTrace tailWord_2312211 prefixEnd_2312211 395758539204386065842947 := by
  unfold tailWord_2312211
  simp only [CollatzResearch.WordTrace]
  refine ⟨84333263426261916044776487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56222175617507944029850991 84333263426261916044776487)
  ·
    refine ⟨126499895139392874067164731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84333263426261916044776487 126499895139392874067164731)
    ·
      refine ⟨189749842709089311100747097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126499895139392874067164731 189749842709089311100747097)
      ·
        refine ⟨142312382031816983325560323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 189749842709089311100747097 142312382031816983325560323)
        ·
          refine ⟨213468573047725474988340485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142312382031816983325560323 213468573047725474988340485)
          ·
            refine ⟨40025357446448526560313841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 213468573047725474988340485 40025357446448526560313841)
            ·
              refine ⟨30019018084836394920235381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40025357446448526560313841 30019018084836394920235381)
              ·
                refine ⟨2814282945453412023772067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30019018084836394920235381 2814282945453412023772067)
                ·
                  refine ⟨4221424418180118035658101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2814282945453412023772067 4221424418180118035658101)
                  ·
                    refine ⟨395758539204386065842947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4221424418180118035658101 395758539204386065842947)
                    ·
                      rfl

theorem cell23_2312211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 5, 1, 5].length) (baseStart_2312211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2312211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2312211 prefixEnd_2312211 := by exact prefixLift 2312211
  have htrace : WordTrace (prefixWord ++ tailWord_2312211) baseStart_2312211 baseEnd_2312211 := by
    simpa [prefixWord, tailWord_2312211, baseEnd_2312211] using wordTrace_append hprefix tailTrace_2312211
  have hstable : (prefixWord ++ tailWord_2312211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2312211).length < 2 ^ (prefixWord ++ tailWord_2312211).sum := by decide
  have hdescent : baseEnd_2312211 < baseStart_2312211 := by decide
  rcases family_descends (prefixWord ++ tailWord_2312211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2312241 : List Nat := [1, 2, 2, 3, 1, 3, 1, 3, 1, 6]
def baseStart_2312241 : Nat := 118140960795 + 2312241 * 2 ^ 59
def prefixEnd_2312241 : Nat := 4983230072969 + 3 ^ 40 * 2312241 * 2
def baseEnd_2312241 : Nat := 395763674010931026717901

theorem tailTrace_2312241 : CollatzResearch.WordTrace tailWord_2312241 prefixEnd_2312241 395763674010931026717901 := by
  unfold tailWord_2312241
  simp only [CollatzResearch.WordTrace]
  refine ⟨84334357616153231168368577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56222905077435487445579051 84334357616153231168368577)
  ·
    refine ⟨63250768212114923376276433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84334357616153231168368577 63250768212114923376276433)
    ·
      refine ⟨47438076159086192532207325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63250768212114923376276433 47438076159086192532207325)
      ·
        refine ⟨17789278559657322199577747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47438076159086192532207325 17789278559657322199577747)
        ·
          refine ⟨26683917839485983299366621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17789278559657322199577747 26683917839485983299366621)
          ·
            refine ⟨10006469189807243737262483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26683917839485983299366621 10006469189807243737262483)
            ·
              refine ⟨15009703784710865605893725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10006469189807243737262483 15009703784710865605893725)
              ·
                refine ⟨5628638919266574602210147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15009703784710865605893725 5628638919266574602210147)
                ·
                  refine ⟨8442958378899861903315221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5628638919266574602210147 8442958378899861903315221)
                  ·
                    refine ⟨395763674010931026717901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8442958378899861903315221 395763674010931026717901)
                    ·
                      rfl

theorem cell23_2312241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 3, 1, 6].length) (baseStart_2312241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2312241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2312241 prefixEnd_2312241 := by exact prefixLift 2312241
  have htrace : WordTrace (prefixWord ++ tailWord_2312241) baseStart_2312241 baseEnd_2312241 := by
    simpa [prefixWord, tailWord_2312241, baseEnd_2312241] using wordTrace_append hprefix tailTrace_2312241
  have hstable : (prefixWord ++ tailWord_2312241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2312241).length < 2 ^ (prefixWord ++ tailWord_2312241).sum := by decide
  have hdescent : baseEnd_2312241 < baseStart_2312241 := by decide
  rcases family_descends (prefixWord ++ tailWord_2312241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2312282 : List Nat := [3, 1, 1, 2, 1, 1, 3, 6, 1, 2, 2]
def baseStart_2312282 : Nat := 118140960795 + 2312282 * 2 ^ 59
def prefixEnd_2312282 : Nat := 4983230072969 + 3 ^ 40 * 2312282 * 2
def baseEnd_2312282 : Nat := 1187312074739627419741015

theorem tailTrace_2312282 : CollatzResearch.WordTrace tailWord_2312282 prefixEnd_2312282 1187312074739627419741015 := by
  unfold tailWord_2312282
  simp only [CollatzResearch.WordTrace]
  refine ⟨21083963252251173792652775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56223902006003130113740733 21083963252251173792652775)
  ·
    refine ⟨31625944878376760688979163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21083963252251173792652775 31625944878376760688979163)
    ·
      refine ⟨47438917317565141033468745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31625944878376760688979163 47438917317565141033468745)
      ·
        refine ⟨35579187988173855775101559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47438917317565141033468745 35579187988173855775101559)
        ·
          refine ⟨53368781982260783662652339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35579187988173855775101559 53368781982260783662652339)
          ·
            refine ⟨80053172973391175493978509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53368781982260783662652339 80053172973391175493978509)
            ·
              refine ⟨30019939865021690810241941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 80053172973391175493978509 30019939865021690810241941)
              ·
                refine ⟨1407184681172891756730091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 30019939865021690810241941 1407184681172891756730091)
                ·
                  refine ⟨2110777021759337635095137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1407184681172891756730091 2110777021759337635095137)
                  ·
                    refine ⟨1583082766319503226321353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2110777021759337635095137 1583082766319503226321353)
                    ·
                      refine ⟨1187312074739627419741015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1583082766319503226321353 1187312074739627419741015)
                      ·
                        rfl

theorem cell23_2312282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 6, 1, 2, 2].length) (baseStart_2312282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2312282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2312282 prefixEnd_2312282 := by exact prefixLift 2312282
  have htrace : WordTrace (prefixWord ++ tailWord_2312282) baseStart_2312282 baseEnd_2312282 := by
    simpa [prefixWord, tailWord_2312282, baseEnd_2312282] using wordTrace_append hprefix tailTrace_2312282
  have hstable : (prefixWord ++ tailWord_2312282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2312282).length < 2 ^ (prefixWord ++ tailWord_2312282).sum := by decide
  have hdescent : baseEnd_2312282 < baseStart_2312282 := by decide
  rcases family_descends (prefixWord ++ tailWord_2312282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2312285 : List Nat := [1, 4, 4, 1, 1, 2, 1, 2, 1, 1, 5]
def baseStart_2312285 : Nat := 118140960795 + 2312285 * 2 ^ 59
def prefixEnd_2312285 : Nat := 4983230072969 + 3 ^ 40 * 2312285 * 2
def baseEnd_2312285 : Nat := 1187313615181590908003501

theorem tailTrace_2312285 : CollatzResearch.WordTrace tailWord_2312285 prefixEnd_2312285 1187313615181590908003501 := by
  unfold tailWord_2312285
  simp only [CollatzResearch.WordTrace]
  refine ⟨84335962427993826682970309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56223974951995884455313539 84335962427993826682970309)
  ·
    refine ⟨15812992955248842503056933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 84335962427993826682970309 15812992955248842503056933)
    ·
      refine ⟨2964936179109157969323175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15812992955248842503056933 2964936179109157969323175)
      ·
        refine ⟨4447404268663736953984763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2964936179109157969323175 4447404268663736953984763)
        ·
          refine ⟨6671106402995605430977145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4447404268663736953984763 6671106402995605430977145)
          ·
            refine ⟨5003329802246704073232859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6671106402995605430977145 5003329802246704073232859)
            ·
              refine ⟨7504994703370056109849289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5003329802246704073232859 7504994703370056109849289)
              ·
                refine ⟨5628746027527542082386967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7504994703370056109849289 5628746027527542082386967)
                ·
                  refine ⟨8443119041291313123580451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5628746027527542082386967 8443119041291313123580451)
                  ·
                    refine ⟨12664678561936969685370677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8443119041291313123580451 12664678561936969685370677)
                    ·
                      refine ⟨1187313615181590908003501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12664678561936969685370677 1187313615181590908003501)
                      ·
                        rfl

theorem cell23_2312285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_2312285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2312285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2312285 prefixEnd_2312285 := by exact prefixLift 2312285
  have htrace : WordTrace (prefixWord ++ tailWord_2312285) baseStart_2312285 baseEnd_2312285 := by
    simpa [prefixWord, tailWord_2312285, baseEnd_2312285] using wordTrace_append hprefix tailTrace_2312285
  have hstable : (prefixWord ++ tailWord_2312285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2312285).length < 2 ^ (prefixWord ++ tailWord_2312285).sum := by decide
  have hdescent : baseEnd_2312285 < baseStart_2312285 := by decide
  rcases family_descends (prefixWord ++ tailWord_2312285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2312311 : List Nat := [1, 1, 3, 1, 1, 5, 1, 1, 2, 2, 5]
def baseStart_2312311 : Nat := 118140960795 + 2312311 * 2 ^ 59
def prefixEnd_2312311 : Nat := 4983230072969 + 3 ^ 40 * 2312311 * 2
def baseEnd_2312311 : Nat := 1187326965678607806278381

theorem tailTrace_2312311 : CollatzResearch.WordTrace tailWord_2312311 prefixEnd_2312311 1187326965678607806278381 := by
  unfold tailWord_2312311
  simp only [CollatzResearch.WordTrace]
  refine ⟨84336910725899633123416787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56224607150599755415611191 84336910725899633123416787)
  ·
    refine ⟨126505366088849449685125181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84336910725899633123416787 126505366088849449685125181)
    ·
      refine ⟨47439512283318543631921943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 126505366088849449685125181 47439512283318543631921943)
      ·
        refine ⟨71159268424977815447882915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47439512283318543631921943 71159268424977815447882915)
        ·
          refine ⟨106738902637466723171824373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71159268424977815447882915 106738902637466723171824373)
          ·
            refine ⟨10006772122262505297358535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 106738902637466723171824373 10006772122262505297358535)
            ·
              refine ⟨15010158183393757946037803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10006772122262505297358535 15010158183393757946037803)
              ·
                refine ⟨22515237275090636919056705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15010158183393757946037803 22515237275090636919056705)
                ·
                  refine ⟨16886427956317977689292529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22515237275090636919056705 16886427956317977689292529)
                  ·
                    refine ⟨12664820967238483266969397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16886427956317977689292529 12664820967238483266969397)
                    ·
                      refine ⟨1187326965678607806278381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12664820967238483266969397 1187326965678607806278381)
                      ·
                        rfl

theorem cell23_2312311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 1, 2, 2, 5].length) (baseStart_2312311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2312311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2312311 prefixEnd_2312311 := by exact prefixLift 2312311
  have htrace : WordTrace (prefixWord ++ tailWord_2312311) baseStart_2312311 baseEnd_2312311 := by
    simpa [prefixWord, tailWord_2312311, baseEnd_2312311] using wordTrace_append hprefix tailTrace_2312311
  have hstable : (prefixWord ++ tailWord_2312311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2312311).length < 2 ^ (prefixWord ++ tailWord_2312311).sum := by decide
  have hdescent : baseEnd_2312311 < baseStart_2312311 := by decide
  rcases family_descends (prefixWord ++ tailWord_2312311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2312338 : List Nat := [3, 2, 3, 1, 1, 1, 2, 1, 2, 3, 4]
def baseStart_2312338 : Nat := 118140960795 + 2312338 * 2 ^ 59
def prefixEnd_2312338 : Nat := 4983230072969 + 3 ^ 40 * 2312338 * 2
def baseEnd_2312338 : Nat := 1187340829656279200640757

theorem tailTrace_2312338 : CollatzResearch.WordTrace tailWord_2312338 prefixEnd_2312338 1187340829656279200640757 := by
  unfold tailWord_2312338
  simp only [CollatzResearch.WordTrace]
  refine ⟨21084473874200454183662417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56225263664534544489766445 21084473874200454183662417)
  ·
    refine ⟨15813355405650340637746813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21084473874200454183662417 15813355405650340637746813)
    ·
      refine ⟨5930008277118877739155055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15813355405650340637746813 5930008277118877739155055)
      ·
        refine ⟨8895012415678316608732583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5930008277118877739155055 8895012415678316608732583)
        ·
          refine ⟨13342518623517474913098875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8895012415678316608732583 13342518623517474913098875)
          ·
            refine ⟨20013777935276212369648313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13342518623517474913098875 20013777935276212369648313)
            ·
              refine ⟨15010333451457159277236235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20013777935276212369648313 15010333451457159277236235)
              ·
                refine ⟨22515500177185738915854353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15010333451457159277236235 22515500177185738915854353)
                ·
                  refine ⟨16886625132889304186890765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22515500177185738915854353 16886625132889304186890765)
                  ·
                    refine ⟨6332484424833489070084037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16886625132889304186890765 6332484424833489070084037)
                    ·
                      refine ⟨1187340829656279200640757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6332484424833489070084037 1187340829656279200640757)
                      ·
                        rfl

theorem cell23_2312338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 1, 2, 3, 4].length) (baseStart_2312338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2312338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2312338 prefixEnd_2312338 := by exact prefixLift 2312338
  have htrace : WordTrace (prefixWord ++ tailWord_2312338) baseStart_2312338 baseEnd_2312338 := by
    simpa [prefixWord, tailWord_2312338, baseEnd_2312338] using wordTrace_append hprefix tailTrace_2312338
  have hstable : (prefixWord ++ tailWord_2312338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2312338).length < 2 ^ (prefixWord ++ tailWord_2312338).sum := by decide
  have hdescent : baseEnd_2312338 < baseStart_2312338 := by decide
  rcases family_descends (prefixWord ++ tailWord_2312338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2312341 : List Nat := [1, 3, 2, 1, 1, 1, 3, 2, 1, 3, 5]
def baseStart_2312341 : Nat := 118140960795 + 2312341 * 2 ^ 59
def prefixEnd_2312341 : Nat := 4983230072969 + 3 ^ 40 * 2312341 * 2
def baseEnd_2312341 : Nat := 1187342370098242688903243

theorem tailTrace_2312341 : CollatzResearch.WordTrace tailWord_2312341 prefixEnd_2312341 1187342370098242688903243 := by
  unfold tailWord_2312341
  simp only [CollatzResearch.WordTrace]
  refine ⟨84338004915790948247008877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56225336610527298831339251 84338004915790948247008877)
  ·
    refine ⟨31626751843421605592628329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84338004915790948247008877 31626751843421605592628329)
    ·
      refine ⟨23720063882566204194471247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31626751843421605592628329 23720063882566204194471247)
      ·
        refine ⟨35580095823849306291706871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23720063882566204194471247 35580095823849306291706871)
        ·
          refine ⟨53370143735773959437560307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35580095823849306291706871 53370143735773959437560307)
          ·
            refine ⟨80055215603660939156340461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53370143735773959437560307 80055215603660939156340461)
            ·
              refine ⟨30020705851372852183627673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 80055215603660939156340461 30020705851372852183627673)
              ·
                refine ⟨22515529388529639137720755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30020705851372852183627673 22515529388529639137720755)
                ·
                  refine ⟨33773294082794458706581133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22515529388529639137720755 33773294082794458706581133)
                  ·
                    refine ⟨12664985281047922014967925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 33773294082794458706581133 12664985281047922014967925)
                    ·
                      refine ⟨1187342370098242688903243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12664985281047922014967925 1187342370098242688903243)
                      ·
                        rfl

theorem cell23_2312341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 2, 1, 3, 5].length) (baseStart_2312341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2312341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2312341 prefixEnd_2312341 := by exact prefixLift 2312341
  have htrace : WordTrace (prefixWord ++ tailWord_2312341) baseStart_2312341 baseEnd_2312341 := by
    simpa [prefixWord, tailWord_2312341, baseEnd_2312341] using wordTrace_append hprefix tailTrace_2312341
  have hstable : (prefixWord ++ tailWord_2312341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2312341).length < 2 ^ (prefixWord ++ tailWord_2312341).sum := by decide
  have hdescent : baseEnd_2312341 < baseStart_2312341 := by decide
  rcases family_descends (prefixWord ++ tailWord_2312341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2312349 : List Nat := [1, 4, 2, 1, 1, 5, 2, 1, 2, 1, 3]
def baseStart_2312349 : Nat := 118140960795 + 2312349 * 2 ^ 59
def prefixEnd_2312349 : Nat := 4983230072969 + 3 ^ 40 * 2312349 * 2
def baseEnd_2312349 : Nat := 1187346477943478657603207

theorem tailTrace_2312349 : CollatzResearch.WordTrace tailWord_2312349 prefixEnd_2312349 1187346477943478657603207 := by
  unfold tailWord_2312349
  simp only [CollatzResearch.WordTrace]
  refine ⟨84338296699761965613300101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56225531133174643742200067 84338296699761965613300101)
  ·
    refine ⟨15813430631205368552493769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 84338296699761965613300101 15813430631205368552493769)
    ·
      refine ⟨11860072973404026414370327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15813430631205368552493769 11860072973404026414370327)
      ·
        refine ⟨17790109460106039621555491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11860072973404026414370327 17790109460106039621555491)
        ·
          refine ⟨26685164190159059432333237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17790109460106039621555491 26685164190159059432333237)
          ·
            refine ⟨2501734142827411821781241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 26685164190159059432333237 2501734142827411821781241)
            ·
              refine ⟨1876300607120558866335931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2501734142827411821781241 1876300607120558866335931)
              ·
                refine ⟨2814450910680838299503897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1876300607120558866335931 2814450910680838299503897)
                ·
                  refine ⟨2110838183010628724627923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2814450910680838299503897 2110838183010628724627923)
                  ·
                    refine ⟨3166257274515943086941885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2110838183010628724627923 3166257274515943086941885)
                    ·
                      refine ⟨1187346477943478657603207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3166257274515943086941885 1187346477943478657603207)
                      ·
                        rfl

theorem cell23_2312349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 2, 1, 2, 1, 3].length) (baseStart_2312349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2312349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2312349 prefixEnd_2312349 := by exact prefixLift 2312349
  have htrace : WordTrace (prefixWord ++ tailWord_2312349) baseStart_2312349 baseEnd_2312349 := by
    simpa [prefixWord, tailWord_2312349, baseEnd_2312349] using wordTrace_append hprefix tailTrace_2312349
  have hstable : (prefixWord ++ tailWord_2312349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2312349).length < 2 ^ (prefixWord ++ tailWord_2312349).sum := by decide
  have hdescent : baseEnd_2312349 < baseStart_2312349 := by decide
  rcases family_descends (prefixWord ++ tailWord_2312349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2312391 : List Nat := [1, 1, 4, 1, 1, 1, 1, 1, 5, 7]
def baseStart_2312391 : Nat := 118140960795 + 2312391 * 2 ^ 59
def prefixEnd_2312391 : Nat := 4983230072969 + 3 ^ 40 * 2312391 * 2
def baseEnd_2312391 : Nat := 395789348043655831092671

theorem tailTrace_2312391 : CollatzResearch.WordTrace tailWord_2312391 prefixEnd_2312391 395789348043655831092671 := by
  unfold tailWord_2312391
  simp only [CollatzResearch.WordTrace]
  refine ⟨84339828565609806786329027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56226552377073204524219351 84339828565609806786329027)
  ·
    refine ⟨126509742848414710179493541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84339828565609806786329027 126509742848414710179493541)
    ·
      refine ⟨23720576784077758158655039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 126509742848414710179493541 23720576784077758158655039)
      ·
        refine ⟨35580865176116637237982559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23720576784077758158655039 35580865176116637237982559)
        ·
          refine ⟨53371297764174955856973839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35580865176116637237982559 53371297764174955856973839)
          ·
            refine ⟨80056946646262433785460759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53371297764174955856973839 80056946646262433785460759)
            ·
              refine ⟨120085419969393650678191139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80056946646262433785460759 120085419969393650678191139)
              ·
                refine ⟨180128129954090476017286709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 120085419969393650678191139 180128129954090476017286709)
                ·
                  refine ⟨16887012183195982126620629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 180128129954090476017286709 16887012183195982126620629)
                  ·
                    refine ⟨395789348043655831092671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16887012183195982126620629 395789348043655831092671)
                    ·
                      rfl

theorem cell23_2312391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 5, 7].length) (baseStart_2312391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2312391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2312391 prefixEnd_2312391 := by exact prefixLift 2312391
  have htrace : WordTrace (prefixWord ++ tailWord_2312391) baseStart_2312391 baseEnd_2312391 := by
    simpa [prefixWord, tailWord_2312391, baseEnd_2312391] using wordTrace_append hprefix tailTrace_2312391
  have hstable : (prefixWord ++ tailWord_2312391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2312391).length < 2 ^ (prefixWord ++ tailWord_2312391).sum := by decide
  have hdescent : baseEnd_2312391 < baseStart_2312391 := by decide
  rcases family_descends (prefixWord ++ tailWord_2312391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2312406 : List Nat := [5, 2, 1, 2, 1, 1, 2, 3, 2, 2, 2]
def baseStart_2312406 : Nat := 118140960795 + 2312406 * 2 ^ 59
def prefixEnd_2312406 : Nat := 4983230072969 + 3 ^ 40 * 2312406 * 2
def baseEnd_2312406 : Nat := 1187375746340784934590445

theorem tailTrace_2312406 : CollatzResearch.WordTrace tailWord_2312406 prefixEnd_2312406 1187375746340784934590445 := by
  unfold tailWord_2312406
  simp only [CollatzResearch.WordTrace]
  refine ⟨5271273478784716521757817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 56226917107036976232083381 5271273478784716521757817)
  ·
    refine ⟨3953455109088537391318363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5271273478784716521757817 3953455109088537391318363)
    ·
      refine ⟨5930182663632806086977545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3953455109088537391318363 5930182663632806086977545)
      ·
        refine ⟨4447636997724604565233159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5930182663632806086977545 4447636997724604565233159)
        ·
          refine ⟨6671455496586906847849739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4447636997724604565233159 6671455496586906847849739)
          ·
            refine ⟨10007183244880360271774609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6671455496586906847849739 10007183244880360271774609)
            ·
              refine ⟨7505387433660270203830957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10007183244880360271774609 7505387433660270203830957)
              ·
                refine ⟨2814520287622601326436609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7505387433660270203830957 2814520287622601326436609)
                ·
                  refine ⟨2110890215716950994827457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2814520287622601326436609 2110890215716950994827457)
                  ·
                    refine ⟨1583167661787713246120593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2110890215716950994827457 1583167661787713246120593)
                    ·
                      refine ⟨1187375746340784934590445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1583167661787713246120593 1187375746340784934590445)
                      ·
                        rfl

theorem cell23_2312406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 2, 3, 2, 2, 2].length) (baseStart_2312406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2312406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2312406 prefixEnd_2312406 := by exact prefixLift 2312406
  have htrace : WordTrace (prefixWord ++ tailWord_2312406) baseStart_2312406 baseEnd_2312406 := by
    simpa [prefixWord, tailWord_2312406, baseEnd_2312406] using wordTrace_append hprefix tailTrace_2312406
  have hstable : (prefixWord ++ tailWord_2312406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2312406).length < 2 ^ (prefixWord ++ tailWord_2312406).sum := by decide
  have hdescent : baseEnd_2312406 < baseStart_2312406 := by decide
  rcases family_descends (prefixWord ++ tailWord_2312406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2312412 : List Nat := [2, 2, 5, 2, 1, 1, 1, 2, 7]
def baseStart_2312412 : Nat := 118140960795 + 2312412 * 2 ^ 59
def prefixEnd_2312412 : Nat := 4983230072969 + 3 ^ 40 * 2312412 * 2
def baseEnd_2312412 : Nat := 131930980802745767901713

theorem tailTrace_2312412 : CollatzResearch.WordTrace tailWord_2312412 prefixEnd_2312412 131930980802745767901713 := by
  unfold tailWord_2312412
  simp only [CollatzResearch.WordTrace]
  refine ⟨42170297249266863686421745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56227062999022484915228993 42170297249266863686421745)
  ·
    refine ⟨31627722936950147764816309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42170297249266863686421745 31627722936950147764816309)
    ·
      refine ⟨2965099025339076352951529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 31627722936950147764816309 2965099025339076352951529)
      ·
        refine ⟨2223824269004307264713647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2965099025339076352951529 2223824269004307264713647)
        ·
          refine ⟨3335736403506460897070471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2223824269004307264713647 3335736403506460897070471)
          ·
            refine ⟨5003604605259691345605707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3335736403506460897070471 5003604605259691345605707)
            ·
              refine ⟨7505406907889537018408561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5003604605259691345605707 7505406907889537018408561)
              ·
                refine ⟨5629055180917152763806421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7505406907889537018408561 5629055180917152763806421)
                ·
                  refine ⟨131930980802745767901713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5629055180917152763806421 131930980802745767901713)
                  ·
                    rfl

theorem cell23_2312412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 1, 2, 7].length) (baseStart_2312412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2312412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2312412 prefixEnd_2312412 := by exact prefixLift 2312412
  have htrace : WordTrace (prefixWord ++ tailWord_2312412) baseStart_2312412 baseEnd_2312412 := by
    simpa [prefixWord, tailWord_2312412, baseEnd_2312412] using wordTrace_append hprefix tailTrace_2312412
  have hstable : (prefixWord ++ tailWord_2312412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2312412).length < 2 ^ (prefixWord ++ tailWord_2312412).sum := by decide
  have hdescent : baseEnd_2312412 < baseStart_2312412 := by decide
  rcases family_descends (prefixWord ++ tailWord_2312412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2312428 : List Nat := [2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 4]
def baseStart_2312428 : Nat := 118140960795 + 2312428 * 2 ^ 59
def prefixEnd_2312428 : Nat := 4983230072969 + 3 ^ 40 * 2312428 * 2
def baseEnd_2312428 : Nat := 1187387042915183848515343

theorem tailTrace_2312428 : CollatzResearch.WordTrace tailWord_2312428 prefixEnd_2312428 1187387042915183848515343 := by
  unfold tailWord_2312428
  simp only [CollatzResearch.WordTrace]
  refine ⟨42170589033237881052712969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56227452044317174736950625 42170589033237881052712969)
  ·
    refine ⟨31627941774928410789534727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42170589033237881052712969 31627941774928410789534727)
    ·
      refine ⟨47441912662392616184302091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31627941774928410789534727 47441912662392616184302091)
      ·
        refine ⟨71162868993588924276453137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47441912662392616184302091 71162868993588924276453137)
        ·
          refine ⟨53372151745191693207339853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71162868993588924276453137 53372151745191693207339853)
          ·
            refine ⟨20014556904446884952752445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53372151745191693207339853 20014556904446884952752445)
            ·
              refine ⟨7505458839167581857282167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20014556904446884952752445 7505458839167581857282167)
              ·
                refine ⟨11258188258751372785923251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7505458839167581857282167 11258188258751372785923251)
                ·
                  refine ⟨16887282388127059178884877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11258188258751372785923251 16887282388127059178884877)
                  ·
                    refine ⟨6332730895547647192081829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16887282388127059178884877 6332730895547647192081829)
                    ·
                      refine ⟨1187387042915183848515343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6332730895547647192081829 1187387042915183848515343)
                      ·
                        rfl

theorem cell23_2312428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 4].length) (baseStart_2312428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2312428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2312428 prefixEnd_2312428 := by exact prefixLift 2312428
  have htrace : WordTrace (prefixWord ++ tailWord_2312428) baseStart_2312428 baseEnd_2312428 := by
    simpa [prefixWord, tailWord_2312428, baseEnd_2312428] using wordTrace_append hprefix tailTrace_2312428
  have hstable : (prefixWord ++ tailWord_2312428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2312428).length < 2 ^ (prefixWord ++ tailWord_2312428).sum := by decide
  have hdescent : baseEnd_2312428 < baseStart_2312428 := by decide
  rcases family_descends (prefixWord ++ tailWord_2312428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2312495 : List Nat := [1, 1, 2, 1, 2, 1, 4, 2, 5, 1, 3]
def baseStart_2312495 : Nat := 118140960795 + 2312495 * 2 ^ 59
def prefixEnd_2312495 : Nat := 4983230072969 + 3 ^ 40 * 2312495 * 2
def baseEnd_2312495 : Nat := 1187421446119035086377535

theorem tailTrace_2312495 : CollatzResearch.WordTrace tailWord_2312495 prefixEnd_2312495 1187421446119035086377535 := by
  unfold tailWord_2312495
  simp only [CollatzResearch.WordTrace]
  refine ⟨84343621757233032548114939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56229081171488688365409959 84343621757233032548114939)
  ·
    refine ⟨126515432635849548822172409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84343621757233032548114939 126515432635849548822172409)
    ·
      refine ⟨94886574476887161616629307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126515432635849548822172409 94886574476887161616629307)
      ·
        refine ⟨142329861715330742424943961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94886574476887161616629307 142329861715330742424943961)
        ·
          refine ⟨106747396286498056818707971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 142329861715330742424943961 106747396286498056818707971)
          ·
            refine ⟨160121094429747085228061957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106747396286498056818707971 160121094429747085228061957)
            ·
              refine ⟨30022705205577578480261617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 160121094429747085228061957 30022705205577578480261617)
              ·
                refine ⟨22517028904183183860196213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30022705205577578480261617 22517028904183183860196213)
                ·
                  refine ⟨2110971459767173486893395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 22517028904183183860196213 2110971459767173486893395)
                  ·
                    refine ⟨3166457189650760230340093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2110971459767173486893395 3166457189650760230340093)
                    ·
                      refine ⟨1187421446119035086377535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3166457189650760230340093 1187421446119035086377535)
                      ·
                        rfl

theorem cell23_2312495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 2, 5, 1, 3].length) (baseStart_2312495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2312495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2312495 prefixEnd_2312495 := by exact prefixLift 2312495
  have htrace : WordTrace (prefixWord ++ tailWord_2312495) baseStart_2312495 baseEnd_2312495 := by
    simpa [prefixWord, tailWord_2312495, baseEnd_2312495] using wordTrace_append hprefix tailTrace_2312495
  have hstable : (prefixWord ++ tailWord_2312495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2312495).length < 2 ^ (prefixWord ++ tailWord_2312495).sum := by decide
  have hdescent : baseEnd_2312495 < baseStart_2312495 := by decide
  rcases family_descends (prefixWord ++ tailWord_2312495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2312532 : List Nat := [2, 4, 1, 1, 2, 2, 3, 2, 1, 5]
def baseStart_2312532 : Nat := 118140960795 + 2312532 * 2 ^ 59
def prefixEnd_2312532 : Nat := 4983230072969 + 3 ^ 40 * 2312532 * 2
def baseEnd_2312532 : Nat := 395813481634417147204955

theorem tailTrace_2312532 : CollatzResearch.WordTrace tailWord_2312532 prefixEnd_2312532 395813481634417147204955 := by
  unfold tailWord_2312532
  simp only [CollatzResearch.WordTrace]
  refine ⟨42172485629049493933605925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56229980838732658578141233 42172485629049493933605925)
  ·
    refine ⟨7907341055446780112551111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42172485629049493933605925 7907341055446780112551111)
    ·
      refine ⟨11861011583170170168826667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7907341055446780112551111 11861011583170170168826667)
      ·
        refine ⟨17791517374755255253240001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11861011583170170168826667 17791517374755255253240001)
        ·
          refine ⟨13343638031066441439930001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17791517374755255253240001 13343638031066441439930001)
          ·
            refine ⟨10007728523299831079947501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13343638031066441439930001 10007728523299831079947501)
            ·
              refine ⟨3752898196237436654980313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10007728523299831079947501 3752898196237436654980313)
              ·
                refine ⟨2814673647178077491235235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3752898196237436654980313 2814673647178077491235235)
                ·
                  refine ⟨4222010470767116236852853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2814673647178077491235235 4222010470767116236852853)
                  ·
                    refine ⟨395813481634417147204955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4222010470767116236852853 395813481634417147204955)
                    ·
                      rfl

theorem cell23_2312532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 3, 2, 1, 5].length) (baseStart_2312532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2312532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2312532 prefixEnd_2312532 := by exact prefixLift 2312532
  have htrace : WordTrace (prefixWord ++ tailWord_2312532) baseStart_2312532 baseEnd_2312532 := by
    simpa [prefixWord, tailWord_2312532, baseEnd_2312532] using wordTrace_append hprefix tailTrace_2312532
  have hstable : (prefixWord ++ tailWord_2312532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2312532).length < 2 ^ (prefixWord ++ tailWord_2312532).sum := by decide
  have hdescent : baseEnd_2312532 < baseStart_2312532 := by decide
  rcases family_descends (prefixWord ++ tailWord_2312532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2312535 : List Nat := [1, 1, 3, 2, 3, 1, 3, 1, 3, 1, 4]
def baseStart_2312535 : Nat := 118140960795 + 2312535 * 2 ^ 59
def prefixEnd_2312535 : Nat := 4983230072969 + 3 ^ 40 * 2312535 * 2
def baseEnd_2312535 : Nat := 1187441985345214929877351

theorem tailTrace_2312535 : CollatzResearch.WordTrace tailWord_2312535 prefixEnd_2312535 1187441985345214929877351 := by
  unfold tailWord_2312535
  simp only [CollatzResearch.WordTrace]
  refine ⟨84345080677088119379571059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56230053784725412919714039 84345080677088119379571059)
  ·
    refine ⟨126517621015632179069356589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84345080677088119379571059 126517621015632179069356589)
    ·
      refine ⟨47444107880862067151008721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 126517621015632179069356589 47444107880862067151008721)
      ·
        refine ⟨35583080910646550363256541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47444107880862067151008721 35583080910646550363256541)
        ·
          refine ⟨13343655341492456386221203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35583080910646550363256541 13343655341492456386221203)
          ·
            refine ⟨20015483012238684579331805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13343655341492456386221203 20015483012238684579331805)
            ·
              refine ⟨7505806129589506717249427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20015483012238684579331805 7505806129589506717249427)
              ·
                refine ⟨11258709194384260075874141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7505806129589506717249427 11258709194384260075874141)
                ·
                  refine ⟨4222015947894097528452803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11258709194384260075874141 4222015947894097528452803)
                  ·
                    refine ⟨6333023921841146292679205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4222015947894097528452803 6333023921841146292679205)
                    ·
                      refine ⟨1187441985345214929877351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6333023921841146292679205 1187441985345214929877351)
                      ·
                        rfl

theorem cell23_2312535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 3, 1, 3, 1, 4].length) (baseStart_2312535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2312535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2312535 prefixEnd_2312535 := by exact prefixLift 2312535
  have htrace : WordTrace (prefixWord ++ tailWord_2312535) baseStart_2312535 baseEnd_2312535 := by
    simpa [prefixWord, tailWord_2312535, baseEnd_2312535] using wordTrace_append hprefix tailTrace_2312535
  have hstable : (prefixWord ++ tailWord_2312535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2312535).length < 2 ^ (prefixWord ++ tailWord_2312535).sum := by decide
  have hdescent : baseEnd_2312535 < baseStart_2312535 := by decide
  rcases family_descends (prefixWord ++ tailWord_2312535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2312558 : List Nat := [4, 1, 2, 16]
def baseStart_2312558 : Nat := 118140960795 + 2312558 * 2 ^ 59
def prefixEnd_2312558 : Nat := 4983230072969 + 3 ^ 40 * 2312558 * 2
def baseEnd_2312558 : Nat := 542960125926048623635

theorem tailTrace_2312558 : CollatzResearch.WordTrace tailWord_2312558 prefixEnd_2312558 542960125926048623635 := by
  unfold tailWord_2312558
  simp only [CollatzResearch.WordTrace]
  refine ⟨10543239944500599288457291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56230613037336529538438885 10543239944500599288457291)
  ·
    refine ⟨15814859916750898932685937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10543239944500599288457291 15814859916750898932685937)
    ·
      refine ⟨11861144937563174199514453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15814859916750898932685937 11861144937563174199514453)
      ·
        refine ⟨542960125926048623635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 16 11861144937563174199514453 542960125926048623635)
        ·
          rfl

theorem cell23_2312558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 16].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 16].length) (baseStart_2312558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2312558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2312558 prefixEnd_2312558 := by exact prefixLift 2312558
  have htrace : WordTrace (prefixWord ++ tailWord_2312558) baseStart_2312558 baseEnd_2312558 := by
    simpa [prefixWord, tailWord_2312558, baseEnd_2312558] using wordTrace_append hprefix tailTrace_2312558
  have hstable : (prefixWord ++ tailWord_2312558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2312558).length < 2 ^ (prefixWord ++ tailWord_2312558).sum := by decide
  have hdescent : baseEnd_2312558 < baseStart_2312558 := by decide
  rcases family_descends (prefixWord ++ tailWord_2312558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2312562 : List Nat := [3, 2, 1, 2, 1, 3, 1, 4, 2, 4]
def baseStart_2312562 : Nat := 118140960795 + 2312562 * 2 ^ 59
def prefixEnd_2312562 : Nat := 4983230072969 + 3 ^ 40 * 2312562 * 2
def baseEnd_2312562 : Nat := 395818616440962108079909

theorem tailTrace_2312562 : CollatzResearch.WordTrace tailWord_2312562 prefixEnd_2312562 395818616440962108079909 := by
  unfold tailWord_2312562
  simp only [CollatzResearch.WordTrace]
  refine ⟨21086516361997575747700985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56230710298660201993869293 21086516361997575747700985)
  ·
    refine ⟨15814887271498181810775739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21086516361997575747700985 15814887271498181810775739)
    ·
      refine ⟨23722330907247272716163609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15814887271498181810775739 23722330907247272716163609)
      ·
        refine ⟨17791748180435454537122707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23722330907247272716163609 17791748180435454537122707)
        ·
          refine ⟨26687622270653181805684061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17791748180435454537122707 26687622270653181805684061)
          ·
            refine ⟨10007858351494943177131523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26687622270653181805684061 10007858351494943177131523)
            ·
              refine ⟨15011787527242414765697285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10007858351494943177131523 15011787527242414765697285)
              ·
                refine ⟨2814710161357952768568241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15011787527242414765697285 2814710161357952768568241)
                ·
                  refine ⟨2111032621018464576426181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2814710161357952768568241 2111032621018464576426181)
                  ·
                    refine ⟨395818616440962108079909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2111032621018464576426181 395818616440962108079909)
                    ·
                      rfl

theorem cell23_2312562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 4, 2, 4].length) (baseStart_2312562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2312562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2312562 prefixEnd_2312562 := by exact prefixLift 2312562
  have htrace : WordTrace (prefixWord ++ tailWord_2312562) baseStart_2312562 baseEnd_2312562 := by
    simpa [prefixWord, tailWord_2312562, baseEnd_2312562] using wordTrace_append hprefix tailTrace_2312562
  have hstable : (prefixWord ++ tailWord_2312562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2312562).length < 2 ^ (prefixWord ++ tailWord_2312562).sum := by decide
  have hdescent : baseEnd_2312562 < baseStart_2312562 := by decide
  rcases family_descends (prefixWord ++ tailWord_2312562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2312602 : List Nat := [3, 1, 1, 4, 1, 2, 2, 2, 1, 3, 3]
def baseStart_2312602 : Nat := 118140960795 + 2312602 * 2 ^ 59
def prefixEnd_2312602 : Nat := 4983230072969 + 3 ^ 40 * 2312602 * 2
def baseEnd_2312602 : Nat := 1187476388549066167739543

theorem tailTrace_2312602 : CollatzResearch.WordTrace tailWord_2312602 prefixEnd_2312602 1187476388549066167739543 := by
  unfold tailWord_2312602
  simp only [CollatzResearch.WordTrace]
  refine ⟨21086881091961347455565015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56231682911896926548173373 21086881091961347455565015)
  ·
    refine ⟨31630321637942021183347523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21086881091961347455565015 31630321637942021183347523)
    ·
      refine ⟨47445482456913031775021285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31630321637942021183347523 47445482456913031775021285)
      ·
        refine ⟨8896027960671193457816491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47445482456913031775021285 8896027960671193457816491)
        ·
          refine ⟨13344041941006790186724737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8896027960671193457816491 13344041941006790186724737)
          ·
            refine ⟨10008031455755092640043553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13344041941006790186724737 10008031455755092640043553)
            ·
              refine ⟨7506023591816319480032665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10008031455755092640043553 7506023591816319480032665)
              ·
                refine ⟨5629517693862239610024499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7506023591816319480032665 5629517693862239610024499)
                ·
                  refine ⟨8444276540793359415036749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5629517693862239610024499 8444276540793359415036749)
                  ·
                    refine ⟨3166603702797509780638781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8444276540793359415036749 3166603702797509780638781)
                    ·
                      refine ⟨1187476388549066167739543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3166603702797509780638781 1187476388549066167739543)
                      ·
                        rfl

theorem cell23_2312602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 2, 2, 1, 3, 3].length) (baseStart_2312602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2312602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2312602 prefixEnd_2312602 := by exact prefixLift 2312602
  have htrace : WordTrace (prefixWord ++ tailWord_2312602) baseStart_2312602 baseEnd_2312602 := by
    simpa [prefixWord, tailWord_2312602, baseEnd_2312602] using wordTrace_append hprefix tailTrace_2312602
  have hstable : (prefixWord ++ tailWord_2312602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2312602).length < 2 ^ (prefixWord ++ tailWord_2312602).sum := by decide
  have hdescent : baseEnd_2312602 < baseStart_2312602 := by decide
  rcases family_descends (prefixWord ++ tailWord_2312602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2312606 : List Nat := [4, 3, 1, 2, 1, 2, 1, 3, 1, 2, 3]
def baseStart_2312606 : Nat := 118140960795 + 2312606 * 2 ^ 59
def prefixEnd_2312606 : Nat := 4983230072969 + 3 ^ 40 * 2312606 * 2
def baseEnd_2312606 : Nat := 1187478442471684152089525

theorem tailTrace_2312606 : CollatzResearch.WordTrace tailWord_2312606 prefixEnd_2312606 1187478442471684152089525 := by
  unfold tailWord_2312606
  simp only [CollatzResearch.WordTrace]
  refine ⟨10543458782478862313175709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56231780173220599003603781 10543458782478862313175709)
  ·
    refine ⟨3953797043429573367440891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10543458782478862313175709 3953797043429573367440891)
    ·
      refine ⟨5930695565144360051161337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3953797043429573367440891 5930695565144360051161337)
      ·
        refine ⟨4448021673858270038371003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5930695565144360051161337 4448021673858270038371003)
        ·
          refine ⟨6672032510787405057556505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4448021673858270038371003 6672032510787405057556505)
          ·
            refine ⟨5004024383090553793167379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6672032510787405057556505 5004024383090553793167379)
            ·
              refine ⟨7506036574635830689751069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5004024383090553793167379 7506036574635830689751069)
              ·
                refine ⟨2814763715488436508656651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7506036574635830689751069 2814763715488436508656651)
                ·
                  refine ⟨4222145573232654762984977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2814763715488436508656651 4222145573232654762984977)
                  ·
                    refine ⟨3166609179924491072238733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4222145573232654762984977 3166609179924491072238733)
                    ·
                      refine ⟨1187478442471684152089525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3166609179924491072238733 1187478442471684152089525)
                      ·
                        rfl

theorem cell23_2312606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 1, 3, 1, 2, 3].length) (baseStart_2312606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2312606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2312606 prefixEnd_2312606 := by exact prefixLift 2312606
  have htrace : WordTrace (prefixWord ++ tailWord_2312606) baseStart_2312606 baseEnd_2312606 := by
    simpa [prefixWord, tailWord_2312606, baseEnd_2312606] using wordTrace_append hprefix tailTrace_2312606
  have hstable : (prefixWord ++ tailWord_2312606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2312606).length < 2 ^ (prefixWord ++ tailWord_2312606).sum := by decide
  have hdescent : baseEnd_2312606 < baseStart_2312606 := by decide
  rcases family_descends (prefixWord ++ tailWord_2312606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2312682 : List Nat := [3, 1, 3, 1, 3, 1, 3, 1, 7]
def baseStart_2312682 : Nat := 118140960795 + 2312682 * 2 ^ 59
def prefixEnd_2312682 : Nat := 4983230072969 + 3 ^ 40 * 2312682 * 2
def baseEnd_2312682 : Nat := 131946385222380650526575

theorem tailTrace_2312682 : CollatzResearch.WordTrace tailWord_2312682 prefixEnd_2312682 131946385222380650526575 := by
  unfold tailWord_2312682
  simp only [CollatzResearch.WordTrace]
  refine ⟨21087610551888890871293075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56233628138370375656781533 21087610551888890871293075)
  ·
    refine ⟨31631415827833336306939613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21087610551888890871293075 31631415827833336306939613)
    ·
      refine ⟨11861780935437501115102355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31631415827833336306939613 11861780935437501115102355)
      ·
        refine ⟨17792671403156251672653533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11861780935437501115102355 17792671403156251672653533)
        ·
          refine ⟨6672251776183594377245075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17792671403156251672653533 6672251776183594377245075)
          ·
            refine ⟨10008377664275391565867613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6672251776183594377245075 10008377664275391565867613)
            ·
              refine ⟨3753141624103271837200355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10008377664275391565867613 3753141624103271837200355)
              ·
                refine ⟨5629712436154907755800533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3753141624103271837200355 5629712436154907755800533)
                ·
                  refine ⟨131946385222380650526575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5629712436154907755800533 131946385222380650526575)
                  ·
                    rfl

theorem cell23_2312682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 3, 1, 7].length) (baseStart_2312682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2312682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2312682 prefixEnd_2312682 := by exact prefixLift 2312682
  have htrace : WordTrace (prefixWord ++ tailWord_2312682) baseStart_2312682 baseEnd_2312682 := by
    simpa [prefixWord, tailWord_2312682, baseEnd_2312682] using wordTrace_append hprefix tailTrace_2312682
  have hstable : (prefixWord ++ tailWord_2312682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2312682).length < 2 ^ (prefixWord ++ tailWord_2312682).sum := by decide
  have hdescent : baseEnd_2312682 < baseStart_2312682 := by decide
  rcases family_descends (prefixWord ++ tailWord_2312682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2312710 : List Nat := [6, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2]
def baseStart_2312710 : Nat := 118140960795 + 2312710 * 2 ^ 59
def prefixEnd_2312710 : Nat := 4983230072969 + 3 ^ 40 * 2312710 * 2
def baseEnd_2312710 : Nat := 1187531844459751745189047

theorem tailTrace_2312710 : CollatzResearch.WordTrace tailWord_2312710 prefixEnd_2312710 1187531844459751745189047 := by
  unfold tailWord_2312710
  simp only [CollatzResearch.WordTrace]
  refine ⟨2635983232857941383349737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 56234308967636082844794389 2635983232857941383349737)
  ·
    refine ⟨1976987424643456037512303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2635983232857941383349737 1976987424643456037512303)
    ·
      refine ⟨2965481136965184056268455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1976987424643456037512303 2965481136965184056268455)
      ·
        refine ⟨4448221705447776084402683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2965481136965184056268455 4448221705447776084402683)
        ·
          refine ⟨6672332558171664126604025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4448221705447776084402683 6672332558171664126604025)
          ·
            refine ⟨5004249418628748094953019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6672332558171664126604025 5004249418628748094953019)
            ·
              refine ⟨7506374127943122142429529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5004249418628748094953019 7506374127943122142429529)
              ·
                refine ⟨5629780595957341606822147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7506374127943122142429529 5629780595957341606822147)
                ·
                  refine ⟨8444670893936012410233221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5629780595957341606822147 8444670893936012410233221)
                  ·
                    refine ⟨1583375792613002326918729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8444670893936012410233221 1583375792613002326918729)
                    ·
                      refine ⟨1187531844459751745189047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1583375792613002326918729 1187531844459751745189047)
                      ·
                        rfl

theorem cell23_2312710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2].length) (baseStart_2312710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2312710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2312710 prefixEnd_2312710 := by exact prefixLift 2312710
  have htrace : WordTrace (prefixWord ++ tailWord_2312710) baseStart_2312710 baseEnd_2312710 := by
    simpa [prefixWord, tailWord_2312710, baseEnd_2312710] using wordTrace_append hprefix tailTrace_2312710
  have hstable : (prefixWord ++ tailWord_2312710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2312710).length < 2 ^ (prefixWord ++ tailWord_2312710).sum := by decide
  have hdescent : baseEnd_2312710 < baseStart_2312710 := by decide
  rcases family_descends (prefixWord ++ tailWord_2312710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2312735 : List Nat := [1, 1, 2, 4, 1, 1, 1, 1, 1, 5, 5]
def baseStart_2312735 : Nat := 118140960795 + 2312735 * 2 ^ 59
def prefixEnd_2312735 : Nat := 4983230072969 + 3 ^ 40 * 2312735 * 2
def baseEnd_2312735 : Nat := 1187544681476114147376431

theorem tailTrace_2312735 : CollatzResearch.WordTrace tailWord_2312735 prefixEnd_2312735 1187544681476114147376431 := by
  unfold tailWord_2312735
  simp only [CollatzResearch.WordTrace]
  refine ⟨84352375276363553536851659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56234916850909035691234439 84352375276363553536851659)
  ·
    refine ⟨126528562914545330305277489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84352375276363553536851659 126528562914545330305277489)
    ·
      refine ⟨94896422185908997728958117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126528562914545330305277489 94896422185908997728958117)
      ·
        refine ⟨17793079159857937074179647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 94896422185908997728958117 17793079159857937074179647)
        ·
          refine ⟨26689618739786905611269471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17793079159857937074179647 26689618739786905611269471)
          ·
            refine ⟨40034428109680358416904207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26689618739786905611269471 40034428109680358416904207)
            ·
              refine ⟨60051642164520537625356311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40034428109680358416904207 60051642164520537625356311)
              ·
                refine ⟨90077463246780806438034467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60051642164520537625356311 90077463246780806438034467)
                ·
                  refine ⟨135116194870171209657051701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 90077463246780806438034467 135116194870171209657051701)
                  ·
                    refine ⟨12667143269078550905348597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 135116194870171209657051701 12667143269078550905348597)
                    ·
                      refine ⟨1187544681476114147376431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12667143269078550905348597 1187544681476114147376431)
                      ·
                        rfl

theorem cell23_2312735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 1, 1, 5, 5].length) (baseStart_2312735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2312735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2312735 prefixEnd_2312735 := by exact prefixLift 2312735
  have htrace : WordTrace (prefixWord ++ tailWord_2312735) baseStart_2312735 baseEnd_2312735 := by
    simpa [prefixWord, tailWord_2312735, baseEnd_2312735] using wordTrace_append hprefix tailTrace_2312735
  have hstable : (prefixWord ++ tailWord_2312735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2312735).length < 2 ^ (prefixWord ++ tailWord_2312735).sum := by decide
  have hdescent : baseEnd_2312735 < baseStart_2312735 := by decide
  rcases family_descends (prefixWord ++ tailWord_2312735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2312752 : List Nat := [2, 1, 1, 1, 2, 3, 2, 2, 4, 2, 3]
def baseStart_2312752 : Nat := 118140960795 + 2312752 * 2 ^ 59
def prefixEnd_2312752 : Nat := 4983230072969 + 3 ^ 40 * 2312752 * 2
def baseEnd_2312752 : Nat := 1187553410647240580863853

theorem tailTrace_2312752 : CollatzResearch.WordTrace tailWord_2312752 prefixEnd_2312752 1187553410647240580863853 := by
  unfold tailWord_2312752
  simp only [CollatzResearch.WordTrace]
  refine ⟨42176497658650982720110255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56235330211534643626813673 42176497658650982720110255)
  ·
    refine ⟨63264746487976474080165383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42176497658650982720110255 63264746487976474080165383)
    ·
      refine ⟨94897119731964711120248075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63264746487976474080165383 94897119731964711120248075)
      ·
        refine ⟨142345679597947066680372113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94897119731964711120248075 142345679597947066680372113)
        ·
          refine ⟨106759259698460300010279085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 142345679597947066680372113 106759259698460300010279085)
          ·
            refine ⟨40034722386922612503854657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 106759259698460300010279085 40034722386922612503854657)
            ·
              refine ⟨30026041790191959377890993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40034722386922612503854657 30026041790191959377890993)
              ·
                refine ⟨22519531342643969533418245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30026041790191959377890993 22519531342643969533418245)
                ·
                  refine ⟨4222412126745744287515921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22519531342643969533418245 4222412126745744287515921)
                  ·
                    refine ⟨3166809095059308215636941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4222412126745744287515921 3166809095059308215636941)
                    ·
                      refine ⟨1187553410647240580863853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3166809095059308215636941 1187553410647240580863853)
                      ·
                        rfl

theorem cell23_2312752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 2, 4, 2, 3].length) (baseStart_2312752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2312752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2312752 prefixEnd_2312752 := by exact prefixLift 2312752
  have htrace : WordTrace (prefixWord ++ tailWord_2312752) baseStart_2312752 baseEnd_2312752 := by
    simpa [prefixWord, tailWord_2312752, baseEnd_2312752] using wordTrace_append hprefix tailTrace_2312752
  have hstable : (prefixWord ++ tailWord_2312752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2312752).length < 2 ^ (prefixWord ++ tailWord_2312752).sum := by decide
  have hdescent : baseEnd_2312752 < baseStart_2312752 := by decide
  rcases family_descends (prefixWord ++ tailWord_2312752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2312766 : List Nat := [4, 2, 1, 4, 1, 1, 1, 1, 1, 3, 4]
def baseStart_2312766 : Nat := 118140960795 + 2312766 * 2 ^ 59
def prefixEnd_2312766 : Nat := 4983230072969 + 3 ^ 40 * 2312766 * 2
def baseEnd_2312766 : Nat := 1187560599376403526088789

theorem tailTrace_2312766 : CollatzResearch.WordTrace tailWord_2312766 prefixEnd_2312766 1187560599376403526088789 := by
  unfold tailWord_2312766
  simp only [CollatzResearch.WordTrace]
  refine ⟨10544188242406405728903769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56235670626167497220820101 10544188242406405728903769)
  ·
    refine ⟨7908141181804804296677827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10544188242406405728903769 7908141181804804296677827)
    ·
      refine ⟨11862211772707206445016741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7908141181804804296677827 11862211772707206445016741)
      ·
        refine ⟨2224164707382601208440639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11862211772707206445016741 2224164707382601208440639)
        ·
          refine ⟨3336247061073901812660959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2224164707382601208440639 3336247061073901812660959)
          ·
            refine ⟨5004370591610852718991439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3336247061073901812660959 5004370591610852718991439)
            ·
              refine ⟨7506555887416279078487159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5004370591610852718991439 7506555887416279078487159)
              ·
                refine ⟨11259833831124418617730739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7506555887416279078487159 11259833831124418617730739)
                ·
                  refine ⟨16889750746686627926596109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11259833831124418617730739 16889750746686627926596109)
                  ·
                    refine ⟨6333656530007485472473541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16889750746686627926596109 6333656530007485472473541)
                    ·
                      refine ⟨1187560599376403526088789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6333656530007485472473541 1187560599376403526088789)
                      ·
                        rfl

theorem cell23_2312766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 1, 1, 1, 3, 4].length) (baseStart_2312766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2312766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2312766 prefixEnd_2312766 := by exact prefixLift 2312766
  have htrace : WordTrace (prefixWord ++ tailWord_2312766) baseStart_2312766 baseEnd_2312766 := by
    simpa [prefixWord, tailWord_2312766, baseEnd_2312766] using wordTrace_append hprefix tailTrace_2312766
  have hstable : (prefixWord ++ tailWord_2312766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2312766).length < 2 ^ (prefixWord ++ tailWord_2312766).sum := by decide
  have hdescent : baseEnd_2312766 < baseStart_2312766 := by decide
  rcases family_descends (prefixWord ++ tailWord_2312766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2312769 : List Nat := [1, 2, 5, 1, 1, 3, 1, 1, 1, 4, 3]
def baseStart_2312769 : Nat := 118140960795 + 2312769 * 2 ^ 59
def prefixEnd_2312769 : Nat := 4983230072969 + 3 ^ 40 * 2312769 * 2
def baseEnd_2312769 : Nat := 1187562139818367014351275

theorem tailTrace_2312769 : CollatzResearch.WordTrace tailWord_2312769 prefixEnd_2312769 1187562139818367014351275 := by
  unfold tailWord_2312769
  simp only [CollatzResearch.WordTrace]
  refine ⟨84353615358240377343589361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56235743572160251562392907 84353615358240377343589361)
  ·
    refine ⟨63265211518680283007692021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84353615358240377343589361 63265211518680283007692021)
    ·
      refine ⟨5931113579876276531971127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 63265211518680283007692021 5931113579876276531971127)
      ·
        refine ⟨8896670369814414797956691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5931113579876276531971127 8896670369814414797956691)
        ·
          refine ⟨13345005554721622196935037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8896670369814414797956691 13345005554721622196935037)
          ·
            refine ⟨5004377083020608323850639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13345005554721622196935037 5004377083020608323850639)
            ·
              refine ⟨7506565624530912485775959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5004377083020608323850639 7506565624530912485775959)
              ·
                refine ⟨11259848436796368728663939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7506565624530912485775959 11259848436796368728663939)
                ·
                  refine ⟨16889772655194553092995909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11259848436796368728663939 16889772655194553092995909)
                  ·
                    refine ⟨3166832372848978704936733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16889772655194553092995909 3166832372848978704936733)
                    ·
                      refine ⟨1187562139818367014351275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3166832372848978704936733 1187562139818367014351275)
                      ·
                        rfl

theorem cell23_2312769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 1, 1, 1, 4, 3].length) (baseStart_2312769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2312769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2312769 prefixEnd_2312769 := by exact prefixLift 2312769
  have htrace : WordTrace (prefixWord ++ tailWord_2312769) baseStart_2312769 baseEnd_2312769 := by
    simpa [prefixWord, tailWord_2312769, baseEnd_2312769] using wordTrace_append hprefix tailTrace_2312769
  have hstable : (prefixWord ++ tailWord_2312769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2312769).length < 2 ^ (prefixWord ++ tailWord_2312769).sum := by decide
  have hdescent : baseEnd_2312769 < baseStart_2312769 := by decide
  rcases family_descends (prefixWord ++ tailWord_2312769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2312839 : List Nat := [1, 1, 4, 2, 1, 2, 1, 5, 1, 1, 4]
def baseStart_2312839 : Nat := 118140960795 + 2312839 * 2 ^ 59
def prefixEnd_2312839 : Nat := 4983230072969 + 3 ^ 40 * 2312839 * 2
def baseEnd_2312839 : Nat := 1187598083464181740475953

theorem tailTrace_2312839 : CollatzResearch.WordTrace tailWord_2312839 prefixEnd_2312839 1187598083464181740475953 := by
  unfold tailWord_2312839
  simp only [CollatzResearch.WordTrace]
  refine ⟨84356168467986779298637571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56237445645324519532425047 84356168467986779298637571)
  ·
    refine ⟨126534252701980168947956357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84356168467986779298637571 126534252701980168947956357)
    ·
      refine ⟨23725172381621281677741817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 126534252701980168947956357 23725172381621281677741817)
      ·
        refine ⟨17793879286215961258306363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23725172381621281677741817 17793879286215961258306363)
        ·
          refine ⟨26690818929323941887459545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17793879286215961258306363 26690818929323941887459545)
          ·
            refine ⟨20018114196992956415594659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26690818929323941887459545 20018114196992956415594659)
            ·
              refine ⟨30027171295489434623391989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20018114196992956415594659 30027171295489434623391989)
              ·
                refine ⟨2815047308952134495942999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30027171295489434623391989 2815047308952134495942999)
                ·
                  refine ⟨4222570963428201743914499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2815047308952134495942999 4222570963428201743914499)
                  ·
                    refine ⟨6333856445142302615871749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4222570963428201743914499 6333856445142302615871749)
                    ·
                      refine ⟨1187598083464181740475953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6333856445142302615871749 1187598083464181740475953)
                      ·
                        rfl

theorem cell23_2312839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 5, 1, 1, 4].length) (baseStart_2312839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2312839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2312839 prefixEnd_2312839 := by exact prefixLift 2312839
  have htrace : WordTrace (prefixWord ++ tailWord_2312839) baseStart_2312839 baseEnd_2312839 := by
    simpa [prefixWord, tailWord_2312839, baseEnd_2312839] using wordTrace_append hprefix tailTrace_2312839
  have hstable : (prefixWord ++ tailWord_2312839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2312839).length < 2 ^ (prefixWord ++ tailWord_2312839).sum := by decide
  have hdescent : baseEnd_2312839 < baseStart_2312839 := by decide
  rcases family_descends (prefixWord ++ tailWord_2312839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2312893 : List Nat := [1, 4, 1, 2, 1, 4, 3, 1, 1, 2, 3]
def baseStart_2312893 : Nat := 118140960795 + 2312893 * 2 ^ 59
def prefixEnd_2312893 : Nat := 4983230072969 + 3 ^ 40 * 2312893 * 2
def baseEnd_2312893 : Nat := 1187625811419524529200705

theorem tailTrace_2312893 : CollatzResearch.WordTrace tailWord_2312893 prefixEnd_2312893 1187625811419524529200705 := by
  unfold tailWord_2312893
  simp only [CollatzResearch.WordTrace]
  refine ⟨84358138009791146521103333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56238758673194097680735555 84358138009791146521103333)
  ·
    refine ⟨15817150876835839972706875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 84358138009791146521103333 15817150876835839972706875)
    ·
      refine ⟨23725726315253759959060313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15817150876835839972706875 23725726315253759959060313)
      ·
        refine ⟨17794294736440319969295235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23725726315253759959060313 17794294736440319969295235)
        ·
          refine ⟨26691442104660479953942853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17794294736440319969295235 26691442104660479953942853)
          ·
            refine ⟨5004645394623839991364285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26691442104660479953942853 5004645394623839991364285)
            ·
              refine ⟨1876742022983939996761607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5004645394623839991364285 1876742022983939996761607)
              ·
                refine ⟨2815113034475909995142411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1876742022983939996761607 2815113034475909995142411)
                ·
                  refine ⟨4222669551713864992713617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2815113034475909995142411 4222669551713864992713617)
                  ·
                    refine ⟨3167002163785398744535213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4222669551713864992713617 3167002163785398744535213)
                    ·
                      refine ⟨1187625811419524529200705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3167002163785398744535213 1187625811419524529200705)
                      ·
                        rfl

theorem cell23_2312893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 3, 1, 1, 2, 3].length) (baseStart_2312893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2312893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2312893 prefixEnd_2312893 := by exact prefixLift 2312893
  have htrace : WordTrace (prefixWord ++ tailWord_2312893) baseStart_2312893 baseEnd_2312893 := by
    simpa [prefixWord, tailWord_2312893, baseEnd_2312893] using wordTrace_append hprefix tailTrace_2312893
  have hstable : (prefixWord ++ tailWord_2312893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2312893).length < 2 ^ (prefixWord ++ tailWord_2312893).sum := by decide
  have hdescent : baseEnd_2312893 < baseStart_2312893 := by decide
  rcases family_descends (prefixWord ++ tailWord_2312893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2312952 : List Nat := [2, 1, 2, 1, 1, 2, 3, 2, 9]
def baseStart_2312952 : Nat := 118140960795 + 2312952 * 2 ^ 59
def prefixEnd_2312952 : Nat := 4983230072969 + 3 ^ 40 * 2312952 * 2
def baseEnd_2312952 : Nat := 131961789642015533151437

theorem tailTrace_2312952 : CollatzResearch.WordTrace tailWord_2312952 prefixEnd_2312952 131961789642015533151437 := by
  unfold tailWord_2312952
  simp only [CollatzResearch.WordTrace]
  refine ⟨42180144958288699798750555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56240193277718266398334073 42180144958288699798750555)
  ·
    refine ⟨63270217437433049698125833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42180144958288699798750555 63270217437433049698125833)
    ·
      refine ⟨47452663078074787273594375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63270217437433049698125833 47452663078074787273594375)
      ·
        refine ⟨71178994617112180910391563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47452663078074787273594375 71178994617112180910391563)
        ·
          refine ⟨106768491925668271365587345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71178994617112180910391563 106768491925668271365587345)
          ·
            refine ⟨80076368944251203524190509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 106768491925668271365587345 80076368944251203524190509)
            ·
              refine ⟨30028638354094201321571441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 80076368944251203524190509 30028638354094201321571441)
              ·
                refine ⟨22521478765570650991178581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30028638354094201321571441 22521478765570650991178581)
                ·
                  refine ⟨131961789642015533151437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 22521478765570650991178581 131961789642015533151437)
                  ·
                    rfl

theorem cell23_2312952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 2, 9].length) (baseStart_2312952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2312952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2312952 prefixEnd_2312952 := by exact prefixLift 2312952
  have htrace : WordTrace (prefixWord ++ tailWord_2312952) baseStart_2312952 baseEnd_2312952 := by
    simpa [prefixWord, tailWord_2312952, baseEnd_2312952] using wordTrace_append hprefix tailTrace_2312952
  have hstable : (prefixWord ++ tailWord_2312952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2312952).length < 2 ^ (prefixWord ++ tailWord_2312952).sum := by decide
  have hdescent : baseEnd_2312952 < baseStart_2312952 := by decide
  rcases family_descends (prefixWord ++ tailWord_2312952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2312979 : List Nat := [1, 1, 1, 2, 1, 3, 3, 3, 2, 3, 3]
def baseStart_2312979 : Nat := 118140960795 + 2312979 * 2 ^ 59
def prefixEnd_2312979 : Nat := 4983230072969 + 3 ^ 40 * 2312979 * 2
def baseEnd_2312979 : Nat := 1187669970755811192725309

theorem tailTrace_2312979 : CollatzResearch.WordTrace tailWord_2312979 prefixEnd_2312979 1187669970755811192725309 := by
  unfold tailWord_2312979
  simp only [CollatzResearch.WordTrace]
  refine ⟨84361274687479583208733991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56240849791653055472489327 84361274687479583208733991)
  ·
    refine ⟨126541912031219374813100987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84361274687479583208733991 126541912031219374813100987)
    ·
      refine ⟨189812868046829062219651481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126541912031219374813100987 189812868046829062219651481)
      ·
        refine ⟨142359651035121796664738611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 189812868046829062219651481 142359651035121796664738611)
        ·
          refine ⟨213539476552682694997107917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142359651035121796664738611 213539476552682694997107917)
          ·
            refine ⟨80077303707256010623915469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 213539476552682694997107917 80077303707256010623915469)
            ·
              refine ⟨30028988890221003983968301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 80077303707256010623915469 30028988890221003983968301)
              ·
                refine ⟨11260870833832876493988113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30028988890221003983968301 11260870833832876493988113)
                ·
                  refine ⟨8445653125374657370491085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11260870833832876493988113 8445653125374657370491085)
                  ·
                    refine ⟨3167119922015496513934157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8445653125374657370491085 3167119922015496513934157)
                    ·
                      refine ⟨1187669970755811192725309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3167119922015496513934157 1187669970755811192725309)
                      ·
                        rfl

theorem cell23_2312979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 3, 2, 3, 3].length) (baseStart_2312979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2312979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2312979 prefixEnd_2312979 := by exact prefixLift 2312979
  have htrace : WordTrace (prefixWord ++ tailWord_2312979) baseStart_2312979 baseEnd_2312979 := by
    simpa [prefixWord, tailWord_2312979, baseEnd_2312979] using wordTrace_append hprefix tailTrace_2312979
  have hstable : (prefixWord ++ tailWord_2312979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2312979).length < 2 ^ (prefixWord ++ tailWord_2312979).sum := by decide
  have hdescent : baseEnd_2312979 < baseStart_2312979 := by decide
  rcases family_descends (prefixWord ++ tailWord_2312979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2313009 : List Nat := [1, 2, 2, 3, 2, 1, 2, 2, 1, 2, 5]
def baseStart_2313009 : Nat := 118140960795 + 2313009 * 2 ^ 59
def prefixEnd_2313009 : Nat := 4983230072969 + 3 ^ 40 * 2313009 * 2
def baseEnd_2313009 : Nat := 1187685375175446075350171

theorem tailTrace_2313009 : CollatzResearch.WordTrace tailWord_2313009 prefixEnd_2313009 1187685375175446075350171 := by
  unfold tailWord_2313009
  simp only [CollatzResearch.WordTrace]
  refine ⟨84362368877370898332326081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56241579251580598888217387 84362368877370898332326081)
  ·
    refine ⟨63271776658028173749244561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84362368877370898332326081 63271776658028173749244561)
    ·
      refine ⟨47453832493521130311933421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63271776658028173749244561 47453832493521130311933421)
      ·
        refine ⟨17795187185070423866975033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47453832493521130311933421 17795187185070423866975033)
        ·
          refine ⟨13346390388802817900231275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17795187185070423866975033 13346390388802817900231275)
          ·
            refine ⟨20019585583204226850346913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13346390388802817900231275 20019585583204226850346913)
            ·
              refine ⟨15014689187403170137760185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20019585583204226850346913 15014689187403170137760185)
              ·
                refine ⟨11261016890552377603320139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15014689187403170137760185 11261016890552377603320139)
                ·
                  refine ⟨16891525335828566404980209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11261016890552377603320139 16891525335828566404980209)
                  ·
                    refine ⟨12668644001871424803735157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16891525335828566404980209 12668644001871424803735157)
                    ·
                      refine ⟨1187685375175446075350171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12668644001871424803735157 1187685375175446075350171)
                      ·
                        rfl

theorem cell23_2313009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 2, 1, 2, 5].length) (baseStart_2313009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2313009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2313009 prefixEnd_2313009 := by exact prefixLift 2313009
  have htrace : WordTrace (prefixWord ++ tailWord_2313009) baseStart_2313009 baseEnd_2313009 := by
    simpa [prefixWord, tailWord_2313009, baseEnd_2313009] using wordTrace_append hprefix tailTrace_2313009
  have hstable : (prefixWord ++ tailWord_2313009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2313009).length < 2 ^ (prefixWord ++ tailWord_2313009).sum := by decide
  have hdescent : baseEnd_2313009 < baseStart_2313009 := by decide
  rcases family_descends (prefixWord ++ tailWord_2313009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2313120 : List Nat := [2, 1, 1, 4, 1, 1, 3, 5, 1, 1, 3]
def baseStart_2313120 : Nat := 118140960795 + 2313120 * 2 ^ 59
def prefixEnd_2313120 : Nat := 4983230072969 + 3 ^ 40 * 2313120 * 2
def baseEnd_2313120 : Nat := 1187742371528095141062161

theorem tailTrace_2313120 : CollatzResearch.WordTrace tailWord_2313120 prefixEnd_2313120 1187742371528095141062161 := by
  unfold tailWord_2313120
  simp only [CollatzResearch.WordTrace]
  refine ⟨42183208689984382144808407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56244278253312509526411209 42183208689984382144808407)
  ·
    refine ⟨63274813034976573217212611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42183208689984382144808407 63274813034976573217212611)
    ·
      refine ⟨94912219552464859825818917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63274813034976573217212611 94912219552464859825818917)
      ·
        refine ⟨17796041166087161217341047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 94912219552464859825818917 17796041166087161217341047)
        ·
          refine ⟨26694061749130741826011571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17796041166087161217341047 26694061749130741826011571)
          ·
            refine ⟨40041092623696112739017357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26694061749130741826011571 40041092623696112739017357)
            ·
              refine ⟨15015409733886042277131509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40041092623696112739017357 15015409733886042277131509)
              ·
                refine ⟨1407694662551816463481079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15015409733886042277131509 1407694662551816463481079)
                ·
                  refine ⟨2111541993827724695221619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1407694662551816463481079 2111541993827724695221619)
                  ·
                    refine ⟨3167312990741587042832429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2111541993827724695221619 3167312990741587042832429)
                    ·
                      refine ⟨1187742371528095141062161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3167312990741587042832429 1187742371528095141062161)
                      ·
                        rfl

theorem cell23_2313120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 5, 1, 1, 3].length) (baseStart_2313120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2313120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2313120 prefixEnd_2313120 := by exact prefixLift 2313120
  have htrace : WordTrace (prefixWord ++ tailWord_2313120) baseStart_2313120 baseEnd_2313120 := by
    simpa [prefixWord, tailWord_2313120, baseEnd_2313120] using wordTrace_append hprefix tailTrace_2313120
  have hstable : (prefixWord ++ tailWord_2313120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2313120).length < 2 ^ (prefixWord ++ tailWord_2313120).sum := by decide
  have hdescent : baseEnd_2313120 < baseStart_2313120 := by decide
  rcases family_descends (prefixWord ++ tailWord_2313120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2313123 : List Nat := [1, 1, 1, 4, 1, 2, 6, 1, 1, 5]
def baseStart_2313123 : Nat := 118140960795 + 2313123 * 2 ^ 59
def prefixEnd_2313123 : Nat := 4983230072969 + 3 ^ 40 * 2313123 * 2
def baseEnd_2313123 : Nat := 395914637323352876441549

theorem tailTrace_2313123 : CollatzResearch.WordTrace tailWord_2313123 prefixEnd_2313123 395914637323352876441549 := by
  unfold tailWord_2313123
  simp only [CollatzResearch.WordTrace]
  refine ⟨84366526798957895801976023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56244351199305263867984015 84366526798957895801976023)
  ·
    refine ⟨126549790198436843702964035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84366526798957895801976023 126549790198436843702964035)
    ·
      refine ⟨189824685297655265554446053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126549790198436843702964035 189824685297655265554446053)
      ·
        refine ⟨35592128493310362291458635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 189824685297655265554446053 35592128493310362291458635)
        ·
          refine ⟨53388192739965543437187953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35592128493310362291458635 53388192739965543437187953)
          ·
            refine ⟨40041144554974157577890965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53388192739965543437187953 40041144554974157577890965)
            ·
              refine ⟨1876928651014413636463639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 40041144554974157577890965 1876928651014413636463639)
              ·
                refine ⟨2815392976521620454695459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1876928651014413636463639 2815392976521620454695459)
                ·
                  refine ⟨4223089464782430682043189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2815392976521620454695459 4223089464782430682043189)
                  ·
                    refine ⟨395914637323352876441549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4223089464782430682043189 395914637323352876441549)
                    ·
                      rfl

theorem cell23_2313123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 6, 1, 1, 5].length) (baseStart_2313123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2313123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2313123 prefixEnd_2313123 := by exact prefixLift 2313123
  have htrace : WordTrace (prefixWord ++ tailWord_2313123) baseStart_2313123 baseEnd_2313123 := by
    simpa [prefixWord, tailWord_2313123, baseEnd_2313123] using wordTrace_append hprefix tailTrace_2313123
  have hstable : (prefixWord ++ tailWord_2313123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2313123).length < 2 ^ (prefixWord ++ tailWord_2313123).sum := by decide
  have hdescent : baseEnd_2313123 < baseStart_2313123 := by decide
  rcases family_descends (prefixWord ++ tailWord_2313123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2313146 : List Nat := [3, 1, 1, 1, 2, 1, 5, 2, 1, 1, 5]
def baseStart_2313146 : Nat := 118140960795 + 2313146 * 2 ^ 59
def prefixEnd_2313146 : Nat := 4983230072969 + 3 ^ 40 * 2313146 * 2
def baseEnd_2313146 : Nat := 1187755722025112039337041

theorem tailTrace_2313146 : CollatzResearch.WordTrace tailWord_2313146 prefixEnd_2313146 1187755722025112039337041 := by
  unfold tailWord_2313146
  simp only [CollatzResearch.WordTrace]
  refine ⟨21091841419468642682515823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56244910451916380486708861 21091841419468642682515823)
  ·
    refine ⟨31637762129202964023773735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21091841419468642682515823 31637762129202964023773735)
    ·
      refine ⟨47456643193804446035660603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31637762129202964023773735 47456643193804446035660603)
      ·
        refine ⟨71184964790706669053490905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47456643193804446035660603 71184964790706669053490905)
        ·
          refine ⟨53388723593030001790118179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71184964790706669053490905 53388723593030001790118179)
          ·
            refine ⟨80083085389545002685177269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53388723593030001790118179 80083085389545002685177269)
            ·
              refine ⟨7507789255269844001735369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 80083085389545002685177269 7507789255269844001735369)
              ·
                refine ⟨5630841941452383001301527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7507789255269844001735369 5630841941452383001301527)
                ·
                  refine ⟨8446262912178574501952291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5630841941452383001301527 8446262912178574501952291)
                  ·
                    refine ⟨12669394368267861752928437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8446262912178574501952291 12669394368267861752928437)
                    ·
                      refine ⟨1187755722025112039337041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12669394368267861752928437 1187755722025112039337041)
                      ·
                        rfl

theorem cell23_2313146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5, 2, 1, 1, 5].length) (baseStart_2313146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2313146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2313146 prefixEnd_2313146 := by exact prefixLift 2313146
  have htrace : WordTrace (prefixWord ++ tailWord_2313146) baseStart_2313146 baseEnd_2313146 := by
    simpa [prefixWord, tailWord_2313146, baseEnd_2313146] using wordTrace_append hprefix tailTrace_2313146
  have hstable : (prefixWord ++ tailWord_2313146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2313146).length < 2 ^ (prefixWord ++ tailWord_2313146).sum := by decide
  have hdescent : baseEnd_2313146 < baseStart_2313146 := by decide
  rcases family_descends (prefixWord ++ tailWord_2313146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2313160 : List Nat := [2, 1, 3, 1, 5, 1, 2, 2, 1, 1, 4]
def baseStart_2313160 : Nat := 118140960795 + 2313160 * 2 ^ 59
def prefixEnd_2313160 : Nat := 4983230072969 + 3 ^ 40 * 2313160 * 2
def baseEnd_2313160 : Nat := 1187762910754274984561977

theorem tailTrace_2313160 : CollatzResearch.WordTrace tailWord_2313160 prefixEnd_2313160 1187762910754274984561977 := by
  unfold tailWord_2313160
  simp only [CollatzResearch.WordTrace]
  refine ⟨42183938149911925560536467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56245250866549234080715289 42183938149911925560536467)
  ·
    refine ⟨63275907224867888340804701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42183938149911925560536467 63275907224867888340804701)
    ·
      refine ⟨23728465209325458127801763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63275907224867888340804701 23728465209325458127801763)
      ·
        refine ⟨35592697813988187191702645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23728465209325458127801763 35592697813988187191702645)
        ·
          refine ⟨3336815420061392549222123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 35592697813988187191702645 3336815420061392549222123)
          ·
            refine ⟨5005223130092088823833185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3336815420061392549222123 5005223130092088823833185)
            ·
              refine ⟨3753917347569066617874889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5005223130092088823833185 3753917347569066617874889)
              ·
                refine ⟨2815438010676799963406167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3753917347569066617874889 2815438010676799963406167)
                ·
                  refine ⟨4223157016015199945109251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2815438010676799963406167 4223157016015199945109251)
                  ·
                    refine ⟨6334735524022799917663877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4223157016015199945109251 6334735524022799917663877)
                    ·
                      refine ⟨1187762910754274984561977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6334735524022799917663877 1187762910754274984561977)
                      ·
                        rfl

theorem cell23_2313160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 2, 2, 1, 1, 4].length) (baseStart_2313160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2313160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2313160 prefixEnd_2313160 := by exact prefixLift 2313160
  have htrace : WordTrace (prefixWord ++ tailWord_2313160) baseStart_2313160 baseEnd_2313160 := by
    simpa [prefixWord, tailWord_2313160, baseEnd_2313160] using wordTrace_append hprefix tailTrace_2313160
  have hstable : (prefixWord ++ tailWord_2313160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2313160).length < 2 ^ (prefixWord ++ tailWord_2313160).sum := by decide
  have hdescent : baseEnd_2313160 < baseStart_2313160 := by decide
  rcases family_descends (prefixWord ++ tailWord_2313160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2313163 : List Nat := [1, 1, 1, 1, 3, 5, 1, 4, 1, 2, 3]
def baseStart_2313163 : Nat := 118140960795 + 2313163 * 2 ^ 59
def prefixEnd_2313163 : Nat := 4983230072969 + 3 ^ 40 * 2313163 * 2
def baseEnd_2313163 : Nat := 1187764451196238472824463

theorem tailTrace_2313163 : CollatzResearch.WordTrace tailWord_2313163 prefixEnd_2313163 1187764451196238472824463 := by
  unfold tailWord_2313163
  simp only [CollatzResearch.WordTrace]
  refine ⟨84367985718812982633432143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56245323812541988422288095 84367985718812982633432143)
  ·
    refine ⟨126551978578219473950148215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84367985718812982633432143 126551978578219473950148215)
    ·
      refine ⟨189827967867329210925222323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126551978578219473950148215 189827967867329210925222323)
      ·
        refine ⟨284741951800993816387833485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 189827967867329210925222323 284741951800993816387833485)
        ·
          refine ⟨106778231925372681145437557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 284741951800993816387833485 106778231925372681145437557)
          ·
            refine ⟨10010459243003688857384771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 106778231925372681145437557 10010459243003688857384771)
            ·
              refine ⟨15015688864505533286077157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10010459243003688857384771 15015688864505533286077157)
              ·
                refine ⟨2815441662094787491139467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15015688864505533286077157 2815441662094787491139467)
                ·
                  refine ⟨4223162493142181236709201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2815441662094787491139467 4223162493142181236709201)
                  ·
                    refine ⟨3167371869856635927531901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4223162493142181236709201 3167371869856635927531901)
                    ·
                      refine ⟨1187764451196238472824463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3167371869856635927531901 1187764451196238472824463)
                      ·
                        rfl

theorem cell23_2313163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 4, 1, 2, 3].length) (baseStart_2313163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2313163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2313163 prefixEnd_2313163 := by exact prefixLift 2313163
  have htrace : WordTrace (prefixWord ++ tailWord_2313163) baseStart_2313163 baseEnd_2313163 := by
    simpa [prefixWord, tailWord_2313163, baseEnd_2313163] using wordTrace_append hprefix tailTrace_2313163
  have hstable : (prefixWord ++ tailWord_2313163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2313163).length < 2 ^ (prefixWord ++ tailWord_2313163).sum := by decide
  have hdescent : baseEnd_2313163 < baseStart_2313163 := by decide
  rcases family_descends (prefixWord ++ tailWord_2313163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2313166 : List Nat := [4, 1, 1, 1, 2, 4, 1, 9]
def baseStart_2313166 : Nat := 118140960795 + 2313166 * 2 ^ 59
def prefixEnd_2313166 : Nat := 4983230072969 + 3 ^ 40 * 2313166 * 2
def baseEnd_2313166 : Nat := 43991333023637109669887

theorem tailTrace_2313166 : CollatzResearch.WordTrace tailWord_2313166 prefixEnd_2313166 43991333023637109669887 := by
  unfold tailWord_2313166
  simp only [CollatzResearch.WordTrace]
  refine ⟨10546011892225264268223919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56245396758534742763860901 10546011892225264268223919)
  ·
    refine ⟨15819017838337896402335879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10546011892225264268223919 15819017838337896402335879)
    ·
      refine ⟨23728526757506844603503819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15819017838337896402335879 23728526757506844603503819)
      ·
        refine ⟨35592790136260266905255729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23728526757506844603503819 35592790136260266905255729)
        ·
          refine ⟨26694592602195200178941797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35592790136260266905255729 26694592602195200178941797)
          ·
            refine ⟨5005236112911600033551587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26694592602195200178941797 5005236112911600033551587)
            ·
              refine ⟨7507854169367400050327381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5005236112911600033551587 7507854169367400050327381)
              ·
                refine ⟨43991333023637109669887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 7507854169367400050327381 43991333023637109669887)
                ·
                  rfl

theorem cell23_2313166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 1, 9].length) (baseStart_2313166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2313166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2313166 prefixEnd_2313166 := by exact prefixLift 2313166
  have htrace : WordTrace (prefixWord ++ tailWord_2313166) baseStart_2313166 baseEnd_2313166 := by
    simpa [prefixWord, tailWord_2313166, baseEnd_2313166] using wordTrace_append hprefix tailTrace_2313166
  have hstable : (prefixWord ++ tailWord_2313166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2313166).length < 2 ^ (prefixWord ++ tailWord_2313166).sum := by decide
  have hdescent : baseEnd_2313166 < baseStart_2313166 := by decide
  rcases family_descends (prefixWord ++ tailWord_2313166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2313183 : List Nat := [1, 1, 2, 3, 6, 1, 9]
def baseStart_2313183 : Nat := 118140960795 + 2313183 * 2 ^ 59
def prefixEnd_2313183 : Nat := 4983230072969 + 3 ^ 40 * 2313183 * 2
def baseEnd_2313183 : Nat := 14663885442090474007091

theorem tailTrace_2313183 : CollatzResearch.WordTrace tailWord_2313183 prefixEnd_2313183 14663885442090474007091 := by
  unfold tailWord_2313183
  simp only [CollatzResearch.WordTrace]
  refine ⟨84368715178740526049160203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56245810119160350699440135 84368715178740526049160203)
  ·
    refine ⟨126553072768110789073740305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84368715178740526049160203 126553072768110789073740305)
    ·
      refine ⟨94914804576083091805305229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126553072768110789073740305 94914804576083091805305229)
      ·
        refine ⟨35593051716031159426989461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 94914804576083091805305229 35593051716031159426989461)
        ·
          refine ⟨1668424299188960598140131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 35593051716031159426989461 1668424299188960598140131)
          ·
            refine ⟨2502636448783440897210197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1668424299188960598140131 2502636448783440897210197)
            ·
              refine ⟨14663885442090474007091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2502636448783440897210197 14663885442090474007091)
              ·
                rfl

theorem cell23_2313183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 9].length) (baseStart_2313183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2313183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2313183 prefixEnd_2313183 := by exact prefixLift 2313183
  have htrace : WordTrace (prefixWord ++ tailWord_2313183) baseStart_2313183 baseEnd_2313183 := by
    simpa [prefixWord, tailWord_2313183, baseEnd_2313183] using wordTrace_append hprefix tailTrace_2313183
  have hstable : (prefixWord ++ tailWord_2313183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2313183).length < 2 ^ (prefixWord ++ tailWord_2313183).sum := by decide
  have hdescent : baseEnd_2313183 < baseStart_2313183 := by decide
  rcases family_descends (prefixWord ++ tailWord_2313183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2313214 : List Nat := [4, 2, 2, 2, 2, 2, 1, 2, 1, 2, 3]
def baseStart_2313214 : Nat := 118140960795 + 2313214 * 2 ^ 59
def prefixEnd_2313214 : Nat := 4983230072969 + 3 ^ 40 * 2313214 * 2
def baseEnd_2313214 : Nat := 1187790638709617773286729

theorem tailTrace_2313214 : CollatzResearch.WordTrace tailWord_2313214 prefixEnd_2313214 1187790638709617773286729 := by
  unfold tailWord_2313214
  simp only [CollatzResearch.WordTrace]
  refine ⟨10546230730203527292942337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56246563894418812229025797 10546230730203527292942337)
  ·
    refine ⟨7909673047652645469706753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10546230730203527292942337 7909673047652645469706753)
    ·
      refine ⟨5932254785739484102280065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7909673047652645469706753 5932254785739484102280065)
      ·
        refine ⟨4449191089304613076710049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5932254785739484102280065 4449191089304613076710049)
        ·
          refine ⟨3336893316978459807532537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4449191089304613076710049 3336893316978459807532537)
          ·
            refine ⟨2502669987733844855649403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3336893316978459807532537 2502669987733844855649403)
            ·
              refine ⟨3754004981600767283474105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2502669987733844855649403 3754004981600767283474105)
              ·
                refine ⟨2815503736200575462605579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3754004981600767283474105 2815503736200575462605579)
                ·
                  refine ⟨4223255604300863193908369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2815503736200575462605579 4223255604300863193908369)
                  ·
                    refine ⟨3167441703225647395431277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4223255604300863193908369 3167441703225647395431277)
                    ·
                      refine ⟨1187790638709617773286729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3167441703225647395431277 1187790638709617773286729)
                      ·
                        rfl

theorem cell23_2313214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 1, 2, 1, 2, 3].length) (baseStart_2313214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2313214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2313214 prefixEnd_2313214 := by exact prefixLift 2313214
  have htrace : WordTrace (prefixWord ++ tailWord_2313214) baseStart_2313214 baseEnd_2313214 := by
    simpa [prefixWord, tailWord_2313214, baseEnd_2313214] using wordTrace_append hprefix tailTrace_2313214
  have hstable : (prefixWord ++ tailWord_2313214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2313214).length < 2 ^ (prefixWord ++ tailWord_2313214).sum := by decide
  have hdescent : baseEnd_2313214 < baseStart_2313214 := by decide
  rcases family_descends (prefixWord ++ tailWord_2313214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2313273 : List Nat := [1, 2, 1, 5, 2, 2, 1, 2, 7]
def baseStart_2313273 : Nat := 118140960795 + 2313273 * 2 ^ 59
def prefixEnd_2313273 : Nat := 4983230072969 + 3 ^ 40 * 2313273 * 2
def baseEnd_2313273 : Nat := 131980103785359226938773

theorem tailTrace_2313273 : CollatzResearch.WordTrace tailWord_2313273 prefixEnd_2313273 131980103785359226938773 := by
  unfold tailWord_2313273
  simp only [CollatzResearch.WordTrace]
  refine ⟨84371997748414471419936473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56247998498942980946624315 84371997748414471419936473)
  ·
    refine ⟨63278998311310853564952355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84371997748414471419936473 63278998311310853564952355)
    ·
      refine ⟨94918497466966280347428533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63278998311310853564952355 94918497466966280347428533)
      ·
        refine ⟨8898609137528088782571425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 94918497466966280347428533 8898609137528088782571425)
        ·
          refine ⟨6673956853146066586928569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8898609137528088782571425 6673956853146066586928569)
          ·
            refine ⟨5005467639859549940196427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6673956853146066586928569 5005467639859549940196427)
            ·
              refine ⟨7508201459789324910294641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5005467639859549940196427 7508201459789324910294641)
              ·
                refine ⟨5631151094841993682720981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7508201459789324910294641 5631151094841993682720981)
                ·
                  refine ⟨131980103785359226938773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5631151094841993682720981 131980103785359226938773)
                  ·
                    rfl

theorem cell23_2313273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 1, 2, 7].length) (baseStart_2313273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2313273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2313273 prefixEnd_2313273 := by exact prefixLift 2313273
  have htrace : WordTrace (prefixWord ++ tailWord_2313273) baseStart_2313273 baseEnd_2313273 := by
    simpa [prefixWord, tailWord_2313273, baseEnd_2313273] using wordTrace_append hprefix tailTrace_2313273
  have hstable : (prefixWord ++ tailWord_2313273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2313273).length < 2 ^ (prefixWord ++ tailWord_2313273).sum := by decide
  have hdescent : baseEnd_2313273 < baseStart_2313273 := by decide
  rcases family_descends (prefixWord ++ tailWord_2313273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2313296 : List Nat := [2, 1, 1, 1, 1, 3, 1, 3, 3, 2, 5]
def baseStart_2313296 : Nat := 118140960795 + 2313296 * 2 ^ 59
def prefixEnd_2313296 : Nat := 4983230072969 + 3 ^ 40 * 2313296 * 2
def baseEnd_2313296 : Nat := 1187832744123286452461351

theorem tailTrace_2313296 : CollatzResearch.WordTrace tailWord_2313296 prefixEnd_2313296 1187832744123286452461351 := by
  unfold tailWord_2313296
  simp only [CollatzResearch.WordTrace]
  refine ⟨42186418313665573174011871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56248557751554097565349161 42186418313665573174011871)
  ·
    refine ⟨63279627470498359761017807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42186418313665573174011871 63279627470498359761017807)
    ·
      refine ⟨94919441205747539641526711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63279627470498359761017807 94919441205747539641526711)
      ·
        refine ⟨142379161808621309462290067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94919441205747539641526711 142379161808621309462290067)
        ·
          refine ⟨213568742712931964193435101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142379161808621309462290067 213568742712931964193435101)
          ·
            refine ⟨80088278517349486572538163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 213568742712931964193435101 80088278517349486572538163)
            ·
              refine ⟨120132417776024229858807245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80088278517349486572538163 120132417776024229858807245)
              ·
                refine ⟨45049656666009086197052717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 120132417776024229858807245 45049656666009086197052717)
                ·
                  refine ⟨16893621249753407323894769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45049656666009086197052717 16893621249753407323894769)
                  ·
                    refine ⟨12670215937315055492921077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16893621249753407323894769 12670215937315055492921077)
                    ·
                      refine ⟨1187832744123286452461351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12670215937315055492921077 1187832744123286452461351)
                      ·
                        rfl

theorem cell23_2313296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 3, 3, 2, 5].length) (baseStart_2313296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2313296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2313296 prefixEnd_2313296 := by exact prefixLift 2313296
  have htrace : WordTrace (prefixWord ++ tailWord_2313296) baseStart_2313296 baseEnd_2313296 := by
    simpa [prefixWord, tailWord_2313296, baseEnd_2313296] using wordTrace_append hprefix tailTrace_2313296
  have hstable : (prefixWord ++ tailWord_2313296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2313296).length < 2 ^ (prefixWord ++ tailWord_2313296).sum := by decide
  have hdescent : baseEnd_2313296 < baseStart_2313296 := by decide
  rcases family_descends (prefixWord ++ tailWord_2313296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2313343 : List Nat := [1, 1, 2, 2, 1, 1, 1, 1, 8, 2, 3]
def baseStart_2313343 : Nat := 118140960795 + 2313343 * 2 ^ 59
def prefixEnd_2313343 : Nat := 4983230072969 + 3 ^ 40 * 2313343 * 2
def baseEnd_2313343 : Nat := 1187856877714047768573635

theorem tailTrace_2313343 : CollatzResearch.WordTrace tailWord_2313343 prefixEnd_2313343 1187856877714047768573635 := by
  unfold tailWord_2313343
  simp only [CollatzResearch.WordTrace]
  refine ⟨84374550858160873374984683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56249700572107248916656455 84374550858160873374984683)
  ·
    refine ⟨126561826287241310062477025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84374550858160873374984683 126561826287241310062477025)
    ·
      refine ⟨94921369715430982546857769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126561826287241310062477025 94921369715430982546857769)
      ·
        refine ⟨71191027286573236910143327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94921369715430982546857769 71191027286573236910143327)
        ·
          refine ⟨106786540929859855365214991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71191027286573236910143327 106786540929859855365214991)
          ·
            refine ⟨160179811394789783047822487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106786540929859855365214991 160179811394789783047822487)
            ·
              refine ⟨240269717092184674571733731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 160179811394789783047822487 240269717092184674571733731)
              ·
                refine ⟨360404575638277011857600597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 240269717092184674571733731 360404575638277011857600597)
                ·
                  refine ⟨4223491120761058732706257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 360404575638277011857600597 4223491120761058732706257)
                  ·
                    refine ⟨3167618340570794049529693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4223491120761058732706257 3167618340570794049529693)
                    ·
                      refine ⟨1187856877714047768573635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3167618340570794049529693 1187856877714047768573635)
                      ·
                        rfl

theorem cell23_2313343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 8, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 8, 2, 3].length) (baseStart_2313343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2313343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2313343 prefixEnd_2313343 := by exact prefixLift 2313343
  have htrace : WordTrace (prefixWord ++ tailWord_2313343) baseStart_2313343 baseEnd_2313343 := by
    simpa [prefixWord, tailWord_2313343, baseEnd_2313343] using wordTrace_append hprefix tailTrace_2313343
  have hstable : (prefixWord ++ tailWord_2313343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2313343).length < 2 ^ (prefixWord ++ tailWord_2313343).sum := by decide
  have hdescent : baseEnd_2313343 < baseStart_2313343 := by decide
  rcases family_descends (prefixWord ++ tailWord_2313343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2313367 : List Nat := [1, 1, 3, 3, 3, 3, 1, 1, 3, 4]
def baseStart_2313367 : Nat := 118140960795 + 2313367 * 2 ^ 59
def prefixEnd_2313367 : Nat := 4983230072969 + 3 ^ 40 * 2313367 * 2
def baseEnd_2313367 : Nat := 395956400416585224891175

theorem tailTrace_2313367 : CollatzResearch.WordTrace tailWord_2313367 prefixEnd_2313367 395956400416585224891175 := by
  unfold tailWord_2313367
  simp only [CollatzResearch.WordTrace]
  refine ⟨84375426210073925473858355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56250284140049283649238903 84375426210073925473858355)
  ·
    refine ⟨126563139315110888210787533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84375426210073925473858355 126563139315110888210787533)
    ·
      refine ⟨47461177243166583079045325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 126563139315110888210787533 47461177243166583079045325)
      ·
        refine ⟨17797941466187468654641997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47461177243166583079045325 17797941466187468654641997)
        ·
          refine ⟨6674228049820300745490749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17797941466187468654641997 6674228049820300745490749)
          ·
            refine ⟨2502835518682612779559031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6674228049820300745490749 2502835518682612779559031)
            ·
              refine ⟨3754253278023919169338547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2502835518682612779559031 3754253278023919169338547)
              ·
                refine ⟨5631379917035878754007821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3754253278023919169338547 5631379917035878754007821)
                ·
                  refine ⟨2111767468888454532752933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5631379917035878754007821 2111767468888454532752933)
                  ·
                    refine ⟨395956400416585224891175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2111767468888454532752933 395956400416585224891175)
                    ·
                      rfl

theorem cell23_2313367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 1, 1, 3, 4].length) (baseStart_2313367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2313367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2313367 prefixEnd_2313367 := by exact prefixLift 2313367
  have htrace : WordTrace (prefixWord ++ tailWord_2313367) baseStart_2313367 baseEnd_2313367 := by
    simpa [prefixWord, tailWord_2313367, baseEnd_2313367] using wordTrace_append hprefix tailTrace_2313367
  have hstable : (prefixWord ++ tailWord_2313367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2313367).length < 2 ^ (prefixWord ++ tailWord_2313367).sum := by decide
  have hdescent : baseEnd_2313367 < baseStart_2313367 := by decide
  rcases family_descends (prefixWord ++ tailWord_2313367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2313380 : List Nat := [2, 3, 1, 2, 3, 2, 1, 3, 6]
def baseStart_2313380 : Nat := 118140960795 + 2313380 * 2 ^ 59
def prefixEnd_2313380 : Nat := 4983230072969 + 3 ^ 40 * 2313380 * 2
def baseEnd_2313380 : Nat := 131986208499807124867885

theorem tailTrace_2313380 : CollatzResearch.WordTrace tailWord_2313380 prefixEnd_2313380 131986208499807124867885 := by
  unfold tailWord_2313380
  simp only [CollatzResearch.WordTrace]
  refine ⟨42187950179513414347040797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56250600239351219129387729 42187950179513414347040797)
  ·
    refine ⟨15820481317317530380140299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42187950179513414347040797 15820481317317530380140299)
    ·
      refine ⟨23730721975976295570210449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15820481317317530380140299 23730721975976295570210449)
      ·
        refine ⟨17798041481982221677657837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23730721975976295570210449 17798041481982221677657837)
        ·
          refine ⟨6674265555743333129121689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17798041481982221677657837 6674265555743333129121689)
          ·
            refine ⟨5005699166807499846841267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6674265555743333129121689 5005699166807499846841267)
            ·
              refine ⟨7508548750211249770261901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5005699166807499846841267 7508548750211249770261901)
              ·
                refine ⟨2815705781329218663848213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7508548750211249770261901 2815705781329218663848213)
                ·
                  refine ⟨131986208499807124867885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2815705781329218663848213 131986208499807124867885)
                  ·
                    rfl

theorem cell23_2313380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 1, 3, 6].length) (baseStart_2313380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2313380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2313380 prefixEnd_2313380 := by exact prefixLift 2313380
  have htrace : WordTrace (prefixWord ++ tailWord_2313380) baseStart_2313380 baseEnd_2313380 := by
    simpa [prefixWord, tailWord_2313380, baseEnd_2313380] using wordTrace_append hprefix tailTrace_2313380
  have hstable : (prefixWord ++ tailWord_2313380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2313380).length < 2 ^ (prefixWord ++ tailWord_2313380).sum := by decide
  have hdescent : baseEnd_2313380 < baseStart_2313380 := by decide
  rcases family_descends (prefixWord ++ tailWord_2313380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2313433 : List Nat := [1, 2, 1, 2, 3, 1, 1, 3, 3, 1, 5]
def baseStart_2313433 : Nat := 118140960795 + 2313433 * 2 ^ 59
def prefixEnd_2313433 : Nat := 4983230072969 + 3 ^ 40 * 2313433 * 2
def baseEnd_2313433 : Nat := 1187903090972952416448221

theorem tailTrace_2313433 : CollatzResearch.WordTrace tailWord_2313433 prefixEnd_2313433 1187903090972952416448221 := by
  unfold tailWord_2313433
  simp only [CollatzResearch.WordTrace]
  refine ⟨84377833427834818745760953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56251888951889879163840635 84377833427834818745760953)
  ·
    refine ⟨63283375070876114059320715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84377833427834818745760953 63283375070876114059320715)
    ·
      refine ⟨94925062606314171088981073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63283375070876114059320715 94925062606314171088981073)
      ·
        refine ⟨71193796954735628316735805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94925062606314171088981073 71193796954735628316735805)
        ·
          refine ⟨26697673858025860618775927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71193796954735628316735805 26697673858025860618775927)
          ·
            refine ⟨40046510787038790928163891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26697673858025860618775927 40046510787038790928163891)
            ·
              refine ⟨60069766180558186392245837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40046510787038790928163891 60069766180558186392245837)
              ·
                refine ⟨22526162317709319897092189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 60069766180558186392245837 22526162317709319897092189)
                ·
                  refine ⟨8447310869140994961409571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22526162317709319897092189 8447310869140994961409571)
                  ·
                    refine ⟨12670966303711492442114357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8447310869140994961409571 12670966303711492442114357)
                    ·
                      refine ⟨1187903090972952416448221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12670966303711492442114357 1187903090972952416448221)
                      ·
                        rfl

theorem cell23_2313433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 3, 3, 1, 5].length) (baseStart_2313433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2313433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2313433 prefixEnd_2313433 := by exact prefixLift 2313433
  have htrace : WordTrace (prefixWord ++ tailWord_2313433) baseStart_2313433 baseEnd_2313433 := by
    simpa [prefixWord, tailWord_2313433, baseEnd_2313433] using wordTrace_append hprefix tailTrace_2313433
  have hstable : (prefixWord ++ tailWord_2313433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2313433).length < 2 ^ (prefixWord ++ tailWord_2313433).sum := by decide
  have hdescent : baseEnd_2313433 < baseStart_2313433 := by decide
  rcases family_descends (prefixWord ++ tailWord_2313433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2313440 : List Nat := [2, 1, 1, 3, 1, 5, 2, 1, 1, 6]
def baseStart_2313440 : Nat := 118140960795 + 2313440 * 2 ^ 59
def prefixEnd_2313440 : Nat := 4983230072969 + 3 ^ 40 * 2313440 * 2
def baseEnd_2313440 : Nat := 395968895112511296353563

theorem tailTrace_2313440 : CollatzResearch.WordTrace tailWord_2313440 prefixEnd_2313440 395968895112511296353563 := by
  unfold tailWord_2313440
  simp only [CollatzResearch.WordTrace]
  refine ⟨42189044369404729470632887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56252059159206305960843849 42189044369404729470632887)
  ·
    refine ⟨63283566554107094205949331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42189044369404729470632887 63283566554107094205949331)
    ·
      refine ⟨94925349831160641308923997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63283566554107094205949331 94925349831160641308923997)
      ·
        refine ⟨35597006186685240490846499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 94925349831160641308923997 35597006186685240490846499)
        ·
          refine ⟨53395509280027860736269749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35597006186685240490846499 53395509280027860736269749)
          ·
            refine ⟨5005828995002611944025289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 53395509280027860736269749 5005828995002611944025289)
            ·
              refine ⟨3754371746251958958018967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5005828995002611944025289 3754371746251958958018967)
              ·
                refine ⟨5631557619377938437028451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3754371746251958958018967 5631557619377938437028451)
                ·
                  refine ⟨8447336429066907655542677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5631557619377938437028451 8447336429066907655542677)
                  ·
                    refine ⟨395968895112511296353563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8447336429066907655542677 395968895112511296353563)
                    ·
                      rfl

theorem cell23_2313440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 2, 1, 1, 6].length) (baseStart_2313440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2313440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2313440 prefixEnd_2313440 := by exact prefixLift 2313440
  have htrace : WordTrace (prefixWord ++ tailWord_2313440) baseStart_2313440 baseEnd_2313440 := by
    simpa [prefixWord, tailWord_2313440, baseEnd_2313440] using wordTrace_append hprefix tailTrace_2313440
  have hstable : (prefixWord ++ tailWord_2313440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2313440).length < 2 ^ (prefixWord ++ tailWord_2313440).sum := by decide
  have hdescent : baseEnd_2313440 < baseStart_2313440 := by decide
  rcases family_descends (prefixWord ++ tailWord_2313440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2313470 : List Nat := [4, 2, 2, 1, 1, 3, 10]
def baseStart_2313470 : Nat := 118140960795 + 2313470 * 2 ^ 59
def prefixEnd_2313470 : Nat := 4983230072969 + 3 ^ 40 * 2313470 * 2
def baseEnd_2313470 : Nat := 14665704811816898415871

theorem tailTrace_2313470 : CollatzResearch.WordTrace tailWord_2313470 prefixEnd_2313470 14665704811816898415871 := by
  unfold tailWord_2313470
  simp only [CollatzResearch.WordTrace]
  refine ⟨10547397866087596758107233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56252788619133849376571909 10547397866087596758107233)
  ·
    refine ⟨7910548399565697568580425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10547397866087596758107233 7910548399565697568580425)
    ·
      refine ⟨5932911299674273176435319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7910548399565697568580425 5932911299674273176435319)
      ·
        refine ⟨8899366949511409764652979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5932911299674273176435319 8899366949511409764652979)
        ·
          refine ⟨13349050424267114646979469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8899366949511409764652979 13349050424267114646979469)
          ·
            refine ⟨5005893909100167992617301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13349050424267114646979469 5005893909100167992617301)
            ·
              refine ⟨14665704811816898415871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 5005893909100167992617301 14665704811816898415871)
              ·
                rfl

theorem cell23_2313470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 10].length) (baseStart_2313470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2313470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2313470 prefixEnd_2313470 := by exact prefixLift 2313470
  have htrace : WordTrace (prefixWord ++ tailWord_2313470) baseStart_2313470 baseEnd_2313470 := by
    simpa [prefixWord, tailWord_2313470, baseEnd_2313470] using wordTrace_append hprefix tailTrace_2313470
  have hstable : (prefixWord ++ tailWord_2313470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2313470).length < 2 ^ (prefixWord ++ tailWord_2313470).sum := by decide
  have hdescent : baseEnd_2313470 < baseStart_2313470 := by decide
  rcases family_descends (prefixWord ++ tailWord_2313470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2313474 : List Nat := [3, 4, 1, 1, 3, 1, 1, 1, 4, 4]
def baseStart_2313474 : Nat := 118140960795 + 2313474 * 2 ^ 59
def prefixEnd_2313474 : Nat := 4983230072969 + 3 ^ 40 * 2313474 * 2
def baseEnd_2313474 : Nat := 395974714559928918678511

theorem tailTrace_2313474 : CollatzResearch.WordTrace tailWord_2313474 prefixEnd_2313474 395974714559928918678511 := by
  unfold tailWord_2313474
  simp only [CollatzResearch.WordTrace]
  refine ⟨21094832205171570687000869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56252885880457521832002317 21094832205171570687000869)
  ·
    refine ⟨3955281038469669503812663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21094832205171570687000869 3955281038469669503812663)
    ·
      refine ⟨5932921557704504255718995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3955281038469669503812663 5932921557704504255718995)
      ·
        refine ⟨8899382336556756383578493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5932921557704504255718995 8899382336556756383578493)
        ·
          refine ⟨3337268376208783643841935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8899382336556756383578493 3337268376208783643841935)
          ·
            refine ⟨5005902564313175465762903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3337268376208783643841935 5005902564313175465762903)
            ·
              refine ⟨7508853846469763198644355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5005902564313175465762903 7508853846469763198644355)
              ·
                refine ⟨11263280769704644797966533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7508853846469763198644355 11263280769704644797966533)
                ·
                  refine ⟨2111865144319620899618725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11263280769704644797966533 2111865144319620899618725)
                  ·
                    refine ⟨395974714559928918678511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2111865144319620899618725 395974714559928918678511)
                    ·
                      rfl

theorem cell23_2313474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 1, 1, 4, 4].length) (baseStart_2313474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2313474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2313474 prefixEnd_2313474 := by exact prefixLift 2313474
  have htrace : WordTrace (prefixWord ++ tailWord_2313474) baseStart_2313474 baseEnd_2313474 := by
    simpa [prefixWord, tailWord_2313474, baseEnd_2313474] using wordTrace_append hprefix tailTrace_2313474
  have hstable : (prefixWord ++ tailWord_2313474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2313474).length < 2 ^ (prefixWord ++ tailWord_2313474).sum := by decide
  have hdescent : baseEnd_2313474 < baseStart_2313474 := by decide
  rcases family_descends (prefixWord ++ tailWord_2313474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2313504 : List Nat := [2, 1, 1, 5, 4, 1, 2, 7]
def baseStart_2313504 : Nat := 118140960795 + 2313504 * 2 ^ 59
def prefixEnd_2313504 : Nat := 4983230072969 + 3 ^ 40 * 2313504 * 2
def baseEnd_2313504 : Nat := 43997761040719319950385

theorem tailTrace_2313504 : CollatzResearch.WordTrace tailWord_2313504 prefixEnd_2313504 43997761040719319950385 := by
  unfold tailWord_2313504
  simp only [CollatzResearch.WordTrace]
  refine ⟨42190211505288798935797783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56253615340385065247730377 42190211505288798935797783)
  ·
    refine ⟨63285317257933198403696675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42190211505288798935797783 63285317257933198403696675)
    ·
      refine ⟨94927975886899797605545013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63285317257933198403696675 94927975886899797605545013)
      ·
        refine ⟨8899497739396856025519845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 94927975886899797605545013 8899497739396856025519845)
        ·
          refine ⟨1668655826136910504784971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8899497739396856025519845 1668655826136910504784971)
          ·
            refine ⟨2502983739205365757177457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1668655826136910504784971 2502983739205365757177457)
            ·
              refine ⟨1877237804404024317883093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2502983739205365757177457 1877237804404024317883093)
              ·
                refine ⟨43997761040719319950385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1877237804404024317883093 43997761040719319950385)
                ·
                  rfl

theorem cell23_2313504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 2, 7].length) (baseStart_2313504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2313504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2313504 prefixEnd_2313504 := by exact prefixLift 2313504
  have htrace : WordTrace (prefixWord ++ tailWord_2313504) baseStart_2313504 baseEnd_2313504 := by
    simpa [prefixWord, tailWord_2313504, baseEnd_2313504] using wordTrace_append hprefix tailTrace_2313504
  have hstable : (prefixWord ++ tailWord_2313504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2313504).length < 2 ^ (prefixWord ++ tailWord_2313504).sum := by decide
  have hdescent : baseEnd_2313504 < baseStart_2313504 := by decide
  rcases family_descends (prefixWord ++ tailWord_2313504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2313514 : List Nat := [3, 1, 4, 2, 1, 1, 1, 2, 4, 1, 3]
def baseStart_2313514 : Nat := 118140960795 + 2313514 * 2 ^ 59
def prefixEnd_2313514 : Nat := 4983230072969 + 3 ^ 40 * 2313514 * 2
def baseEnd_2313514 : Nat := 1187944682905966599535349

theorem tailTrace_2313514 : CollatzResearch.WordTrace tailWord_2313514 prefixEnd_2313514 1187944682905966599535349 := by
  unfold tailWord_2313514
  simp only [CollatzResearch.WordTrace]
  refine ⟨21095196935135342394864899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56253858493694246386306397 21095196935135342394864899)
  ·
    refine ⟨31642795402703013592297349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21095196935135342394864899 31642795402703013592297349)
    ·
      refine ⟨5933024138006815048555753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31642795402703013592297349 5933024138006815048555753)
      ·
        refine ⟨4449768103505111286416815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5933024138006815048555753 4449768103505111286416815)
        ·
          refine ⟨6674652155257666929625223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4449768103505111286416815 6674652155257666929625223)
          ·
            refine ⟨10011978232886500394437835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6674652155257666929625223 10011978232886500394437835)
            ·
              refine ⟨15017967349329750591656753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10011978232886500394437835 15017967349329750591656753)
              ·
                refine ⟨11263475511997312943742565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15017967349329750591656753 11263475511997312943742565)
                ·
                  refine ⟨2111901658499496176951731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11263475511997312943742565 2111901658499496176951731)
                  ·
                    refine ⟨3167852487749244265427597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2111901658499496176951731 3167852487749244265427597)
                    ·
                      refine ⟨1187944682905966599535349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3167852487749244265427597 1187944682905966599535349)
                      ·
                        rfl

theorem cell23_2313514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 2, 4, 1, 3].length) (baseStart_2313514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2313514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2313514 prefixEnd_2313514 := by exact prefixLift 2313514
  have htrace : WordTrace (prefixWord ++ tailWord_2313514) baseStart_2313514 baseEnd_2313514 := by
    simpa [prefixWord, tailWord_2313514, baseEnd_2313514] using wordTrace_append hprefix tailTrace_2313514
  have hstable : (prefixWord ++ tailWord_2313514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2313514).length < 2 ^ (prefixWord ++ tailWord_2313514).sum := by decide
  have hdescent : baseEnd_2313514 < baseStart_2313514 := by decide
  rcases family_descends (prefixWord ++ tailWord_2313514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2313542 : List Nat := [6, 1, 1, 3, 2, 1, 2, 1, 2, 4]
def baseStart_2313542 : Nat := 118140960795 + 2313542 * 2 ^ 59
def prefixEnd_2313542 : Nat := 4983230072969 + 3 ^ 40 * 2313542 * 2
def baseEnd_2313542 : Nat := 395986353454764163328407

theorem tailTrace_2313542 : CollatzResearch.WordTrace tailWord_2313542 prefixEnd_2313542 395986353454764163328407 := by
  unfold tailWord_2313542
  simp only [CollatzResearch.WordTrace]
  refine ⟨2636931530763747823796215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 56254539322959953574319253 2636931530763747823796215)
  ·
    refine ⟨3955397296145621735694323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2636931530763747823796215 3955397296145621735694323)
    ·
      refine ⟨5933095944218432603541485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3955397296145621735694323 5933095944218432603541485)
      ·
        refine ⟨2224910979081912226328057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5933095944218432603541485 2224910979081912226328057)
        ·
          refine ⟨1668683234311434169746043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2224910979081912226328057 1668683234311434169746043)
          ·
            refine ⟨2503024851467151254619065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1668683234311434169746043 2503024851467151254619065)
            ·
              refine ⟨1877268638600363440964299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2503024851467151254619065 1877268638600363440964299)
              ·
                refine ⟨2815902957900545161446449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1877268638600363440964299 2815902957900545161446449)
                ·
                  refine ⟨2111927218425408871084837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2815902957900545161446449 2111927218425408871084837)
                  ·
                    refine ⟨395986353454764163328407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2111927218425408871084837 395986353454764163328407)
                    ·
                      rfl

theorem cell23_2313542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 2, 1, 2, 4].length) (baseStart_2313542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2313542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2313542 prefixEnd_2313542 := by exact prefixLift 2313542
  have htrace : WordTrace (prefixWord ++ tailWord_2313542) baseStart_2313542 baseEnd_2313542 := by
    simpa [prefixWord, tailWord_2313542, baseEnd_2313542] using wordTrace_append hprefix tailTrace_2313542
  have hstable : (prefixWord ++ tailWord_2313542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2313542).length < 2 ^ (prefixWord ++ tailWord_2313542).sum := by decide
  have hdescent : baseEnd_2313542 < baseStart_2313542 := by decide
  rcases family_descends (prefixWord ++ tailWord_2313542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2313550 : List Nat := [4, 1, 1, 1, 1, 1, 4, 1, 1, 4, 4]
def baseStart_2313550 : Nat := 118140960795 + 2313550 * 2 ^ 59
def prefixEnd_2313550 : Nat := 4983230072969 + 3 ^ 40 * 2313550 * 2
def baseEnd_2313550 : Nat := 1187963168209528458685183

theorem tailTrace_2313550 : CollatzResearch.WordTrace tailWord_2313550 prefixEnd_2313550 1187963168209528458685183 := by
  unfold tailWord_2313550
  simp only [CollatzResearch.WordTrace]
  refine ⟨10547762596051368465971263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56254733845607298485180069 10547762596051368465971263)
  ·
    refine ⟨15821643894077052698956895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10547762596051368465971263 15821643894077052698956895)
    ·
      refine ⟨23732465841115579048435343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15821643894077052698956895 23732465841115579048435343)
      ·
        refine ⟨35598698761673368572653015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23732465841115579048435343 35598698761673368572653015)
        ·
          refine ⟨53398048142510052858979523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35598698761673368572653015 53398048142510052858979523)
          ·
            refine ⟨80097072213765079288469285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53398048142510052858979523 80097072213765079288469285)
            ·
              refine ⟨15018201040080952366587991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 80097072213765079288469285 15018201040080952366587991)
              ·
                refine ⟨22527301560121428549881987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15018201040080952366587991 22527301560121428549881987)
                ·
                  refine ⟨33790952340182142824822981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22527301560121428549881987 33790952340182142824822981)
                  ·
                    refine ⟨6335803563784151779654309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 33790952340182142824822981 6335803563784151779654309)
                    ·
                      refine ⟨1187963168209528458685183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6335803563784151779654309 1187963168209528458685183)
                      ·
                        rfl

theorem cell23_2313550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 1, 1, 4, 4].length) (baseStart_2313550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2313550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2313550 prefixEnd_2313550 := by exact prefixLift 2313550
  have htrace : WordTrace (prefixWord ++ tailWord_2313550) baseStart_2313550 baseEnd_2313550 := by
    simpa [prefixWord, tailWord_2313550, baseEnd_2313550] using wordTrace_append hprefix tailTrace_2313550
  have hstable : (prefixWord ++ tailWord_2313550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2313550).length < 2 ^ (prefixWord ++ tailWord_2313550).sum := by decide
  have hdescent : baseEnd_2313550 < baseStart_2313550 := by decide
  rcases family_descends (prefixWord ++ tailWord_2313550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2313597 : List Nat := [1, 4, 1, 1, 2, 2, 1, 1, 1, 7, 2]
def baseStart_2313597 : Nat := 118140960795 + 2313597 * 2 ^ 59
def prefixEnd_2313597 : Nat := 4983230072969 + 3 ^ 40 * 2313597 * 2
def baseEnd_2313597 : Nat := 1187987301800289774797467

theorem tailTrace_2313597 : CollatzResearch.WordTrace tailWord_2313597 prefixEnd_2313597 1187987301800289774797467 := by
  unfold tailWord_2313597
  simp only [CollatzResearch.WordTrace]
  refine ⟨84383814999240674754731045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56255876666160449836487363 84383814999240674754731045)
  ·
    refine ⟨15821965312357626516512071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 84383814999240674754731045 15821965312357626516512071)
    ·
      refine ⟨23732947968536439774768107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15821965312357626516512071 23732947968536439774768107)
      ·
        refine ⟨35599421952804659662152161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23732947968536439774768107 35599421952804659662152161)
        ·
          refine ⟨26699566464603494746614121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35599421952804659662152161 26699566464603494746614121)
          ·
            refine ⟨20024674848452621059960591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26699566464603494746614121 20024674848452621059960591)
            ·
              refine ⟨30037012272678931589940887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20024674848452621059960591 30037012272678931589940887)
              ·
                refine ⟨45055518409018397384911331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30037012272678931589940887 45055518409018397384911331)
                ·
                  refine ⟨67583277613527596077366997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45055518409018397384911331 67583277613527596077366997)
                  ·
                    refine ⟨1583983069067053033063289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 67583277613527596077366997 1583983069067053033063289)
                    ·
                      refine ⟨1187987301800289774797467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1583983069067053033063289 1187987301800289774797467)
                      ·
                        rfl

theorem cell23_2313597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 1, 1, 7, 2].length) (baseStart_2313597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2313597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2313597 prefixEnd_2313597 := by exact prefixLift 2313597
  have htrace : WordTrace (prefixWord ++ tailWord_2313597) baseStart_2313597 baseEnd_2313597 := by
    simpa [prefixWord, tailWord_2313597, baseEnd_2313597] using wordTrace_append hprefix tailTrace_2313597
  have hstable : (prefixWord ++ tailWord_2313597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2313597).length < 2 ^ (prefixWord ++ tailWord_2313597).sum := by decide
  have hdescent : baseEnd_2313597 < baseStart_2313597 := by decide
  rcases family_descends (prefixWord ++ tailWord_2313597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2313647 : List Nat := [1, 1, 2, 1, 2, 2, 1, 6, 2, 2, 3]
def baseStart_2313647 : Nat := 118140960795 + 2313647 * 2 ^ 59
def prefixEnd_2313647 : Nat := 4983230072969 + 3 ^ 40 * 2313647 * 2
def baseEnd_2313647 : Nat := 1188012975833014579172237

theorem tailTrace_2313647 : CollatzResearch.WordTrace tailWord_2313647 prefixEnd_2313647 1188012975833014579172237 := by
  unfold tailWord_2313647
  simp only [CollatzResearch.WordTrace]
  refine ⟨84385638649059533294051195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56257092432706355529367463 84385638649059533294051195)
  ·
    refine ⟨126578457973589299941076793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84385638649059533294051195 126578457973589299941076793)
    ·
      refine ⟨94933843480191974955807595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126578457973589299941076793 94933843480191974955807595)
      ·
        refine ⟨142400765220287962433711393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94933843480191974955807595 142400765220287962433711393)
        ·
          refine ⟨106800573915215971825283545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 142400765220287962433711393 106800573915215971825283545)
          ·
            refine ⟨80100430436411978868962659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 106800573915215971825283545 80100430436411978868962659)
            ·
              refine ⟨120150645654617968303443989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80100430436411978868962659 120150645654617968303443989)
              ·
                refine ⟨5632061515060217264223937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 120150645654617968303443989 5632061515060217264223937)
                ·
                  refine ⟨4224046136295162948167953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5632061515060217264223937 4224046136295162948167953)
                  ·
                    refine ⟨3168034602221372211125965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4224046136295162948167953 3168034602221372211125965)
                    ·
                      refine ⟨1188012975833014579172237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3168034602221372211125965 1188012975833014579172237)
                      ·
                        rfl

theorem cell23_2313647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 6, 2, 2, 3].length) (baseStart_2313647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2313647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2313647 prefixEnd_2313647 := by exact prefixLift 2313647
  have htrace : WordTrace (prefixWord ++ tailWord_2313647) baseStart_2313647 baseEnd_2313647 := by
    simpa [prefixWord, tailWord_2313647, baseEnd_2313647] using wordTrace_append hprefix tailTrace_2313647
  have hstable : (prefixWord ++ tailWord_2313647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2313647).length < 2 ^ (prefixWord ++ tailWord_2313647).sum := by decide
  have hdescent : baseEnd_2313647 < baseStart_2313647 := by decide
  rcases family_descends (prefixWord ++ tailWord_2313647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2313711 : List Nat := [1, 1, 2, 1, 4, 1, 2, 6, 1, 1, 3]
def baseStart_2313711 : Nat := 118140960795 + 2313711 * 2 ^ 59
def prefixEnd_2313711 : Nat := 4983230072969 + 3 ^ 40 * 2313711 * 2
def baseEnd_2313711 : Nat := 1188045838594902328771943

theorem tailTrace_2313711 : CollatzResearch.WordTrace tailWord_2313711 prefixEnd_2313711 1188045838594902328771943 := by
  unfold tailWord_2313711
  simp only [CollatzResearch.WordTrace]
  refine ⟨84387972920827672224380987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56258648613885114816253991 84387972920827672224380987)
  ·
    refine ⟨126581959381241508336571481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84387972920827672224380987 126581959381241508336571481)
    ·
      refine ⟨94936469535931131252428611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126581959381241508336571481 94936469535931131252428611)
      ·
        refine ⟨142404704303896696878642917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94936469535931131252428611 142404704303896696878642917)
        ·
          refine ⟨26700882056980630664745547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 142404704303896696878642917 26700882056980630664745547)
          ·
            refine ⟨40051323085470945997118321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26700882056980630664745547 40051323085470945997118321)
            ·
              refine ⟨30038492314103209497838741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40051323085470945997118321 30038492314103209497838741)
              ·
                refine ⟨1408054327223587945211191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 30038492314103209497838741 1408054327223587945211191)
                ·
                  refine ⟨2112081490835381917816787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1408054327223587945211191 2112081490835381917816787)
                  ·
                    refine ⟨3168122236253072876725181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2112081490835381917816787 3168122236253072876725181)
                    ·
                      refine ⟨1188045838594902328771943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3168122236253072876725181 1188045838594902328771943)
                      ·
                        rfl

theorem cell23_2313711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 6, 1, 1, 3].length) (baseStart_2313711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2313711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2313711 prefixEnd_2313711 := by exact prefixLift 2313711
  have htrace : WordTrace (prefixWord ++ tailWord_2313711) baseStart_2313711 baseEnd_2313711 := by
    simpa [prefixWord, tailWord_2313711, baseEnd_2313711] using wordTrace_append hprefix tailTrace_2313711
  have hstable : (prefixWord ++ tailWord_2313711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2313711).length < 2 ^ (prefixWord ++ tailWord_2313711).sum := by decide
  have hdescent : baseEnd_2313711 < baseStart_2313711 := by decide
  rcases family_descends (prefixWord ++ tailWord_2313711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2313727 : List Nat := [1, 1, 2, 2, 1, 2, 2, 2, 6, 4]
def baseStart_2313727 : Nat := 118140960795 + 2313727 * 2 ^ 59
def prefixEnd_2313727 : Nat := 4983230072969 + 3 ^ 40 * 2313727 * 2
def baseEnd_2313727 : Nat := 396018018095124755390623

theorem tailTrace_2313727 : CollatzResearch.WordTrace tailWord_2313727 prefixEnd_2313727 396018018095124755390623 := by
  unfold tailWord_2313727
  simp only [CollatzResearch.WordTrace]
  refine ⟨84388556488769706956963435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56259037659179804637975623 84388556488769706956963435)
  ·
    refine ⟨126582834733154560435445153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84388556488769706956963435 126582834733154560435445153)
    ·
      refine ⟨94937126049865920326583865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126582834733154560435445153 94937126049865920326583865)
      ·
        refine ⟨71202844537399440244937899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94937126049865920326583865 71202844537399440244937899)
        ·
          refine ⟨106804266806099160367406849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71202844537399440244937899 106804266806099160367406849)
          ·
            refine ⟨80103200104574370275555137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 106804266806099160367406849 80103200104574370275555137)
            ·
              refine ⟨60077400078430777706666353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80103200104574370275555137 60077400078430777706666353)
              ·
                refine ⟨45058050058823083279999765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60077400078430777706666353 45058050058823083279999765)
                ·
                  refine ⟨2112096096507332028749989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 45058050058823083279999765 2112096096507332028749989)
                  ·
                    refine ⟨396018018095124755390623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2112096096507332028749989 396018018095124755390623)
                    ·
                      rfl

theorem cell23_2313727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 2, 6, 4].length) (baseStart_2313727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2313727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2313727 prefixEnd_2313727 := by exact prefixLift 2313727
  have htrace : WordTrace (prefixWord ++ tailWord_2313727) baseStart_2313727 baseEnd_2313727 := by
    simpa [prefixWord, tailWord_2313727, baseEnd_2313727] using wordTrace_append hprefix tailTrace_2313727
  have hstable : (prefixWord ++ tailWord_2313727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2313727).length < 2 ^ (prefixWord ++ tailWord_2313727).sum := by decide
  have hdescent : baseEnd_2313727 < baseStart_2313727 := by decide
  rcases family_descends (prefixWord ++ tailWord_2313727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2313747 : List Nat := [1, 1, 1, 2, 1, 6, 1, 1, 3, 2, 4]
def baseStart_2313747 : Nat := 118140960795 + 2313747 * 2 ^ 59
def prefixEnd_2313747 : Nat := 4983230072969 + 3 ^ 40 * 2313747 * 2
def baseEnd_2313747 : Nat := 1188064323898464187921777

theorem tailTrace_2313747 : CollatzResearch.WordTrace tailWord_2313747 prefixEnd_2313747 1188064323898464187921777 := by
  unfold tailWord_2313747
  simp only [CollatzResearch.WordTrace]
  refine ⟨84389285948697250372691495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56259523965798166915127663 84389285948697250372691495)
  ·
    refine ⟨126583928923045875559037243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84389285948697250372691495 126583928923045875559037243)
    ·
      refine ⟨189875893384568813338555865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126583928923045875559037243 189875893384568813338555865)
      ·
        refine ⟨142406920038426610003916899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 189875893384568813338555865 142406920038426610003916899)
        ·
          refine ⟨213610380057639915005875349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142406920038426610003916899 213610380057639915005875349)
          ·
            refine ⟨10012986565201871015900407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 213610380057639915005875349 10012986565201871015900407)
            ·
              refine ⟨15019479847802806523850611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10012986565201871015900407 15019479847802806523850611)
              ·
                refine ⟨22529219771704209785775917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15019479847802806523850611 22529219771704209785775917)
                ·
                  refine ⟨8448457414389078669665969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22529219771704209785775917 8448457414389078669665969)
                  ·
                    refine ⟨6336343060791809002249477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8448457414389078669665969 6336343060791809002249477)
                    ·
                      refine ⟨1188064323898464187921777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6336343060791809002249477 1188064323898464187921777)
                      ·
                        rfl

theorem cell23_2313747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 1, 3, 2, 4].length) (baseStart_2313747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2313747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2313747 prefixEnd_2313747 := by exact prefixLift 2313747
  have htrace : WordTrace (prefixWord ++ tailWord_2313747) baseStart_2313747 baseEnd_2313747 := by
    simpa [prefixWord, tailWord_2313747, baseEnd_2313747] using wordTrace_append hprefix tailTrace_2313747
  have hstable : (prefixWord ++ tailWord_2313747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2313747).length < 2 ^ (prefixWord ++ tailWord_2313747).sum := by decide
  have hdescent : baseEnd_2313747 < baseStart_2313747 := by decide
  rcases family_descends (prefixWord ++ tailWord_2313747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2313761 : List Nat := [1, 2, 3, 2, 2, 3, 2, 2, 2, 4]
def baseStart_2313761 : Nat := 118140960795 + 2313761 * 2 ^ 59
def prefixEnd_2313761 : Nat := 4983230072969 + 3 ^ 40 * 2313761 * 2
def baseEnd_2313761 : Nat := 396023837542542377715571

theorem tailTrace_2313761 : CollatzResearch.WordTrace tailWord_2313761 prefixEnd_2313761 396023837542542377715571 := by
  unfold tailWord_2313761
  simp only [CollatzResearch.WordTrace]
  refine ⟨84389796570646530763701137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56259864380431020509134091 84389796570646530763701137)
  ·
    refine ⟨63292347427984898072775853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84389796570646530763701137 63292347427984898072775853)
    ·
      refine ⟨23734630285494336777290945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63292347427984898072775853 23734630285494336777290945)
      ·
        refine ⟨17800972714120752582968209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23734630285494336777290945 17800972714120752582968209)
        ·
          refine ⟨13350729535590564437226157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17800972714120752582968209 13350729535590564437226157)
          ·
            refine ⟨5006523575846461663959809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13350729535590564437226157 5006523575846461663959809)
            ·
              refine ⟨3754892681884846247969857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5006523575846461663959809 3754892681884846247969857)
              ·
                refine ⟨2816169511413634685977393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3754892681884846247969857 2816169511413634685977393)
                ·
                  refine ⟨2112127133560226014483045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2816169511413634685977393 2112127133560226014483045)
                  ·
                    refine ⟨396023837542542377715571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2112127133560226014483045 396023837542542377715571)
                    ·
                      rfl

theorem cell23_2313761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 2, 2, 2, 4].length) (baseStart_2313761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2313761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2313761 prefixEnd_2313761 := by exact prefixLift 2313761
  have htrace : WordTrace (prefixWord ++ tailWord_2313761) baseStart_2313761 baseEnd_2313761 := by
    simpa [prefixWord, tailWord_2313761, baseEnd_2313761] using wordTrace_append hprefix tailTrace_2313761
  have hstable : (prefixWord ++ tailWord_2313761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2313761).length < 2 ^ (prefixWord ++ tailWord_2313761).sum := by decide
  have hdescent : baseEnd_2313761 < baseStart_2313761 := by decide
  rcases family_descends (prefixWord ++ tailWord_2313761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2313774 : List Nat := [4, 1, 3, 1, 2, 1, 3, 8]
def baseStart_2313774 : Nat := 118140960795 + 2313774 * 2 ^ 59
def prefixEnd_2313774 : Nat := 4983230072969 + 3 ^ 40 * 2313774 * 2
def baseEnd_2313774 : Nat := 44002895847264280825339

theorem tailTrace_2313774 : CollatzResearch.WordTrace tailWord_2313774 prefixEnd_2313774 44002895847264280825339 := by
  unfold tailWord_2313774
  simp only [CollatzResearch.WordTrace]
  refine ⟨10548783839949929247990547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56260180479732955989282917 10548783839949929247990547)
  ·
    refine ⟨15823175759924893871985821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10548783839949929247990547 15823175759924893871985821)
    ·
      refine ⟨5933690909971835201994683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15823175759924893871985821 5933690909971835201994683)
      ·
        refine ⟨8900536364957752802992025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5933690909971835201994683 8900536364957752802992025)
        ·
          refine ⟨6675402273718314602244019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8900536364957752802992025 6675402273718314602244019)
          ·
            refine ⟨10013103410577471903366029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6675402273718314602244019 10013103410577471903366029)
            ·
              refine ⟨3754913778966551963762261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10013103410577471903366029 3754913778966551963762261)
              ·
                refine ⟨44002895847264280825339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3754913778966551963762261 44002895847264280825339)
                ·
                  rfl

theorem cell23_2313774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 3, 8].length) (baseStart_2313774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2313774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2313774 prefixEnd_2313774 := by exact prefixLift 2313774
  have htrace : WordTrace (prefixWord ++ tailWord_2313774) baseStart_2313774 baseEnd_2313774 := by
    simpa [prefixWord, tailWord_2313774, baseEnd_2313774] using wordTrace_append hprefix tailTrace_2313774
  have hstable : (prefixWord ++ tailWord_2313774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2313774).length < 2 ^ (prefixWord ++ tailWord_2313774).sum := by decide
  have hdescent : baseEnd_2313774 < baseStart_2313774 := by decide
  rcases family_descends (prefixWord ++ tailWord_2313774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2313784 : List Nat := [2, 1, 2, 1, 4, 2, 1, 3, 1, 3, 3]
def baseStart_2313784 : Nat := 118140960795 + 2313784 * 2 ^ 59
def prefixEnd_2313784 : Nat := 4983230072969 + 3 ^ 40 * 2313784 * 2
def baseEnd_2313784 : Nat := 1188083322682680543159107

theorem tailTrace_2313784 : CollatzResearch.WordTrace tailWord_2313784 prefixEnd_2313784 1188083322682680543159107 := by
  unfold tailWord_2313784
  simp only [CollatzResearch.WordTrace]
  refine ⟨42195317724781602845894203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56260423633042137127858937 42195317724781602845894203)
  ·
    refine ⟨63292976587172404268841305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42195317724781602845894203 63292976587172404268841305)
    ·
      refine ⟨47469732440379303201630979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63292976587172404268841305 47469732440379303201630979)
      ·
        refine ⟨71204598660568954802446469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47469732440379303201630979 71204598660568954802446469)
        ·
          refine ⟨13350862248856679025458713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 71204598660568954802446469 13350862248856679025458713)
          ·
            refine ⟨10013146686642509269094035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13350862248856679025458713 10013146686642509269094035)
            ·
              refine ⟨15019720029963763903641053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10013146686642509269094035 15019720029963763903641053)
              ·
                refine ⟨5632395011236411463865395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15019720029963763903641053 5632395011236411463865395)
                ·
                  refine ⟨8448592516854617195798093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5632395011236411463865395 8448592516854617195798093)
                  ·
                    refine ⟨3168222193820481448424285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8448592516854617195798093 3168222193820481448424285)
                    ·
                      refine ⟨1188083322682680543159107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3168222193820481448424285 1188083322682680543159107)
                      ·
                        rfl

theorem cell23_2313784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 3, 1, 3, 3].length) (baseStart_2313784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2313784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2313784 prefixEnd_2313784 := by exact prefixLift 2313784
  have htrace : WordTrace (prefixWord ++ tailWord_2313784) baseStart_2313784 baseEnd_2313784 := by
    simpa [prefixWord, tailWord_2313784, baseEnd_2313784] using wordTrace_append hprefix tailTrace_2313784
  have hstable : (prefixWord ++ tailWord_2313784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2313784).length < 2 ^ (prefixWord ++ tailWord_2313784).sum := by decide
  have hdescent : baseEnd_2313784 < baseStart_2313784 := by decide
  rcases family_descends (prefixWord ++ tailWord_2313784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2313797 : List Nat := [1, 3, 1, 1, 1, 4, 2, 1, 2, 2, 5]
def baseStart_2313797 : Nat := 118140960795 + 2313797 * 2 ^ 59
def prefixEnd_2313797 : Nat := 4983230072969 + 3 ^ 40 * 2313797 * 2
def baseEnd_2313797 : Nat := 1188089997931188992296547

theorem tailTrace_2313797 : CollatzResearch.WordTrace tailWord_2313797 prefixEnd_2313797 1188089997931188992296547 := by
  unfold tailWord_2313797
  simp only [CollatzResearch.WordTrace]
  refine ⟨84391109598516108912011645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56260739732344072608007763 84391109598516108912011645)
  ·
    refine ⟨31646666099443540842004367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84391109598516108912011645 31646666099443540842004367)
    ·
      refine ⟨47469999149165311263006551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31646666099443540842004367 47469999149165311263006551)
      ·
        refine ⟨71204998723747966894509827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47469999149165311263006551 71204998723747966894509827)
        ·
          refine ⟨106807498085621950341764741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71204998723747966894509827 106807498085621950341764741)
          ·
            refine ⟨20026405891054115689080889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 106807498085621950341764741 20026405891054115689080889)
            ·
              refine ⟨15019804418290586766810667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20026405891054115689080889 15019804418290586766810667)
              ·
                refine ⟨22529706627435880150216001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15019804418290586766810667 22529706627435880150216001)
                ·
                  refine ⟨16897279970576910112662001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22529706627435880150216001 16897279970576910112662001)
                  ·
                    refine ⟨12672959977932682584496501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16897279970576910112662001 12672959977932682584496501)
                    ·
                      refine ⟨1188089997931188992296547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12672959977932682584496501 1188089997931188992296547)
                      ·
                        rfl

theorem cell23_2313797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 1, 2, 2, 5].length) (baseStart_2313797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2313797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2313797 prefixEnd_2313797 := by exact prefixLift 2313797
  have htrace : WordTrace (prefixWord ++ tailWord_2313797) baseStart_2313797 baseEnd_2313797 := by
    simpa [prefixWord, tailWord_2313797, baseEnd_2313797] using wordTrace_append hprefix tailTrace_2313797
  have hstable : (prefixWord ++ tailWord_2313797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2313797).length < 2 ^ (prefixWord ++ tailWord_2313797).sum := by decide
  have hdescent : baseEnd_2313797 < baseStart_2313797 := by decide
  rcases family_descends (prefixWord ++ tailWord_2313797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2313834 : List Nat := [3, 1, 3, 2, 1, 2, 2, 1, 2, 6]
def baseStart_2313834 : Nat := 118140960795 + 2313834 * 2 ^ 59
def prefixEnd_2313834 : Nat := 4983230072969 + 3 ^ 40 * 2313834 * 2
def baseEnd_2313834 : Nat := 396036332238468449177959

theorem tailTrace_2313834 : CollatzResearch.WordTrace tailWord_2313834 prefixEnd_2313834 396036332238468449177959 := by
  unfold tailWord_2313834
  simp only [CollatzResearch.WordTrace]
  refine ⟨21098114774845516057777139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56261639399588042820739037 21098114774845516057777139)
  ·
    refine ⟨31647172162268274086665709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21098114774845516057777139 31647172162268274086665709)
    ·
      refine ⟨11867689560850602782499641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31647172162268274086665709 11867689560850602782499641)
      ·
        refine ⟨8900767170637952086874731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11867689560850602782499641 8900767170637952086874731)
        ·
          refine ⟨13351150755956928130312097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8900767170637952086874731 13351150755956928130312097)
          ·
            refine ⟨10013363066967696097734073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13351150755956928130312097 10013363066967696097734073)
            ·
              refine ⟨7510022300225772073300555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10013363066967696097734073 7510022300225772073300555)
              ·
                refine ⟨11265033450338658109950833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7510022300225772073300555 11265033450338658109950833)
                ·
                  refine ⟨8448775087753993582463125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11265033450338658109950833 8448775087753993582463125)
                  ·
                    refine ⟨396036332238468449177959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8448775087753993582463125 396036332238468449177959)
                    ·
                      rfl

theorem cell23_2313834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 2, 1, 2, 6].length) (baseStart_2313834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2313834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2313834 prefixEnd_2313834 := by exact prefixLift 2313834
  have htrace : WordTrace (prefixWord ++ tailWord_2313834) baseStart_2313834 baseEnd_2313834 := by
    simpa [prefixWord, tailWord_2313834, baseEnd_2313834] using wordTrace_append hprefix tailTrace_2313834
  have hstable : (prefixWord ++ tailWord_2313834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2313834).length < 2 ^ (prefixWord ++ tailWord_2313834).sum := by decide
  have hdescent : baseEnd_2313834 < baseStart_2313834 := by decide
  rcases family_descends (prefixWord ++ tailWord_2313834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2313845 : List Nat := [1, 3, 4, 2, 1, 2, 2, 2, 1, 3, 2]
def baseStart_2313845 : Nat := 118140960795 + 2313845 * 2 ^ 59
def prefixEnd_2313845 : Nat := 4983230072969 + 3 ^ 40 * 2313845 * 2
def baseEnd_2313845 : Nat := 1188114645002604804496327

theorem tailTrace_2313845 : CollatzResearch.WordTrace tailWord_2313845 prefixEnd_2313845 1188114645002604804496327 := by
  unfold tailWord_2313845
  simp only [CollatzResearch.WordTrace]
  refine ⟨84392860302342213109758989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56261906868228142073172659 84392860302342213109758989)
  ·
    refine ⟨31647322613378329916159621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84392860302342213109758989 31647322613378329916159621)
    ·
      refine ⟨5933872990008436859279929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31647322613378329916159621 5933872990008436859279929)
      ·
        refine ⟨4450404742506327644459947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5933872990008436859279929 4450404742506327644459947)
        ·
          refine ⟨6675607113759491466689921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4450404742506327644459947 6675607113759491466689921)
          ·
            refine ⟨5006705335319618600017441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6675607113759491466689921 5006705335319618600017441)
            ·
              refine ⟨3755029001489713950013081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5006705335319618600017441 3755029001489713950013081)
              ·
                refine ⟨2816271751117285462509811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3755029001489713950013081 2816271751117285462509811)
                ·
                  refine ⟨4224407626675928193764717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2816271751117285462509811 4224407626675928193764717)
                  ·
                    refine ⟨1584152860003473072661769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4224407626675928193764717 1584152860003473072661769)
                    ·
                      refine ⟨1188114645002604804496327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1584152860003473072661769 1188114645002604804496327)
                      ·
                        rfl

theorem cell23_2313845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 2, 2, 1, 3, 2].length) (baseStart_2313845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2313845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2313845 prefixEnd_2313845 := by exact prefixLift 2313845
  have htrace : WordTrace (prefixWord ++ tailWord_2313845) baseStart_2313845 baseEnd_2313845 := by
    simpa [prefixWord, tailWord_2313845, baseEnd_2313845] using wordTrace_append hprefix tailTrace_2313845
  have hstable : (prefixWord ++ tailWord_2313845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2313845).length < 2 ^ (prefixWord ++ tailWord_2313845).sum := by decide
  have hdescent : baseEnd_2313845 < baseStart_2313845 := by decide
  rcases family_descends (prefixWord ++ tailWord_2313845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2313892 : List Nat := [2, 3, 1, 2, 2, 4, 2, 1, 2, 2, 2]
def baseStart_2313892 : Nat := 118140960795 + 2313892 * 2 ^ 59
def prefixEnd_2313892 : Nat := 4983230072969 + 3 ^ 40 * 2313892 * 2
def baseEnd_2313892 : Nat := 1188138778593366120608611

theorem tailTrace_2313892 : CollatzResearch.WordTrace tailWord_2313892 prefixEnd_2313892 1188138778593366120608611 := by
  unfold tailWord_2313892
  simp only [CollatzResearch.WordTrace]
  refine ⟨42197287266585970068359965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56263049688781293424479953 42197287266585970068359965)
  ·
    refine ⟨15823982724969738775634987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42197287266585970068359965 15823982724969738775634987)
    ·
      refine ⟨23735974087454608163452481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15823982724969738775634987 23735974087454608163452481)
      ·
        refine ⟨17801980565590956122589361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23735974087454608163452481 17801980565590956122589361)
        ·
          refine ⟨13351485424193217091942021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17801980565590956122589361 13351485424193217091942021)
          ·
            refine ⟨2503403517036228204739129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13351485424193217091942021 2503403517036228204739129)
            ·
              refine ⟨1877552637777171153554347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2503403517036228204739129 1877552637777171153554347)
              ·
                refine ⟨2816328956665756730331521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1877552637777171153554347 2816328956665756730331521)
                ·
                  refine ⟨2112246717499317547748641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2816328956665756730331521 2112246717499317547748641)
                  ·
                    refine ⟨1584185038124488160811481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2112246717499317547748641 1584185038124488160811481)
                    ·
                      refine ⟨1188138778593366120608611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1584185038124488160811481 1188138778593366120608611)
                      ·
                        rfl

theorem cell23_2313892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 2, 1, 2, 2, 2].length) (baseStart_2313892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2313892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2313892 prefixEnd_2313892 := by exact prefixLift 2313892
  have htrace : WordTrace (prefixWord ++ tailWord_2313892) baseStart_2313892 baseEnd_2313892 := by
    simpa [prefixWord, tailWord_2313892, baseEnd_2313892] using wordTrace_append hprefix tailTrace_2313892
  have hstable : (prefixWord ++ tailWord_2313892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2313892).length < 2 ^ (prefixWord ++ tailWord_2313892).sum := by decide
  have hdescent : baseEnd_2313892 < baseStart_2313892 := by decide
  rcases family_descends (prefixWord ++ tailWord_2313892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2313896 : List Nat := [2, 1, 7, 1, 2, 1, 1, 2, 1, 3, 2]
def baseStart_2313896 : Nat := 118140960795 + 2313896 * 2 ^ 59
def prefixEnd_2313896 : Nat := 4983230072969 + 3 ^ 40 * 2313896 * 2
def baseEnd_2313896 : Nat := 1188140832515984104958593

theorem tailTrace_2313896 : CollatzResearch.WordTrace tailWord_2313896 prefixEnd_2313896 1188140832515984104958593 := by
  unfold tailWord_2313896
  simp only [CollatzResearch.WordTrace]
  refine ⟨42197360212578724409932771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56263146950104965879910361 42197360212578724409932771)
  ·
    refine ⟨63296040318868086614899157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42197360212578724409932771 63296040318868086614899157)
    ·
      refine ⟨1483500944973470780036699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 63296040318868086614899157 1483500944973470780036699)
      ·
        refine ⟨2225251417460206170055049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1483500944973470780036699 2225251417460206170055049)
        ·
          refine ⟨1668938563095154627541287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2225251417460206170055049 1668938563095154627541287)
          ·
            refine ⟨2503407844642731941311931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1668938563095154627541287 2503407844642731941311931)
            ·
              refine ⟨3755111766964097911967897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2503407844642731941311931 3755111766964097911967897)
              ·
                refine ⟨2816333825223073433975923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3755111766964097911967897 2816333825223073433975923)
                ·
                  refine ⟨4224500737834610150963885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2816333825223073433975923 4224500737834610150963885)
                  ·
                    refine ⟨1584187776687978806611457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4224500737834610150963885 1584187776687978806611457)
                    ·
                      refine ⟨1188140832515984104958593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1584187776687978806611457 1188140832515984104958593)
                      ·
                        rfl

theorem cell23_2313896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 1, 2, 1, 3, 2].length) (baseStart_2313896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2313896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2313896 prefixEnd_2313896 := by exact prefixLift 2313896
  have htrace : WordTrace (prefixWord ++ tailWord_2313896) baseStart_2313896 baseEnd_2313896 := by
    simpa [prefixWord, tailWord_2313896, baseEnd_2313896] using wordTrace_append hprefix tailTrace_2313896
  have hstable : (prefixWord ++ tailWord_2313896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2313896).length < 2 ^ (prefixWord ++ tailWord_2313896).sum := by decide
  have hdescent : baseEnd_2313896 < baseStart_2313896 := by decide
  rcases family_descends (prefixWord ++ tailWord_2313896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2313911 : List Nat := [1, 1, 3, 1, 5, 2, 2, 1, 2, 5]
def baseStart_2313911 : Nat := 118140960795 + 2313911 * 2 ^ 59
def prefixEnd_2313911 : Nat := 4983230072969 + 3 ^ 40 * 2313911 * 2
def baseEnd_2313911 : Nat := 396049511575267182090341

theorem tailTrace_2313911 : CollatzResearch.WordTrace tailWord_2313911 prefixEnd_2313911 396049511575267182090341 := by
  unfold tailWord_2313911
  simp only [CollatzResearch.WordTrace]
  refine ⟨84395267520103106381661587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56263511680068737587774391 84395267520103106381661587)
  ·
    refine ⟨126592901280154659572492381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84395267520103106381661587 126592901280154659572492381)
    ·
      refine ⟨47472337980057997339684643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 126592901280154659572492381 47472337980057997339684643)
      ·
        refine ⟨71208506970086996009526965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47472337980057997339684643 71208506970086996009526965)
        ·
          refine ⟨6675797528445655875893153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 71208506970086996009526965 6675797528445655875893153)
          ·
            refine ⟨5006848146334241906919865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6675797528445655875893153 5006848146334241906919865)
            ·
              refine ⟨3755136109750681430189899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5006848146334241906919865 3755136109750681430189899)
              ·
                refine ⟨5632704164626022145284849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3755136109750681430189899 5632704164626022145284849)
                ·
                  refine ⟨4224528123469516608963637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5632704164626022145284849 4224528123469516608963637)
                  ·
                    refine ⟨396049511575267182090341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4224528123469516608963637 396049511575267182090341)
                    ·
                      rfl

theorem cell23_2313911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 2, 1, 2, 5].length) (baseStart_2313911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2313911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2313911 prefixEnd_2313911 := by exact prefixLift 2313911
  have htrace : WordTrace (prefixWord ++ tailWord_2313911) baseStart_2313911 baseEnd_2313911 := by
    simpa [prefixWord, tailWord_2313911, baseEnd_2313911] using wordTrace_append hprefix tailTrace_2313911
  have hstable : (prefixWord ++ tailWord_2313911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2313911).length < 2 ^ (prefixWord ++ tailWord_2313911).sum := by decide
  have hdescent : baseEnd_2313911 < baseStart_2313911 := by decide
  rcases family_descends (prefixWord ++ tailWord_2313911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2313932 : List Nat := [2, 2, 1, 5, 3, 1, 2, 2, 5]
def baseStart_2313932 : Nat := 118140960795 + 2313932 * 2 ^ 59
def prefixEnd_2313932 : Nat := 4983230072969 + 3 ^ 40 * 2313932 * 2
def baseEnd_2313932 : Nat := 132017701979949551567603

theorem tailTrace_2313932 : CollatzResearch.WordTrace tailWord_2313932 prefixEnd_2313932 132017701979949551567603 := by
  unfold tailWord_2313932
  simp only [CollatzResearch.WordTrace]
  refine ⟨42198016726513513484088025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56264022302018017978784033 42198016726513513484088025)
  ·
    refine ⟨31648512544885135113066019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42198016726513513484088025 31648512544885135113066019)
    ·
      refine ⟨47472768817327702669599029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31648512544885135113066019 47472768817327702669599029)
      ·
        refine ⟨4450572076624472125274909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 47472768817327702669599029 4450572076624472125274909)
        ·
          refine ⟨1668964528734177046978091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4450572076624472125274909 1668964528734177046978091)
          ·
            refine ⟨2503446793101265570467137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1668964528734177046978091 2503446793101265570467137)
            ·
              refine ⟨1877585094825949177850353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2503446793101265570467137 1877585094825949177850353)
              ·
                refine ⟨1408188821119461883387765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1877585094825949177850353 1408188821119461883387765)
                ·
                  refine ⟨132017701979949551567603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1408188821119461883387765 132017701979949551567603)
                  ·
                    rfl

theorem cell23_2313932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 2, 2, 5].length) (baseStart_2313932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2313932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2313932 prefixEnd_2313932 := by exact prefixLift 2313932
  have htrace : WordTrace (prefixWord ++ tailWord_2313932) baseStart_2313932 baseEnd_2313932 := by
    simpa [prefixWord, tailWord_2313932, baseEnd_2313932] using wordTrace_append hprefix tailTrace_2313932
  have hstable : (prefixWord ++ tailWord_2313932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2313932).length < 2 ^ (prefixWord ++ tailWord_2313932).sum := by decide
  have hdescent : baseEnd_2313932 < baseStart_2313932 := by decide
  rcases family_descends (prefixWord ++ tailWord_2313932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2313934 : List Nat := [4, 1, 1, 1, 3, 1, 1, 1, 2, 3, 5]
def baseStart_2313934 : Nat := 118140960795 + 2313934 * 2 ^ 59
def prefixEnd_2313934 : Nat := 4983230072969 + 3 ^ 40 * 2313934 * 2
def baseEnd_2313934 : Nat := 1188160344780854956283417

theorem tailTrace_2313934 : CollatzResearch.WordTrace tailWord_2313934 prefixEnd_2313934 1188160344780854956283417 := by
  unfold tailWord_2313934
  simp only [CollatzResearch.WordTrace]
  refine ⟨10549513299877472663718607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56264070932679854206499237 10549513299877472663718607)
  ·
    refine ⟨15824269949816208995577911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10549513299877472663718607 15824269949816208995577911)
    ·
      refine ⟨23736404924724313493366867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15824269949816208995577911 23736404924724313493366867)
      ·
        refine ⟨35604607387086470240050301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23736404924724313493366867 35604607387086470240050301)
        ·
          refine ⟨13351727770157426340018863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35604607387086470240050301 13351727770157426340018863)
          ·
            refine ⟨20027591655236139510028295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13351727770157426340018863 20027591655236139510028295)
            ·
              refine ⟨30041387482854209265042443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20027591655236139510028295 30041387482854209265042443)
              ·
                refine ⟨45062081224281313897563665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30041387482854209265042443 45062081224281313897563665)
                ·
                  refine ⟨33796560918210985423172749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45062081224281313897563665 33796560918210985423172749)
                  ·
                    refine ⟨12673710344329119533689781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 33796560918210985423172749 12673710344329119533689781)
                    ·
                      refine ⟨1188160344780854956283417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12673710344329119533689781 1188160344780854956283417)
                      ·
                        rfl

theorem cell23_2313934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 1, 2, 3, 5].length) (baseStart_2313934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2313934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2313934 prefixEnd_2313934 := by exact prefixLift 2313934
  have htrace : WordTrace (prefixWord ++ tailWord_2313934) baseStart_2313934 baseEnd_2313934 := by
    simpa [prefixWord, tailWord_2313934, baseEnd_2313934] using wordTrace_append hprefix tailTrace_2313934
  have hstable : (prefixWord ++ tailWord_2313934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2313934).length < 2 ^ (prefixWord ++ tailWord_2313934).sum := by decide
  have hdescent : baseEnd_2313934 < baseStart_2313934 := by decide
  rcases family_descends (prefixWord ++ tailWord_2313934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2313988 : List Nat := [2, 3, 2, 2, 1, 4, 1, 2, 6]
def baseStart_2313988 : Nat := 118140960795 + 2313988 * 2 ^ 59
def prefixEnd_2313988 : Nat := 4983230072969 + 3 ^ 40 * 2313988 * 2
def baseEnd_2313988 : Nat := 132020896970688638334241

theorem tailTrace_2313988 : CollatzResearch.WordTrace tailWord_2313988 prefixEnd_2313988 132020896970688638334241 := by
  unfold tailWord_2313988
  simp only [CollatzResearch.WordTrace]
  refine ⟨42199037970412074266107309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56265383960549432354809745 42199037970412074266107309)
  ·
    refine ⟨15824639238904527849790241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42199037970412074266107309 15824639238904527849790241)
    ·
      refine ⟨11868479429178395887342681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15824639238904527849790241 11868479429178395887342681)
      ·
        refine ⟨8901359571883796915507011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11868479429178395887342681 8901359571883796915507011)
        ·
          refine ⟨13352039357825695373260517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8901359571883796915507011 13352039357825695373260517)
          ·
            refine ⟨2503507379592317882486347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13352039357825695373260517 2503507379592317882486347)
            ·
              refine ⟨3755261069388476823729521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2503507379592317882486347 3755261069388476823729521)
              ·
                refine ⟨2816445802041357617797141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3755261069388476823729521 2816445802041357617797141)
                ·
                  refine ⟨132020896970688638334241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2816445802041357617797141 132020896970688638334241)
                  ·
                    rfl

theorem cell23_2313988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 1, 2, 6].length) (baseStart_2313988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2313988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2313988 prefixEnd_2313988 := by exact prefixLift 2313988
  have htrace : WordTrace (prefixWord ++ tailWord_2313988) baseStart_2313988 baseEnd_2313988 := by
    simpa [prefixWord, tailWord_2313988, baseEnd_2313988] using wordTrace_append hprefix tailTrace_2313988
  have hstable : (prefixWord ++ tailWord_2313988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2313988).length < 2 ^ (prefixWord ++ tailWord_2313988).sum := by decide
  have hdescent : baseEnd_2313988 < baseStart_2313988 := by decide
  rcases family_descends (prefixWord ++ tailWord_2313988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2313998 : List Nat := [4, 1, 1, 2, 1, 1, 3, 3, 3, 1, 3]
def baseStart_2313998 : Nat := 118140960795 + 2313998 * 2 ^ 59
def prefixEnd_2313998 : Nat := 4983230072969 + 3 ^ 40 * 2313998 * 2
def baseEnd_2313998 : Nat := 1188193207542742705883123

theorem tailTrace_2313998 : CollatzResearch.WordTrace tailWord_2313998 prefixEnd_2313998 1188193207542742705883123 := by
  unfold tailWord_2313998
  simp only [CollatzResearch.WordTrace]
  refine ⟨10549805083848490030009831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56265627113858613493385765 10549805083848490030009831)
  ·
    refine ⟨15824707625772735045014747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10549805083848490030009831 15824707625772735045014747)
    ·
      refine ⟨23737061438659102567522121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15824707625772735045014747 23737061438659102567522121)
      ·
        refine ⟨17802796078994326925641591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23737061438659102567522121 17802796078994326925641591)
        ·
          refine ⟨26704194118491490388462387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17802796078994326925641591 26704194118491490388462387)
          ·
            refine ⟨40056291177737235582693581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26704194118491490388462387 40056291177737235582693581)
            ·
              refine ⟨15021109191651463343510093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40056291177737235582693581 15021109191651463343510093)
              ·
                refine ⟨5632915946869298753816285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15021109191651463343510093 5632915946869298753816285)
                ·
                  refine ⟨2112343480075987032681107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5632915946869298753816285 2112343480075987032681107)
                  ·
                    refine ⟨3168515220113980549021661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2112343480075987032681107 3168515220113980549021661)
                    ·
                      refine ⟨1188193207542742705883123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3168515220113980549021661 1188193207542742705883123)
                      ·
                        rfl

theorem cell23_2313998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 3, 3, 1, 3].length) (baseStart_2313998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2313998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2313998 prefixEnd_2313998 := by exact prefixLift 2313998
  have htrace : WordTrace (prefixWord ++ tailWord_2313998) baseStart_2313998 baseEnd_2313998 := by
    simpa [prefixWord, tailWord_2313998, baseEnd_2313998] using wordTrace_append hprefix tailTrace_2313998
  have hstable : (prefixWord ++ tailWord_2313998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2313998).length < 2 ^ (prefixWord ++ tailWord_2313998).sum := by decide
  have hdescent : baseEnd_2313998 < baseStart_2313998 := by decide
  rcases family_descends (prefixWord ++ tailWord_2313998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2314018 : List Nat := [3, 3, 1, 1, 2, 1, 4, 2, 1, 5]
def baseStart_2314018 : Nat := 118140960795 + 2314018 * 2 ^ 59
def prefixEnd_2314018 : Nat := 4983230072969 + 3 ^ 40 * 2314018 * 2
def baseEnd_2314018 : Nat := 396067825718610875877677

theorem tailTrace_2314018 : CollatzResearch.WordTrace tailWord_2314018 prefixEnd_2314018 396067825718610875877677 := by
  unfold tailWord_2314018
  simp only [CollatzResearch.WordTrace]
  refine ⟨21099792532678865913951677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56266113420476975770537805 21099792532678865913951677)
  ·
    refine ⟨7912422199754574717731879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21099792532678865913951677 7912422199754574717731879)
    ·
      refine ⟨11868633299631862076597819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7912422199754574717731879 11868633299631862076597819)
      ·
        refine ⟨17802949949447793114896729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11868633299631862076597819 17802949949447793114896729)
        ·
          refine ⟨13352212462085844836172547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17802949949447793114896729 13352212462085844836172547)
          ·
            refine ⟨20028318693128767254258821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13352212462085844836172547 20028318693128767254258821)
            ·
              refine ⟨3755309754961643860173529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20028318693128767254258821 3755309754961643860173529)
              ·
                refine ⟨2816482316221232895130147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3755309754961643860173529 2816482316221232895130147)
                ·
                  refine ⟨4224723474331849342695221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2816482316221232895130147 4224723474331849342695221)
                  ·
                    refine ⟨396067825718610875877677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4224723474331849342695221 396067825718610875877677)
                    ·
                      rfl

theorem cell23_2314018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 4, 2, 1, 5].length) (baseStart_2314018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2314018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2314018 prefixEnd_2314018 := by exact prefixLift 2314018
  have htrace : WordTrace (prefixWord ++ tailWord_2314018) baseStart_2314018 baseEnd_2314018 := by
    simpa [prefixWord, tailWord_2314018, baseEnd_2314018] using wordTrace_append hprefix tailTrace_2314018
  have hstable : (prefixWord ++ tailWord_2314018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2314018).length < 2 ^ (prefixWord ++ tailWord_2314018).sum := by decide
  have hdescent : baseEnd_2314018 < baseStart_2314018 := by decide
  rcases family_descends (prefixWord ++ tailWord_2314018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2314044 : List Nat := [2, 2, 2, 2, 1, 1, 13]
def baseStart_2314044 : Nat := 118140960795 + 2314044 * 2 ^ 59
def prefixEnd_2314044 : Nat := 4983230072969 + 3 ^ 40 * 2314044 * 2
def baseEnd_2314044 : Nat := 14669343551269747233431

theorem tailTrace_2314044 : CollatzResearch.WordTrace tailWord_2314044 prefixEnd_2314044 14669343551269747233431 := by
  unfold tailWord_2314044
  simp only [CollatzResearch.WordTrace]
  refine ⟨42200059214310635048126593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56266745619080846730835457 42200059214310635048126593)
  ·
    refine ⟨31650044410732976286094945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42200059214310635048126593 31650044410732976286094945)
    ·
      refine ⟨23737533308049732214571209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31650044410732976286094945 23737533308049732214571209)
      ·
        refine ⟨17803149981037299160928407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23737533308049732214571209 17803149981037299160928407)
        ·
          refine ⟨26704724971555948741392611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17803149981037299160928407 26704724971555948741392611)
          ·
            refine ⟨40057087457333923112088917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26704724971555948741392611 40057087457333923112088917)
            ·
              refine ⟨14669343551269747233431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 40057087457333923112088917 14669343551269747233431)
              ·
                rfl

theorem cell23_2314044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 13].length) (baseStart_2314044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2314044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2314044 prefixEnd_2314044 := by exact prefixLift 2314044
  have htrace : WordTrace (prefixWord ++ tailWord_2314044) baseStart_2314044 baseEnd_2314044 := by
    simpa [prefixWord, tailWord_2314044, baseEnd_2314044] using wordTrace_append hprefix tailTrace_2314044
  have hstable : (prefixWord ++ tailWord_2314044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2314044).length < 2 ^ (prefixWord ++ tailWord_2314044).sum := by decide
  have hdescent : baseEnd_2314044 < baseStart_2314044 := by decide
  rcases family_descends (prefixWord ++ tailWord_2314044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2314055 : List Nat := [1, 1, 4, 1, 2, 1, 5, 1, 3, 2, 2]
def baseStart_2314055 : Nat := 118140960795 + 2314055 * 2 ^ 59
def prefixEnd_2314055 : Nat := 4983230072969 + 3 ^ 40 * 2314055 * 2
def baseEnd_2314055 : Nat := 1188222475940048982870361

theorem tailTrace_2314055 : CollatzResearch.WordTrace tailWord_2314055 prefixEnd_2314055 1188222475940048982870361 := by
  unfold tailWord_2314055
  simp only [CollatzResearch.WordTrace]
  refine ⟨84400519631581418974903619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56267013087720945983269079 84400519631581418974903619)
  ·
    refine ⟨126600779447372128462355429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84400519631581418974903619 126600779447372128462355429)
    ·
      refine ⟨23737646146382274086691643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 126600779447372128462355429 23737646146382274086691643)
      ·
        refine ⟨35606469219573411130037465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23737646146382274086691643 35606469219573411130037465)
        ·
          refine ⟨26704851914680058347528099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35606469219573411130037465 26704851914680058347528099)
          ·
            refine ⟨40057277872020087521292149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26704851914680058347528099 40057277872020087521292149)
            ·
              refine ⟨3755369800501883205121139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 40057277872020087521292149 3755369800501883205121139)
              ·
                refine ⟨5633054700752824807681709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3755369800501883205121139 5633054700752824807681709)
                ·
                  refine ⟨2112395512782309302880641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5633054700752824807681709 2112395512782309302880641)
                  ·
                    refine ⟨1584296634586731977160481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2112395512782309302880641 1584296634586731977160481)
                    ·
                      refine ⟨1188222475940048982870361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1584296634586731977160481 1188222475940048982870361)
                      ·
                        rfl

theorem cell23_2314055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 5, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 5, 1, 3, 2, 2].length) (baseStart_2314055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2314055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2314055 prefixEnd_2314055 := by exact prefixLift 2314055
  have htrace : WordTrace (prefixWord ++ tailWord_2314055) baseStart_2314055 baseEnd_2314055 := by
    simpa [prefixWord, tailWord_2314055, baseEnd_2314055] using wordTrace_append hprefix tailTrace_2314055
  have hstable : (prefixWord ++ tailWord_2314055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2314055).length < 2 ^ (prefixWord ++ tailWord_2314055).sum := by decide
  have hdescent : baseEnd_2314055 < baseStart_2314055 := by decide
  rcases family_descends (prefixWord ++ tailWord_2314055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2314064 : List Nat := [2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 6]
def baseStart_2314064 : Nat := 118140960795 + 2314064 * 2 ^ 59
def prefixEnd_2314064 : Nat := 4983230072969 + 3 ^ 40 * 2314064 * 2
def baseEnd_2314064 : Nat := 1188227097265939447657819

theorem tailTrace_2314064 : CollatzResearch.WordTrace tailWord_2314064 prefixEnd_2314064 1188227097265939447657819 := by
  unfold tailWord_2314064
  simp only [CollatzResearch.WordTrace]
  refine ⟨42200423944274406755990623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56267231925699209007987497 42200423944274406755990623)
  ·
    refine ⟨63300635916411610133985935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42200423944274406755990623 63300635916411610133985935)
    ·
      refine ⟨94950953874617415200978903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63300635916411610133985935 94950953874617415200978903)
      ·
        refine ⟨142426430811926122801468355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94950953874617415200978903 142426430811926122801468355)
        ·
          refine ⟨213639646217889184202202533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142426430811926122801468355 213639646217889184202202533)
          ·
            refine ⟨40057433665854222037912975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 213639646217889184202202533 40057433665854222037912975)
            ·
              refine ⟨60086150498781333056869463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40057433665854222037912975 60086150498781333056869463)
              ·
                refine ⟨90129225748171999585304195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60086150498781333056869463 90129225748171999585304195)
                ·
                  refine ⟨135193838622257999377956293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 90129225748171999585304195 135193838622257999377956293)
                  ·
                    refine ⟨25348844741673374883366805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 135193838622257999377956293 25348844741673374883366805)
                    ·
                      refine ⟨1188227097265939447657819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 25348844741673374883366805 1188227097265939447657819)
                      ·
                        rfl

theorem cell23_2314064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 6].length) (baseStart_2314064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2314064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2314064 prefixEnd_2314064 := by exact prefixLift 2314064
  have htrace : WordTrace (prefixWord ++ tailWord_2314064) baseStart_2314064 baseEnd_2314064 := by
    simpa [prefixWord, tailWord_2314064, baseEnd_2314064] using wordTrace_append hprefix tailTrace_2314064
  have hstable : (prefixWord ++ tailWord_2314064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2314064).length < 2 ^ (prefixWord ++ tailWord_2314064).sum := by decide
  have hdescent : baseEnd_2314064 < baseStart_2314064 := by decide
  rcases family_descends (prefixWord ++ tailWord_2314064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2314065 : List Nat := [1, 2, 2, 1, 5, 1, 4, 1, 2, 4]
def baseStart_2314065 : Nat := 118140960795 + 2314065 * 2 ^ 59
def prefixEnd_2314065 : Nat := 4983230072969 + 3 ^ 40 * 2314065 * 2
def baseEnd_2314065 : Nat := 396075870248864647915105

theorem tailTrace_2314065 : CollatzResearch.WordTrace tailWord_2314065 prefixEnd_2314065 396075870248864647915105 := by
  unfold tailWord_2314065
  simp only [CollatzResearch.WordTrace]
  refine ⟨84400884361545190682767649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56267256241030127121845099 84400884361545190682767649)
  ·
    refine ⟨63300663271158893012075737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84400884361545190682767649 63300663271158893012075737)
    ·
      refine ⟨47475497453369169759056803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63300663271158893012075737 47475497453369169759056803)
      ·
        refine ⟨71213246180053754638585205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47475497453369169759056803 71213246180053754638585205)
        ·
          refine ⟨6676241829380039497367363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 71213246180053754638585205 6676241829380039497367363)
          ·
            refine ⟨10014362744070059246051045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6676241829380039497367363 10014362744070059246051045)
            ·
              refine ⟨1877693014513136108634571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10014362744070059246051045 1877693014513136108634571)
              ·
                refine ⟨2816539521769704162951857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1877693014513136108634571 2816539521769704162951857)
                ·
                  refine ⟨2112404641327278122213893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2816539521769704162951857 2112404641327278122213893)
                  ·
                    refine ⟨396075870248864647915105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2112404641327278122213893 396075870248864647915105)
                    ·
                      rfl

theorem cell23_2314065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 4, 1, 2, 4].length) (baseStart_2314065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2314065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2314065 prefixEnd_2314065 := by exact prefixLift 2314065
  have htrace : WordTrace (prefixWord ++ tailWord_2314065) baseStart_2314065 baseEnd_2314065 := by
    simpa [prefixWord, tailWord_2314065, baseEnd_2314065] using wordTrace_append hprefix tailTrace_2314065
  have hstable : (prefixWord ++ tailWord_2314065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2314065).length < 2 ^ (prefixWord ++ tailWord_2314065).sum := by decide
  have hdescent : baseEnd_2314065 < baseStart_2314065 := by decide
  rcases family_descends (prefixWord ++ tailWord_2314065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2314088 : List Nat := [2, 1, 4, 2, 1, 1, 3, 2, 1, 3, 3]
def baseStart_2314088 : Nat := 118140960795 + 2314088 * 2 ^ 59
def prefixEnd_2314088 : Nat := 4983230072969 + 3 ^ 40 * 2314088 * 2
def baseEnd_2314088 : Nat := 1188239420801647353757709

theorem tailTrace_2314088 : CollatzResearch.WordTrace tailWord_2314088 prefixEnd_2314088 1188239420801647353757709 := by
  unfold tailWord_2314088
  simp only [CollatzResearch.WordTrace]
  refine ⟨42200861620230932805427459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56267815493641243740569945 42200861620230932805427459)
  ·
    refine ⟨63301292430346399208141189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42200861620230932805427459 63301292430346399208141189)
    ·
      refine ⟨11868992330689949851526473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 63301292430346399208141189 11868992330689949851526473)
      ·
        refine ⟨8901744248017462388644855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11868992330689949851526473 8901744248017462388644855)
        ·
          refine ⟨13352616372026193582967283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8901744248017462388644855 13352616372026193582967283)
          ·
            refine ⟨20028924558039290374450925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13352616372026193582967283 20028924558039290374450925)
            ·
              refine ⟨7510846709264733890419097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20028924558039290374450925 7510846709264733890419097)
              ·
                refine ⟨5633135031948550417814323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7510846709264733890419097 5633135031948550417814323)
                ·
                  refine ⟨8449702547922825626721485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5633135031948550417814323 8449702547922825626721485)
                  ·
                    refine ⟨3168638455471059610020557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8449702547922825626721485 3168638455471059610020557)
                    ·
                      refine ⟨1188239420801647353757709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3168638455471059610020557 1188239420801647353757709)
                      ·
                        rfl

theorem cell23_2314088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 3, 2, 1, 3, 3].length) (baseStart_2314088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2314088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2314088 prefixEnd_2314088 := by exact prefixLift 2314088
  have htrace : WordTrace (prefixWord ++ tailWord_2314088) baseStart_2314088 baseEnd_2314088 := by
    simpa [prefixWord, tailWord_2314088, baseEnd_2314088] using wordTrace_append hprefix tailTrace_2314088
  have hstable : (prefixWord ++ tailWord_2314088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2314088).length < 2 ^ (prefixWord ++ tailWord_2314088).sum := by decide
  have hdescent : baseEnd_2314088 < baseStart_2314088 := by decide
  rcases family_descends (prefixWord ++ tailWord_2314088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2314105 : List Nat := [1, 2, 1, 3, 2, 2, 4, 2, 2, 1, 3]
def baseStart_2314105 : Nat := 118140960795 + 2314105 * 2 ^ 59
def prefixEnd_2314105 : Nat := 4983230072969 + 3 ^ 40 * 2314105 * 2
def baseEnd_2314105 : Nat := 1188248149972773787245131

theorem tailTrace_2314105 : CollatzResearch.WordTrace tailWord_2314105 prefixEnd_2314105 1188248149972773787245131 := by
  unfold tailWord_2314105
  simp only [CollatzResearch.WordTrace]
  refine ⟨84402343281400277514223769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56268228854266851676149179 84402343281400277514223769)
  ·
    refine ⟨63301757461050208135667827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84402343281400277514223769 63301757461050208135667827)
    ·
      refine ⟨94952636191575312203501741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63301757461050208135667827 94952636191575312203501741)
      ·
        refine ⟨35607238571840742076313153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 94952636191575312203501741 35607238571840742076313153)
        ·
          refine ⟨26705428928880556557234865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35607238571840742076313153 26705428928880556557234865)
          ·
            refine ⟨20029071696660417417926149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26705428928880556557234865 20029071696660417417926149)
            ·
              refine ⟨3755450943123828265861153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20029071696660417417926149 3755450943123828265861153)
              ·
                refine ⟨2816588207342871199395865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3755450943123828265861153 2816588207342871199395865)
                ·
                  refine ⟨2112441155507153399546899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2816588207342871199395865 2112441155507153399546899)
                  ·
                    refine ⟨3168661733260730099320349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2112441155507153399546899 3168661733260730099320349)
                    ·
                      refine ⟨1188248149972773787245131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3168661733260730099320349 1188248149972773787245131)
                      ·
                        rfl

theorem cell23_2314105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 4, 2, 2, 1, 3].length) (baseStart_2314105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2314105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2314105 prefixEnd_2314105 := by exact prefixLift 2314105
  have htrace : WordTrace (prefixWord ++ tailWord_2314105) baseStart_2314105 baseEnd_2314105 := by
    simpa [prefixWord, tailWord_2314105, baseEnd_2314105] using wordTrace_append hprefix tailTrace_2314105
  have hstable : (prefixWord ++ tailWord_2314105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2314105).length < 2 ^ (prefixWord ++ tailWord_2314105).sum := by decide
  have hdescent : baseEnd_2314105 < baseStart_2314105 := by decide
  rcases family_descends (prefixWord ++ tailWord_2314105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2314121 : List Nat := [1, 2, 1, 1, 5, 1, 3, 1, 2, 6]
def baseStart_2314121 : Nat := 118140960795 + 2314121 * 2 ^ 59
def prefixEnd_2314121 : Nat := 4983230072969 + 3 ^ 40 * 2314121 * 2
def baseEnd_2314121 : Nat := 396085455221081908215019

theorem tailTrace_2314121 : CollatzResearch.WordTrace tailWord_2314121 prefixEnd_2314121 396085455221081908215019 := by
  unfold tailWord_2314121
  simp only [CollatzResearch.WordTrace]
  refine ⟨84402926849342312246806217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56268617899561541497870811 84402926849342312246806217)
  ·
    refine ⟨63302195137006734185104663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84402926849342312246806217 63302195137006734185104663)
    ·
      refine ⟨94953292705510101277656995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63302195137006734185104663 94953292705510101277656995)
      ·
        refine ⟨142429939058265151916485493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94953292705510101277656995 142429939058265151916485493)
        ·
          refine ⟨13352806786712357992170515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 142429939058265151916485493 13352806786712357992170515)
          ·
            refine ⟨20029210180068536988255773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13352806786712357992170515 20029210180068536988255773)
            ·
              refine ⟨7510953817525701370595915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20029210180068536988255773 7510953817525701370595915)
              ·
                refine ⟨11266430726288552055893873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7510953817525701370595915 11266430726288552055893873)
                ·
                  refine ⟨8449823044716414041920405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11266430726288552055893873 8449823044716414041920405)
                  ·
                    refine ⟨396085455221081908215019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8449823044716414041920405 396085455221081908215019)
                    ·
                      rfl

theorem cell23_2314121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3, 1, 2, 6].length) (baseStart_2314121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2314121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2314121 prefixEnd_2314121 := by exact prefixLift 2314121
  have htrace : WordTrace (prefixWord ++ tailWord_2314121) baseStart_2314121 baseEnd_2314121 := by
    simpa [prefixWord, tailWord_2314121, baseEnd_2314121] using wordTrace_append hprefix tailTrace_2314121
  have hstable : (prefixWord ++ tailWord_2314121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2314121).length < 2 ^ (prefixWord ++ tailWord_2314121).sum := by decide
  have hdescent : baseEnd_2314121 < baseStart_2314121 := by decide
  rcases family_descends (prefixWord ++ tailWord_2314121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2314128 : List Nat := [2, 1, 1, 1, 1, 1, 2, 7, 1, 4, 2]
def baseStart_2314128 : Nat := 118140960795 + 2314128 * 2 ^ 59
def prefixEnd_2314128 : Nat := 4983230072969 + 3 ^ 40 * 2314128 * 2
def baseEnd_2314128 : Nat := 1188259960027827197257525

theorem tailTrace_2314128 : CollatzResearch.WordTrace tailWord_2314128 prefixEnd_2314128 1188259960027827197257525 := by
  unfold tailWord_2314128
  simp only [CollatzResearch.WordTrace]
  refine ⟨42201591080158476221155519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56268788106877968294874025 42201591080158476221155519)
  ·
    refine ⟨63302386620237714331733279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42201591080158476221155519 63302386620237714331733279)
    ·
      refine ⟨94953579930356571497599919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63302386620237714331733279 94953579930356571497599919)
      ·
        refine ⟨142430369895534857246399879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94953579930356571497599919 142430369895534857246399879)
        ·
          refine ⟨213645554843302285869599819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142430369895534857246399879 213645554843302285869599819)
          ·
            refine ⟨320468332264953428804399729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 213645554843302285869599819 320468332264953428804399729)
            ·
              refine ⟨240351249198715071603299797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 320468332264953428804399729 240351249198715071603299797)
              ·
                refine ⟨5633232403094884490702339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 240351249198715071603299797 5633232403094884490702339)
                ·
                  refine ⟨8449848604642326736053509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5633232403094884490702339 8449848604642326736053509)
                  ·
                    refine ⟨1584346613370436263010033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8449848604642326736053509 1584346613370436263010033)
                    ·
                      refine ⟨1188259960027827197257525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1584346613370436263010033 1188259960027827197257525)
                      ·
                        rfl

theorem cell23_2314128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 7, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 7, 1, 4, 2].length) (baseStart_2314128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2314128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2314128 prefixEnd_2314128 := by exact prefixLift 2314128
  have htrace : WordTrace (prefixWord ++ tailWord_2314128) baseStart_2314128 baseEnd_2314128 := by
    simpa [prefixWord, tailWord_2314128, baseEnd_2314128] using wordTrace_append hprefix tailTrace_2314128
  have hstable : (prefixWord ++ tailWord_2314128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2314128).length < 2 ^ (prefixWord ++ tailWord_2314128).sum := by decide
  have hdescent : baseEnd_2314128 < baseStart_2314128 := by decide
  rcases family_descends (prefixWord ++ tailWord_2314128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2314168 : List Nat := [2, 1, 2, 1, 2, 3, 1, 6, 5]
def baseStart_2314168 : Nat := 118140960795 + 2314168 * 2 ^ 59
def prefixEnd_2314168 : Nat := 4983230072969 + 3 ^ 40 * 2314168 * 2
def baseEnd_2314168 : Nat := 132031166583778560084149

theorem tailTrace_2314168 : CollatzResearch.WordTrace tailWord_2314168 prefixEnd_2314168 132031166583778560084149 := by
  unfold tailWord_2314168
  simp only [CollatzResearch.WordTrace]
  refine ⟨42202320540086019636883579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56269760720114692849178105 42202320540086019636883579)
  ·
    refine ⟨63303480810129029455325369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42202320540086019636883579 63303480810129029455325369)
    ·
      refine ⟨47477610607596772091494027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63303480810129029455325369 47477610607596772091494027)
      ·
        refine ⟨71216415911395158137241041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47477610607596772091494027 71216415911395158137241041)
        ·
          refine ⟨53412311933546368602930781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71216415911395158137241041 53412311933546368602930781)
          ·
            refine ⟨20029616975079888226099043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53412311933546368602930781 20029616975079888226099043)
            ·
              refine ⟨30044425462619832339148565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20029616975079888226099043 30044425462619832339148565)
              ·
                refine ⟨1408332443560304640897589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 30044425462619832339148565 1408332443560304640897589)
                ·
                  refine ⟨132031166583778560084149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1408332443560304640897589 132031166583778560084149)
                  ·
                    rfl

theorem cell23_2314168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 6, 5].length) (baseStart_2314168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2314168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2314168 prefixEnd_2314168 := by exact prefixLift 2314168
  have htrace : WordTrace (prefixWord ++ tailWord_2314168) baseStart_2314168 baseEnd_2314168 := by
    simpa [prefixWord, tailWord_2314168, baseEnd_2314168] using wordTrace_append hprefix tailTrace_2314168
  have hstable : (prefixWord ++ tailWord_2314168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2314168).length < 2 ^ (prefixWord ++ tailWord_2314168).sum := by decide
  have hdescent : baseEnd_2314168 < baseStart_2314168 := by decide
  rcases family_descends (prefixWord ++ tailWord_2314168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2314181 : List Nat := [1, 3, 1, 1, 1, 1, 1, 3, 6, 5]
def baseStart_2314181 : Nat := 118140960795 + 2314181 * 2 ^ 59
def prefixEnd_2314181 : Nat := 4983230072969 + 3 ^ 40 * 2314181 * 2
def baseEnd_2314181 : Nat := 396095724834171829964927

theorem tailTrace_2314181 : CollatzResearch.WordTrace tailWord_2314181 prefixEnd_2314181 396095724834171829964927 := by
  unfold tailWord_2314181
  simp only [CollatzResearch.WordTrace]
  refine ⟨84405115229124942493990397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56270076819416628329326931 84405115229124942493990397)
  ·
    refine ⟨31651918210921853435246399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84405115229124942493990397 31651918210921853435246399)
    ·
      refine ⟨47477877316382780152869599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31651918210921853435246399 47477877316382780152869599)
      ·
        refine ⟨71216815974574170229304399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47477877316382780152869599 71216815974574170229304399)
        ·
          refine ⟨106825223961861255343956599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71216815974574170229304399 106825223961861255343956599)
          ·
            refine ⟨160237835942791883015934899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106825223961861255343956599 160237835942791883015934899)
            ·
              refine ⟨240356753914187824523902349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 160237835942791883015934899 240356753914187824523902349)
              ·
                refine ⟨90133782717820434196463381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 240356753914187824523902349 90133782717820434196463381)
                ·
                  refine ⟨4225021064897832852959221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 90133782717820434196463381 4225021064897832852959221)
                  ·
                    refine ⟨396095724834171829964927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4225021064897832852959221 396095724834171829964927)
                    ·
                      rfl

theorem cell23_2314181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 3, 6, 5].length) (baseStart_2314181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2314181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2314181 prefixEnd_2314181 := by exact prefixLift 2314181
  have htrace : WordTrace (prefixWord ++ tailWord_2314181) baseStart_2314181 baseEnd_2314181 := by
    simpa [prefixWord, tailWord_2314181, baseEnd_2314181] using wordTrace_append hprefix tailTrace_2314181
  have hstable : (prefixWord ++ tailWord_2314181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2314181).length < 2 ^ (prefixWord ++ tailWord_2314181).sum := by decide
  have hdescent : baseEnd_2314181 < baseStart_2314181 := by decide
  rcases family_descends (prefixWord ++ tailWord_2314181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2314202 : List Nat := [3, 1, 1, 2, 5, 2, 1, 3, 5]
def baseStart_2314202 : Nat := 118140960795 + 2314202 * 2 ^ 59
def prefixEnd_2314202 : Nat := 4983230072969 + 3 ^ 40 * 2314202 * 2
def baseEnd_2314202 : Nat := 132033106399584434192465

theorem tailTrace_2314202 : CollatzResearch.WordTrace tailWord_2314202 prefixEnd_2314202 132033106399584434192465 := by
  unfold tailWord_2314202
  simp only [CollatzResearch.WordTrace]
  refine ⟨21101470290512215770126215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56270587441365908720336573 21101470290512215770126215)
  ·
    refine ⟨31652205435768323655189323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21101470290512215770126215 31652205435768323655189323)
    ·
      refine ⟨47478308153652485482783985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31652205435768323655189323 47478308153652485482783985)
      ·
        refine ⟨35608731115239364112087989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47478308153652485482783985 35608731115239364112087989)
        ·
          refine ⟨3338318542053690385508249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 35608731115239364112087989 3338318542053690385508249)
          ·
            refine ⟨2503738906540267789131187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3338318542053690385508249 2503738906540267789131187)
            ·
              refine ⟨3755608359810401683696781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2503738906540267789131187 3755608359810401683696781)
              ·
                refine ⟨1408353134928900631386293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3755608359810401683696781 1408353134928900631386293)
                ·
                  refine ⟨132033106399584434192465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1408353134928900631386293 132033106399584434192465)
                  ·
                    rfl

theorem cell23_2314202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 1, 3, 5].length) (baseStart_2314202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2314202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2314202 prefixEnd_2314202 := by exact prefixLift 2314202
  have htrace : WordTrace (prefixWord ++ tailWord_2314202) baseStart_2314202 baseEnd_2314202 := by
    simpa [prefixWord, tailWord_2314202, baseEnd_2314202] using wordTrace_append hprefix tailTrace_2314202
  have hstable : (prefixWord ++ tailWord_2314202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2314202).length < 2 ^ (prefixWord ++ tailWord_2314202).sum := by decide
  have hdescent : baseEnd_2314202 < baseStart_2314202 := by decide
  rcases family_descends (prefixWord ++ tailWord_2314202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2314215 : List Nat := [1, 1, 5, 2, 3, 1, 1, 2, 2, 5]
def baseStart_2314215 : Nat := 118140960795 + 2314215 * 2 ^ 59
def prefixEnd_2314215 : Nat := 4983230072969 + 3 ^ 40 * 2314215 * 2
def baseEnd_2314215 : Nat := 396101544281589452289875

theorem tailTrace_2314215 : CollatzResearch.WordTrace tailWord_2314215 prefixEnd_2314215 396101544281589452289875 := by
  unfold tailWord_2314215
  simp only [CollatzResearch.WordTrace]
  refine ⟨84406355311001766300728099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56270903540667844200485399 84406355311001766300728099)
  ·
    refine ⟨126609532966502649451092149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84406355311001766300728099 126609532966502649451092149)
    ·
      refine ⟨11869643715609623386039889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 126609532966502649451092149 11869643715609623386039889)
      ·
        refine ⟨8902232786707217539529917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11869643715609623386039889 8902232786707217539529917)
        ·
          refine ⟨3338337295015206577323719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8902232786707217539529917 3338337295015206577323719)
          ·
            refine ⟨5007505942522809865985579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3338337295015206577323719 5007505942522809865985579)
            ·
              refine ⟨7511258913784214798978369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5007505942522809865985579 7511258913784214798978369)
              ·
                refine ⟨5633444185338161099233777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7511258913784214798978369 5633444185338161099233777)
                ·
                  refine ⟨4225083139003620824425333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5633444185338161099233777 4225083139003620824425333)
                  ·
                    refine ⟨396101544281589452289875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4225083139003620824425333 396101544281589452289875)
                    ·
                      rfl

theorem cell23_2314215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 1, 2, 2, 5].length) (baseStart_2314215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2314215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2314215 prefixEnd_2314215 := by exact prefixLift 2314215
  have htrace : WordTrace (prefixWord ++ tailWord_2314215) baseStart_2314215 baseEnd_2314215 := by
    simpa [prefixWord, tailWord_2314215, baseEnd_2314215] using wordTrace_append hprefix tailTrace_2314215
  have hstable : (prefixWord ++ tailWord_2314215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2314215).length < 2 ^ (prefixWord ++ tailWord_2314215).sum := by decide
  have hdescent : baseEnd_2314215 < baseStart_2314215 := by decide
  rcases family_descends (prefixWord ++ tailWord_2314215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2314288 : List Nat := [2, 1, 1, 1, 2, 5, 1, 2, 3, 5]
def baseStart_2314288 : Nat := 118140960795 + 2314288 * 2 ^ 59
def prefixEnd_2314288 : Nat := 4983230072969 + 3 ^ 40 * 2314288 * 2
def baseEnd_2314288 : Nat := 396114038977515523752263

theorem tailTrace_2314288 : CollatzResearch.WordTrace tailWord_2314288 prefixEnd_2314288 396114038977515523752263 := by
  unfold tailWord_2314288
  simp only [CollatzResearch.WordTrace]
  refine ⟨42204508919868649884067759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56272678559824866512090345 42204508919868649884067759)
  ·
    refine ⟨63306763379802974826101639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42204508919868649884067759 63306763379802974826101639)
    ·
      refine ⟨94960145069704462239152459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63306763379802974826101639 94960145069704462239152459)
      ·
        refine ⟨142440217604556693358728689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94960145069704462239152459 142440217604556693358728689)
        ·
          refine ⟨106830163203417520019046517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 142440217604556693358728689 106830163203417520019046517)
          ·
            refine ⟨10015327800320392501785611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 106830163203417520019046517 10015327800320392501785611)
            ·
              refine ⟨15022991700480588752678417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10015327800320392501785611 15022991700480588752678417)
              ·
                refine ⟨11267243775360441564508813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15022991700480588752678417 11267243775360441564508813)
                ·
                  refine ⟨4225216415760165586690805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11267243775360441564508813 4225216415760165586690805)
                  ·
                    refine ⟨396114038977515523752263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4225216415760165586690805 396114038977515523752263)
                    ·
                      rfl

theorem cell23_2314288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 2, 3, 5].length) (baseStart_2314288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2314288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2314288 prefixEnd_2314288 := by exact prefixLift 2314288
  have htrace : WordTrace (prefixWord ++ tailWord_2314288) baseStart_2314288 baseEnd_2314288 := by
    simpa [prefixWord, tailWord_2314288, baseEnd_2314288] using wordTrace_append hprefix tailTrace_2314288
  have hstable : (prefixWord ++ tailWord_2314288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2314288).length < 2 ^ (prefixWord ++ tailWord_2314288).sum := by decide
  have hdescent : baseEnd_2314288 < baseStart_2314288 := by decide
  rcases family_descends (prefixWord ++ tailWord_2314288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2314295 : List Nat := [1, 1, 3, 1, 2, 2, 2, 2, 4, 3, 2]
def baseStart_2314295 : Nat := 118140960795 + 2314295 * 2 ^ 59
def prefixEnd_2314295 : Nat := 4983230072969 + 3 ^ 40 * 2314295 * 2
def baseEnd_2314295 : Nat := 1188345711297128043869257

theorem tailTrace_2314295 : CollatzResearch.WordTrace tailWord_2314295 prefixEnd_2314295 1188345711297128043869257 := by
  unfold tailWord_2314295
  simp only [CollatzResearch.WordTrace]
  refine ⟨84409273150711939963640339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56272848767141293309093559 84409273150711939963640339)
  ·
    refine ⟨126613909726067909945460509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84409273150711939963640339 126613909726067909945460509)
    ·
      refine ⟨47480216147275466229547691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 126613909726067909945460509 47480216147275466229547691)
      ·
        refine ⟨71220324220913199344321537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47480216147275466229547691 71220324220913199344321537)
        ·
          refine ⟨53415243165684899508241153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71220324220913199344321537 53415243165684899508241153)
          ·
            refine ⟨40061432374263674631180865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53415243165684899508241153 40061432374263674631180865)
            ·
              refine ⟨30046074280697755973385649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40061432374263674631180865 30046074280697755973385649)
              ·
                refine ⟨22534555710523316980039237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30046074280697755973385649 22534555710523316980039237)
                ·
                  refine ⟨4225229195723121933757357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22534555710523316980039237 4225229195723121933757357)
                  ·
                    refine ⟨1584460948396170725159009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4225229195723121933757357 1584460948396170725159009)
                    ·
                      refine ⟨1188345711297128043869257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1584460948396170725159009 1188345711297128043869257)
                      ·
                        rfl

theorem cell23_2314295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 2, 4, 3, 2].length) (baseStart_2314295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2314295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2314295 prefixEnd_2314295 := by exact prefixLift 2314295
  have htrace : WordTrace (prefixWord ++ tailWord_2314295) baseStart_2314295 baseEnd_2314295 := by
    simpa [prefixWord, tailWord_2314295, baseEnd_2314295] using wordTrace_append hprefix tailTrace_2314295
  have hstable : (prefixWord ++ tailWord_2314295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2314295).length < 2 ^ (prefixWord ++ tailWord_2314295).sum := by decide
  have hdescent : baseEnd_2314295 < baseStart_2314295 := by decide
  rcases family_descends (prefixWord ++ tailWord_2314295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2314305 : List Nat := [1, 2, 5, 1, 2, 1, 2, 1, 3, 5]
def baseStart_2314305 : Nat := 118140960795 + 2314305 * 2 ^ 59
def prefixEnd_2314305 : Nat := 4983230072969 + 3 ^ 40 * 2314305 * 2
def baseEnd_2314305 : Nat := 396116948701224334914737

theorem tailTrace_2314305 : CollatzResearch.WordTrace tailWord_2314305 prefixEnd_2314305 396116948701224334914737 := by
  unfold tailWord_2314305
  simp only [CollatzResearch.WordTrace]
  refine ⟨84409637880675711671504369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56273091920450474447669579 84409637880675711671504369)
  ·
    refine ⟨63307228410506783753628277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84409637880675711671504369 63307228410506783753628277)
    ·
      refine ⟨5935052663485010976902651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 63307228410506783753628277 5935052663485010976902651)
      ·
        refine ⟨8902578995227516465353977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5935052663485010976902651 8902578995227516465353977)
        ·
          refine ⟨6676934246420637349015483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8902578995227516465353977 6676934246420637349015483)
          ·
            refine ⟨10015401369630956023523225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6676934246420637349015483 10015401369630956023523225)
            ·
              refine ⟨7511551027223217017642419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10015401369630956023523225 7511551027223217017642419)
              ·
                refine ⟨11267326540834825526463629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7511551027223217017642419 11267326540834825526463629)
                ·
                  refine ⟨4225247452813059572423861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11267326540834825526463629 4225247452813059572423861)
                  ·
                    refine ⟨396116948701224334914737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4225247452813059572423861 396116948701224334914737)
                    ·
                      rfl

theorem cell23_2314305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 2, 1, 3, 5].length) (baseStart_2314305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2314305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2314305 prefixEnd_2314305 := by exact prefixLift 2314305
  have htrace : WordTrace (prefixWord ++ tailWord_2314305) baseStart_2314305 baseEnd_2314305 := by
    simpa [prefixWord, tailWord_2314305, baseEnd_2314305] using wordTrace_append hprefix tailTrace_2314305
  have hstable : (prefixWord ++ tailWord_2314305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2314305).length < 2 ^ (prefixWord ++ tailWord_2314305).sum := by decide
  have hdescent : baseEnd_2314305 < baseStart_2314305 := by decide
  rcases family_descends (prefixWord ++ tailWord_2314305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2314322 : List Nat := [3, 2, 2, 1, 4, 1, 1, 3, 1, 5]
def baseStart_2314322 : Nat := 118140960795 + 2314322 * 2 ^ 59
def prefixEnd_2314322 : Nat := 4983230072969 + 3 ^ 40 * 2314322 * 2
def baseEnd_2314322 : Nat := 396119858424933146077211

theorem tailTrace_2314322 : CollatzResearch.WordTrace tailWord_2314322 prefixEnd_2314322 396119858424933146077211 := by
  unfold tailWord_2314322
  simp only [CollatzResearch.WordTrace]
  refine ⟨21102564480403530893718305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56273505281076082383248813 21102564480403530893718305)
  ·
    refine ⟨15826923360302648170288729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21102564480403530893718305 15826923360302648170288729)
    ·
      refine ⟨11870192520226986127716547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15826923360302648170288729 11870192520226986127716547)
      ·
        refine ⟨17805288780340479191574821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11870192520226986127716547 17805288780340479191574821)
        ·
          refine ⟨3338491646313839848420279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17805288780340479191574821 3338491646313839848420279)
          ·
            refine ⟨5007737469470759772630419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3338491646313839848420279 5007737469470759772630419)
            ·
              refine ⟨7511606204206139658945629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5007737469470759772630419 7511606204206139658945629)
              ·
                refine ⟨2816852326577302372104611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7511606204206139658945629 2816852326577302372104611)
                ·
                  refine ⟨4225278489865953558156917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2816852326577302372104611 4225278489865953558156917)
                  ·
                    refine ⟨396119858424933146077211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4225278489865953558156917 396119858424933146077211)
                    ·
                      rfl

theorem cell23_2314322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 1, 3, 1, 5].length) (baseStart_2314322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2314322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2314322 prefixEnd_2314322 := by exact prefixLift 2314322
  have htrace : WordTrace (prefixWord ++ tailWord_2314322) baseStart_2314322 baseEnd_2314322 := by
    simpa [prefixWord, tailWord_2314322, baseEnd_2314322] using wordTrace_append hprefix tailTrace_2314322
  have hstable : (prefixWord ++ tailWord_2314322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2314322).length < 2 ^ (prefixWord ++ tailWord_2314322).sum := by decide
  have hdescent : baseEnd_2314322 < baseStart_2314322 := by decide
  rcases family_descends (prefixWord ++ tailWord_2314322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2314335 : List Nat := [1, 1, 2, 3, 1, 1, 2, 6, 2, 4]
def baseStart_2314335 : Nat := 118140960795 + 2314335 * 2 ^ 59
def prefixEnd_2314335 : Nat := 4983230072969 + 3 ^ 40 * 2314335 * 2
def baseEnd_2314335 : Nat := 396122083507769295789691

theorem tailTrace_2314335 : CollatzResearch.WordTrace tailWord_2314335 prefixEnd_2314335 396122083507769295789691 := by
  unfold tailWord_2314335
  simp only [CollatzResearch.WordTrace]
  refine ⟨84410732070567026795096459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56273821380378017863397639 84410732070567026795096459)
  ·
    refine ⟨126616098105850540192644689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84410732070567026795096459 126616098105850540192644689)
    ·
      refine ⟨94962073579387905144483517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126616098105850540192644689 94962073579387905144483517)
      ·
        refine ⟨35610777592270464429181319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 94962073579387905144483517 35610777592270464429181319)
        ·
          refine ⟨53416166388405696643771979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35610777592270464429181319 53416166388405696643771979)
          ·
            refine ⟨80124249582608544965657969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53416166388405696643771979 80124249582608544965657969)
            ·
              refine ⟨60093187186956408724243477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80124249582608544965657969 60093187186956408724243477)
              ·
                refine ⟨2816868149388581658948913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 60093187186956408724243477 2816868149388581658948913)
                ·
                  refine ⟨2112651112041436244211685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2816868149388581658948913 2112651112041436244211685)
                  ·
                    refine ⟨396122083507769295789691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2112651112041436244211685 396122083507769295789691)
                    ·
                      rfl

theorem cell23_2314335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 6, 2, 4].length) (baseStart_2314335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2314335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2314335 prefixEnd_2314335 := by exact prefixLift 2314335
  have htrace : WordTrace (prefixWord ++ tailWord_2314335) baseStart_2314335 baseEnd_2314335 := by
    simpa [prefixWord, tailWord_2314335, baseEnd_2314335] using wordTrace_append hprefix tailTrace_2314335
  have hstable : (prefixWord ++ tailWord_2314335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2314335).length < 2 ^ (prefixWord ++ tailWord_2314335).sum := by decide
  have hdescent : baseEnd_2314335 < baseStart_2314335 := by decide
  rcases family_descends (prefixWord ++ tailWord_2314335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2314365 : List Nat := [1, 4, 1, 1, 3, 2, 4, 7]
def baseStart_2314365 : Nat := 118140960795 + 2314365 * 2 ^ 59
def prefixEnd_2314365 : Nat := 4983230072969 + 3 ^ 40 * 2314365 * 2
def baseEnd_2314365 : Nat := 44014135368257139629405

theorem tailTrace_2314365 : CollatzResearch.WordTrace tailWord_2314365 prefixEnd_2314365 44014135368257139629405 := by
  unfold tailWord_2314365
  simp only [CollatzResearch.WordTrace]
  refine ⟨84411826260458341918688549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56274550840305561279125699 84411826260458341918688549)
  ·
    refine ⟨15827217423835939109754103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 84411826260458341918688549 15827217423835939109754103)
    ·
      refine ⟨23740826135753908664631155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15827217423835939109754103 23740826135753908664631155)
      ·
        refine ⟨35611239203630862996946733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23740826135753908664631155 35611239203630862996946733)
        ·
          refine ⟨13354214701361573623855025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35611239203630862996946733 13354214701361573623855025)
          ·
            refine ⟨10015661026021180217891269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13354214701361573623855025 10015661026021180217891269)
            ·
              refine ⟨1877936442378971290854613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10015661026021180217891269 1877936442378971290854613)
              ·
                refine ⟨44014135368257139629405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1877936442378971290854613 44014135368257139629405)
                ·
                  rfl

theorem cell23_2314365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 4, 7].length) (baseStart_2314365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2314365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2314365 prefixEnd_2314365 := by exact prefixLift 2314365
  have htrace : WordTrace (prefixWord ++ tailWord_2314365) baseStart_2314365 baseEnd_2314365 := by
    simpa [prefixWord, tailWord_2314365, baseEnd_2314365] using wordTrace_append hprefix tailTrace_2314365
  have hstable : (prefixWord ++ tailWord_2314365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2314365).length < 2 ^ (prefixWord ++ tailWord_2314365).sum := by decide
  have hdescent : baseEnd_2314365 < baseStart_2314365 := by decide
  rcases family_descends (prefixWord ++ tailWord_2314365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2314375 : List Nat := [1, 1, 4, 2, 1, 1, 2, 4, 1, 3, 3]
def baseStart_2314375 : Nat := 118140960795 + 2314375 * 2 ^ 59
def prefixEnd_2314375 : Nat := 4983230072969 + 3 ^ 40 * 2314375 * 2
def baseEnd_2314375 : Nat := 1188386789749487730868889

theorem tailTrace_2314375 : CollatzResearch.WordTrace tailWord_2314375 prefixEnd_2314375 1188386789749487730868889 := by
  unfold tailWord_2314375
  simp only [CollatzResearch.WordTrace]
  refine ⟨84412190990422113626552579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56274793993614742417701719 84412190990422113626552579)
  ·
    refine ⟨126618286485633170439828869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84412190990422113626552579 126618286485633170439828869)
    ·
      refine ⟨23740928716056219457467913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 126618286485633170439828869 23740928716056219457467913)
      ·
        refine ⟨17805696537042164593100935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23740928716056219457467913 17805696537042164593100935)
        ·
          refine ⟨26708544805563246889651403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17805696537042164593100935 26708544805563246889651403)
          ·
            refine ⟨40062817208344870334477105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26708544805563246889651403 40062817208344870334477105)
            ·
              refine ⟨30047112906258652750857829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40062817208344870334477105 30047112906258652750857829)
              ·
                refine ⟨5633833669923497390785843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30047112906258652750857829 5633833669923497390785843)
                ·
                  refine ⟨8450750504885246086178765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5633833669923497390785843 8450750504885246086178765)
                  ·
                    refine ⟨3169031439331967282317037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8450750504885246086178765 3169031439331967282317037)
                    ·
                      refine ⟨1188386789749487730868889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3169031439331967282317037 1188386789749487730868889)
                      ·
                        rfl

theorem cell23_2314375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 4, 1, 3, 3].length) (baseStart_2314375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2314375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2314375 prefixEnd_2314375 := by exact prefixLift 2314375
  have htrace : WordTrace (prefixWord ++ tailWord_2314375) baseStart_2314375 baseEnd_2314375 := by
    simpa [prefixWord, tailWord_2314375, baseEnd_2314375] using wordTrace_append hprefix tailTrace_2314375
  have hstable : (prefixWord ++ tailWord_2314375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2314375).length < 2 ^ (prefixWord ++ tailWord_2314375).sum := by decide
  have hdescent : baseEnd_2314375 < baseStart_2314375 := by decide
  rcases family_descends (prefixWord ++ tailWord_2314375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2314382 : List Nat := [4, 1, 1, 3, 4, 1, 9]
def baseStart_2314382 : Nat := 118140960795 + 2314382 * 2 ^ 59
def prefixEnd_2314382 : Nat := 4983230072969 + 3 ^ 40 * 2314382 * 2
def baseEnd_2314382 : Nat := 14671486223630483993597

theorem tailTrace_2314382 : CollatzResearch.WordTrace tailWord_2314382 prefixEnd_2314382 14671486223630483993597 := by
  unfold tailWord_2314382
  simp only [CollatzResearch.WordTrace]
  refine ⟨10551555787674594227757175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56274964200931169214704933 10551555787674594227757175)
  ·
    refine ⟨15827333681511891341635763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10551555787674594227757175 15827333681511891341635763)
    ·
      refine ⟨23741000522267837012453645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15827333681511891341635763 23741000522267837012453645)
      ·
        refine ⟨8902875195850438879670117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23741000522267837012453645 8902875195850438879670117)
        ·
          refine ⟨1669289099221957289938147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8902875195850438879670117 1669289099221957289938147)
          ·
            refine ⟨2503933648832935934907221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1669289099221957289938147 2503933648832935934907221)
            ·
              refine ⟨14671486223630483993597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2503933648832935934907221 14671486223630483993597)
              ·
                rfl

theorem cell23_2314382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 9].length) (baseStart_2314382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2314382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2314382 prefixEnd_2314382 := by exact prefixLift 2314382
  have htrace : WordTrace (prefixWord ++ tailWord_2314382) baseStart_2314382 baseEnd_2314382 := by
    simpa [prefixWord, tailWord_2314382, baseEnd_2314382] using wordTrace_append hprefix tailTrace_2314382
  have hstable : (prefixWord ++ tailWord_2314382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2314382).length < 2 ^ (prefixWord ++ tailWord_2314382).sum := by decide
  have hdescent : baseEnd_2314382 < baseStart_2314382 := by decide
  rcases family_descends (prefixWord ++ tailWord_2314382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2314432 : List Nat := [2, 1, 1, 2, 5, 1, 1, 1, 3, 4, 2]
def baseStart_2314432 : Nat := 118140960795 + 2314432 * 2 ^ 59
def prefixEnd_2314432 : Nat := 4983230072969 + 3 ^ 40 * 2314432 * 2
def baseEnd_2314432 : Nat := 1188416058146794007856127

theorem tailTrace_2314432 : CollatzResearch.WordTrace tailWord_2314432 prefixEnd_2314432 1188416058146794007856127 := by
  unfold tailWord_2314432
  simp only [CollatzResearch.WordTrace]
  refine ⟨42207134975607806180688775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56276179967477074907585033 42207134975607806180688775)
  ·
    refine ⟨63310702463411709271033163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42207134975607806180688775 63310702463411709271033163)
    ·
      refine ⟨94966053695117563906549745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63310702463411709271033163 94966053695117563906549745)
      ·
        refine ⟨71224540271338172929912309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94966053695117563906549745 71224540271338172929912309)
        ·
          refine ⟨6677300650437953712179279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 71224540271338172929912309 6677300650437953712179279)
          ·
            refine ⟨10015950975656930568268919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6677300650437953712179279 10015950975656930568268919)
            ·
              refine ⟨15023926463485395852403379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10015950975656930568268919 15023926463485395852403379)
              ·
                refine ⟨22535889695228093778605069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15023926463485395852403379 22535889695228093778605069)
                ·
                  refine ⟨8450958635710535166976901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22535889695228093778605069 8450958635710535166976901)
                  ·
                    refine ⟨1584554744195725343808169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8450958635710535166976901 1584554744195725343808169)
                    ·
                      refine ⟨1188416058146794007856127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1584554744195725343808169 1188416058146794007856127)
                      ·
                        rfl

theorem cell23_2314432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 1, 3, 4, 2].length) (baseStart_2314432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2314432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2314432 prefixEnd_2314432 := by exact prefixLift 2314432
  have htrace : WordTrace (prefixWord ++ tailWord_2314432) baseStart_2314432 baseEnd_2314432 := by
    simpa [prefixWord, tailWord_2314432, baseEnd_2314432] using wordTrace_append hprefix tailTrace_2314432
  have hstable : (prefixWord ++ tailWord_2314432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2314432).length < 2 ^ (prefixWord ++ tailWord_2314432).sum := by decide
  have hdescent : baseEnd_2314432 < baseStart_2314432 := by decide
  rcases family_descends (prefixWord ++ tailWord_2314432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2314449 : List Nat := [1, 2, 2, 1, 2, 2, 3, 4, 2, 2, 2]
def baseStart_2314449 : Nat := 118140960795 + 2314449 * 2 ^ 59
def prefixEnd_2314449 : Nat := 4983230072969 + 3 ^ 40 * 2314449 * 2
def baseEnd_2314449 : Nat := 1188424787317920441343549

theorem tailTrace_2314449 : CollatzResearch.WordTrace tailWord_2314449 prefixEnd_2314449 1188424787317920441343549 := by
  unfold tailWord_2314449
  simp only [CollatzResearch.WordTrace]
  refine ⟨84414889992154024264746401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56276593328102682843164267 84414889992154024264746401)
  ·
    refine ⟨63311167494115518198559801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84414889992154024264746401 63311167494115518198559801)
    ·
      refine ⟨47483375620586638648919851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63311167494115518198559801 47483375620586638648919851)
      ·
        refine ⟨71225063430879957973379777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47483375620586638648919851 71225063430879957973379777)
        ·
          refine ⟨53418797573159968480034833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71225063430879957973379777 53418797573159968480034833)
          ·
            refine ⟨40064098179869976360026125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53418797573159968480034833 40064098179869976360026125)
            ·
              refine ⟨15024036817451241135009797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40064098179869976360026125 15024036817451241135009797)
              ·
                refine ⟨2817006903272107712814337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15024036817451241135009797 2817006903272107712814337)
                ·
                  refine ⟨2112755177454080784610753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2817006903272107712814337 2112755177454080784610753)
                  ·
                    refine ⟨1584566383090560588458065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2112755177454080784610753 1584566383090560588458065)
                    ·
                      refine ⟨1188424787317920441343549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1584566383090560588458065 1188424787317920441343549)
                      ·
                        rfl

theorem cell23_2314449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 4, 2, 2, 2].length) (baseStart_2314449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2314449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2314449 prefixEnd_2314449 := by exact prefixLift 2314449
  have htrace : WordTrace (prefixWord ++ tailWord_2314449) baseStart_2314449 baseEnd_2314449 := by
    simpa [prefixWord, tailWord_2314449, baseEnd_2314449] using wordTrace_append hprefix tailTrace_2314449
  have hstable : (prefixWord ++ tailWord_2314449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2314449).length < 2 ^ (prefixWord ++ tailWord_2314449).sum := by decide
  have hdescent : baseEnd_2314449 < baseStart_2314449 := by decide
  rcases family_descends (prefixWord ++ tailWord_2314449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2314500 : List Nat := [2, 3, 2, 2, 4, 1, 1, 2, 2, 2, 2]
def baseStart_2314500 : Nat := 118140960795 + 2314500 * 2 ^ 59
def prefixEnd_2314500 : Nat := 4983230072969 + 3 ^ 40 * 2314500 * 2
def baseEnd_2314500 : Nat := 1188450974831299741805815

theorem tailTrace_2314500 : CollatzResearch.WordTrace tailWord_2314500 prefixEnd_2314500 1188450974831299741805815 := by
  unfold tailWord_2314500
  simp only [CollatzResearch.WordTrace]
  refine ⟨42208375057484629987426477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56277833409979506649901969 42208375057484629987426477)
  ·
    refine ⟨15828140646556736245284929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42208375057484629987426477 15828140646556736245284929)
    ·
      refine ⟨11871105484917552183963697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15828140646556736245284929 11871105484917552183963697)
      ·
        refine ⟨8903329113688164137972773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11871105484917552183963697 8903329113688164137972773)
        ·
          refine ⟨1669374208816530775869895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8903329113688164137972773 1669374208816530775869895)
          ·
            refine ⟨2504061313224796163804843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1669374208816530775869895 2504061313224796163804843)
            ·
              refine ⟨3756091969837194245707265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2504061313224796163804843 3756091969837194245707265)
              ·
                refine ⟨2817068977377895684280449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3756091969837194245707265 2817068977377895684280449)
                ·
                  refine ⟨2112801733033421763210337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2817068977377895684280449 2112801733033421763210337)
                  ·
                    refine ⟨1584601299775066322407753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2112801733033421763210337 1584601299775066322407753)
                    ·
                      refine ⟨1188450974831299741805815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1584601299775066322407753 1188450974831299741805815)
                      ·
                        rfl

theorem cell23_2314500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 1, 2, 2, 2, 2].length) (baseStart_2314500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2314500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2314500 prefixEnd_2314500 := by exact prefixLift 2314500
  have htrace : WordTrace (prefixWord ++ tailWord_2314500) baseStart_2314500 baseEnd_2314500 := by
    simpa [prefixWord, tailWord_2314500, baseEnd_2314500] using wordTrace_append hprefix tailTrace_2314500
  have hstable : (prefixWord ++ tailWord_2314500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2314500).length < 2 ^ (prefixWord ++ tailWord_2314500).sum := by decide
  have hdescent : baseEnd_2314500 < baseStart_2314500 := by decide
  rcases family_descends (prefixWord ++ tailWord_2314500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2314632 : List Nat := [2, 1, 3, 3, 1, 1, 2, 1, 3, 1, 5]
def baseStart_2314632 : Nat := 118140960795 + 2314632 * 2 ^ 59
def prefixEnd_2314632 : Nat := 4983230072969 + 3 ^ 40 * 2314632 * 2
def baseEnd_2314632 : Nat := 1188518754277693225355207

theorem tailTrace_2314632 : CollatzResearch.WordTrace tailWord_2314632 prefixEnd_2314632 1188518754277693225355207 := by
  unfold tailWord_2314632
  simp only [CollatzResearch.WordTrace]
  refine ⟨42210782275245523259329075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56281043033660697679105433 42210782275245523259329075)
  ·
    refine ⟨63316173412868284888993613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42210782275245523259329075 63316173412868284888993613)
    ·
      refine ⟨23743565029825606833372605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63316173412868284888993613 23743565029825606833372605)
      ·
        refine ⟨8903836886184602562514727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23743565029825606833372605 8903836886184602562514727)
        ·
          refine ⟨13355755329276903843772091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8903836886184602562514727 13355755329276903843772091)
          ·
            refine ⟨20033632993915355765658137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13355755329276903843772091 20033632993915355765658137)
            ·
              refine ⟨15025224745436516824243603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20033632993915355765658137 15025224745436516824243603)
              ·
                refine ⟨22537837118154775236365405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15025224745436516824243603 22537837118154775236365405)
                ·
                  refine ⟨8451688919308040713637027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22537837118154775236365405 8451688919308040713637027)
                  ·
                    refine ⟨12677533378962061070455541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8451688919308040713637027 12677533378962061070455541)
                    ·
                      refine ⟨1188518754277693225355207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12677533378962061070455541 1188518754277693225355207)
                      ·
                        rfl

theorem cell23_2314632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 1, 3, 1, 5].length) (baseStart_2314632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2314632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2314632 prefixEnd_2314632 := by exact prefixLift 2314632
  have htrace : WordTrace (prefixWord ++ tailWord_2314632) baseStart_2314632 baseEnd_2314632 := by
    simpa [prefixWord, tailWord_2314632, baseEnd_2314632] using wordTrace_append hprefix tailTrace_2314632
  have hstable : (prefixWord ++ tailWord_2314632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2314632).length < 2 ^ (prefixWord ++ tailWord_2314632).sum := by decide
  have hdescent : baseEnd_2314632 < baseStart_2314632 := by decide
  rcases family_descends (prefixWord ++ tailWord_2314632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2314649 : List Nat := [1, 2, 1, 2, 1, 4, 2, 4, 1, 2, 3]
def baseStart_2314649 : Nat := 118140960795 + 2314649 * 2 ^ 59
def prefixEnd_2314649 : Nat := 4983230072969 + 3 ^ 40 * 2314649 * 2
def baseEnd_2314649 : Nat := 1188527483448819658842629

theorem tailTrace_2314649 : CollatzResearch.WordTrace tailWord_2314649 prefixEnd_2314649 1188527483448819658842629 := by
  unfold tailWord_2314649
  simp only [CollatzResearch.WordTrace]
  refine ⟨84422184591429458422027001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56281456394286305614684667 84422184591429458422027001)
  ·
    refine ⟨63316638443572093816520251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84422184591429458422027001 63316638443572093816520251)
    ·
      refine ⟨94974957665358140724780377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63316638443572093816520251 94974957665358140724780377)
      ·
        refine ⟨71231218249018605543585283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94974957665358140724780377 71231218249018605543585283)
        ·
          refine ⟨106846827373527908315377925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71231218249018605543585283 106846827373527908315377925)
          ·
            refine ⟨20033780132536482809133361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 106846827373527908315377925 20033780132536482809133361)
            ·
              refine ⟨15025335099402362106850021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20033780132536482809133361 15025335099402362106850021)
              ·
                refine ⟨2817250331137942895034379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15025335099402362106850021 2817250331137942895034379)
                ·
                  refine ⟨4225875496706914342551569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2817250331137942895034379 4225875496706914342551569)
                  ·
                    refine ⟨3169406622530185756913677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4225875496706914342551569 3169406622530185756913677)
                    ·
                      refine ⟨1188527483448819658842629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3169406622530185756913677 1188527483448819658842629)
                      ·
                        rfl

theorem cell23_2314649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 4, 1, 2, 3].length) (baseStart_2314649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2314649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2314649 prefixEnd_2314649 := by exact prefixLift 2314649
  have htrace : WordTrace (prefixWord ++ tailWord_2314649) baseStart_2314649 baseEnd_2314649 := by
    simpa [prefixWord, tailWord_2314649, baseEnd_2314649] using wordTrace_append hprefix tailTrace_2314649
  have hstable : (prefixWord ++ tailWord_2314649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2314649).length < 2 ^ (prefixWord ++ tailWord_2314649).sum := by decide
  have hdescent : baseEnd_2314649 < baseStart_2314649 := by decide
  rcases family_descends (prefixWord ++ tailWord_2314649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2314663 : List Nat := [1, 1, 6, 1, 1, 4, 2, 1, 1, 1, 4]
def baseStart_2314663 : Nat := 118140960795 + 2314663 * 2 ^ 59
def prefixEnd_2314663 : Nat := 4983230072969 + 3 ^ 40 * 2314663 * 2
def baseEnd_2314663 : Nat := 1188534672177982604067565

theorem tailTrace_2314663 : CollatzResearch.WordTrace tailWord_2314663 prefixEnd_2314663 1188534672177982604067565 := by
  unfold tailWord_2314663
  simp only [CollatzResearch.WordTrace]
  refine ⟨84422695213378738813036643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56281796808919159208691095 84422695213378738813036643)
  ·
    refine ⟨126634042820068108219554965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84422695213378738813036643 126634042820068108219554965)
    ·
      refine ⟨5935970757190692572791639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 126634042820068108219554965 5935970757190692572791639)
      ·
        refine ⟨8903956135786038859187459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5935970757190692572791639 8903956135786038859187459)
        ·
          refine ⟨13355934203679058288781189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8903956135786038859187459 13355934203679058288781189)
          ·
            refine ⟨2504237663189823429146473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13355934203679058288781189 2504237663189823429146473)
            ·
              refine ⟨1878178247392367571859855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2504237663189823429146473 1878178247392367571859855)
              ·
                refine ⟨2817267371088551357789783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1878178247392367571859855 2817267371088551357789783)
                ·
                  refine ⟨4225901056632827036684675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2817267371088551357789783 4225901056632827036684675)
                  ·
                    refine ⟨6338851584949240555027013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4225901056632827036684675 6338851584949240555027013)
                    ·
                      refine ⟨1188534672177982604067565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6338851584949240555027013 1188534672177982604067565)
                      ·
                        rfl

theorem cell23_2314663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 2, 1, 1, 1, 4].length) (baseStart_2314663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2314663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2314663 prefixEnd_2314663 := by exact prefixLift 2314663
  have htrace : WordTrace (prefixWord ++ tailWord_2314663) baseStart_2314663 baseEnd_2314663 := by
    simpa [prefixWord, tailWord_2314663, baseEnd_2314663] using wordTrace_append hprefix tailTrace_2314663
  have hstable : (prefixWord ++ tailWord_2314663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2314663).length < 2 ^ (prefixWord ++ tailWord_2314663).sum := by decide
  have hdescent : baseEnd_2314663 < baseStart_2314663 := by decide
  rcases family_descends (prefixWord ++ tailWord_2314663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2314669 : List Nat := [1, 5, 2, 2, 2, 1, 10]
def baseStart_2314669 : Nat := 118140960795 + 2314669 * 2 ^ 59
def prefixEnd_2314669 : Nat := 4983230072969 + 3 ^ 40 * 2314669 * 2
def baseEnd_2314669 : Nat := 14673305593356908402377

theorem tailTrace_2314669 : CollatzResearch.WordTrace tailWord_2314669 prefixEnd_2314669 14673305593356908402377 := by
  unfold tailWord_2314669
  simp only [CollatzResearch.WordTrace]
  refine ⟨84422914051357001837755061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56281942700904667891836707 84422914051357001837755061)
  ·
    refine ⟨7914648192314718922289537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 84422914051357001837755061 7914648192314718922289537)
    ·
      refine ⟨5935986144236039191717153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7914648192314718922289537 5935986144236039191717153)
      ·
        refine ⟨4451989608177029393787865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5935986144236039191717153 4451989608177029393787865)
        ·
          refine ⟨3338992206132772045340899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4451989608177029393787865 3338992206132772045340899)
          ·
            refine ⟨5008488309199158068011349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3338992206132772045340899 5008488309199158068011349)
            ·
              refine ⟨14673305593356908402377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 5008488309199158068011349 14673305593356908402377)
              ·
                rfl

theorem cell23_2314669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 10].length) (baseStart_2314669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2314669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2314669 prefixEnd_2314669 := by exact prefixLift 2314669
  have htrace : WordTrace (prefixWord ++ tailWord_2314669) baseStart_2314669 baseEnd_2314669 := by
    simpa [prefixWord, tailWord_2314669, baseEnd_2314669] using wordTrace_append hprefix tailTrace_2314669
  have hstable : (prefixWord ++ tailWord_2314669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2314669).length < 2 ^ (prefixWord ++ tailWord_2314669).sum := by decide
  have hdescent : baseEnd_2314669 < baseStart_2314669 := by decide
  rcases family_descends (prefixWord ++ tailWord_2314669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2314696 : List Nat := [2, 1, 3, 1, 3, 4, 1, 1, 1, 3, 3]
def baseStart_2314696 : Nat := 118140960795 + 2314696 * 2 ^ 59
def prefixEnd_2314696 : Nat := 4983230072969 + 3 ^ 40 * 2314696 * 2
def baseEnd_2314696 : Nat := 1188551617039580974954913

theorem tailTrace_2314696 : CollatzResearch.WordTrace tailWord_2314696 prefixEnd_2314696 1188551617039580974954913 := by
  unfold tailWord_2314696
  simp only [CollatzResearch.WordTrace]
  refine ⟨42211949411129592724493971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56282599214839456965991961 42211949411129592724493971)
  ·
    refine ⟨63317924116694389086740957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42211949411129592724493971 63317924116694389086740957)
    ·
      refine ⟨23744221543760395907527859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63317924116694389086740957 23744221543760395907527859)
      ·
        refine ⟨35616332315640593861291789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23744221543760395907527859 35616332315640593861291789)
        ·
          refine ⟨13356124618365222697984421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35616332315640593861291789 13356124618365222697984421)
          ·
            refine ⟨2504273365943479255872079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13356124618365222697984421 2504273365943479255872079)
            ·
              refine ⟨3756410048915218883808119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2504273365943479255872079 3756410048915218883808119)
              ·
                refine ⟨5634615073372828325712179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3756410048915218883808119 5634615073372828325712179)
                ·
                  refine ⟨8451922610059242488568269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5634615073372828325712179 8451922610059242488568269)
                  ·
                    refine ⟨3169470978772215933213101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8451922610059242488568269 3169470978772215933213101)
                    ·
                      refine ⟨1188551617039580974954913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3169470978772215933213101 1188551617039580974954913)
                      ·
                        rfl

theorem cell23_2314696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 1, 1, 1, 3, 3].length) (baseStart_2314696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2314696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2314696 prefixEnd_2314696 := by exact prefixLift 2314696
  have htrace : WordTrace (prefixWord ++ tailWord_2314696) baseStart_2314696 baseEnd_2314696 := by
    simpa [prefixWord, tailWord_2314696, baseEnd_2314696] using wordTrace_append hprefix tailTrace_2314696
  have hstable : (prefixWord ++ tailWord_2314696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2314696).length < 2 ^ (prefixWord ++ tailWord_2314696).sum := by decide
  have hdescent : baseEnd_2314696 < baseStart_2314696 := by decide
  rcases family_descends (prefixWord ++ tailWord_2314696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2314736 : List Nat := [2, 1, 1, 1, 3, 3, 1, 3, 4, 2, 2]
def baseStart_2314736 : Nat := 118140960795 + 2314736 * 2 ^ 59
def prefixEnd_2314736 : Nat := 4983230072969 + 3 ^ 40 * 2314736 * 2
def baseEnd_2314736 : Nat := 1188572156265760818454729

theorem tailTrace_2314736 : CollatzResearch.WordTrace tailWord_2314736 prefixEnd_2314736 1188572156265760818454729 := by
  unfold tailWord_2314736
  simp only [CollatzResearch.WordTrace]
  refine ⟨42212678871057136140222031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56283571828076181520296041 42212678871057136140222031)
  ·
    refine ⟨63319018306585704210333047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42212678871057136140222031 63319018306585704210333047)
    ·
      refine ⟨94978527459878556315499571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63319018306585704210333047 94978527459878556315499571)
      ·
        refine ⟨142467791189817834473249357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94978527459878556315499571 142467791189817834473249357)
        ·
          refine ⟨53425421696181687927468509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 142467791189817834473249357 53425421696181687927468509)
          ·
            refine ⟨20034533136068132972800691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53425421696181687927468509 20034533136068132972800691)
            ·
              refine ⟨30051799704102199459201037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20034533136068132972800691 30051799704102199459201037)
              ·
                refine ⟨11269424889038324797200389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30051799704102199459201037 11269424889038324797200389)
                ·
                  refine ⟨2113017166694685899475073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11269424889038324797200389 2113017166694685899475073)
                  ·
                    refine ⟨1584762875021014424606305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2113017166694685899475073 1584762875021014424606305)
                    ·
                      refine ⟨1188572156265760818454729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1584762875021014424606305 1188572156265760818454729)
                      ·
                        rfl

theorem cell23_2314736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 3, 4, 2, 2].length) (baseStart_2314736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2314736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2314736 prefixEnd_2314736 := by exact prefixLift 2314736
  have htrace : WordTrace (prefixWord ++ tailWord_2314736) baseStart_2314736 baseEnd_2314736 := by
    simpa [prefixWord, tailWord_2314736, baseEnd_2314736] using wordTrace_append hprefix tailTrace_2314736
  have hstable : (prefixWord ++ tailWord_2314736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2314736).length < 2 ^ (prefixWord ++ tailWord_2314736).sum := by decide
  have hdescent : baseEnd_2314736 < baseStart_2314736 := by decide
  rcases family_descends (prefixWord ++ tailWord_2314736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2314779 : List Nat := [1, 1, 1, 1, 1, 1, 3, 1, 6, 5, 2]
def baseStart_2314779 : Nat := 118140960795 + 2314779 * 2 ^ 59
def prefixEnd_2314779 : Nat := 4983230072969 + 3 ^ 40 * 2314779 * 2
def baseEnd_2314779 : Nat := 1188594235933904150217031

theorem tailTrace_2314779 : CollatzResearch.WordTrace tailWord_2314779 prefixEnd_2314779 1188594235933904150217031 := by
  unfold tailWord_2314779
  simp only [CollatzResearch.WordTrace]
  refine ⟨84426926080958490624259391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56284617387305660416172927 84426926080958490624259391)
  ·
    refine ⟨126640389121437735936389087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84426926080958490624259391 126640389121437735936389087)
    ·
      refine ⟨189960583682156603904583631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126640389121437735936389087 189960583682156603904583631)
      ·
        refine ⟨284940875523234905856875447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 189960583682156603904583631 284940875523234905856875447)
        ·
          refine ⟨427411313284852358785313171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 284940875523234905856875447 427411313284852358785313171)
          ·
            refine ⟨641116969927278538177969757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 427411313284852358785313171 641116969927278538177969757)
            ·
              refine ⟨240418863722729451816738659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 641116969927278538177969757 240418863722729451816738659)
              ·
                refine ⟨360628295584094177725107989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 240418863722729451816738659 360628295584094177725107989)
                ·
                  refine ⟨16904451355504414580864437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 360628295584094177725107989 16904451355504414580864437)
                  ·
                    refine ⟨1584792314578538866956041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 16904451355504414580864437 1584792314578538866956041)
                    ·
                      refine ⟨1188594235933904150217031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1584792314578538866956041 1188594235933904150217031)
                      ·
                        rfl

theorem cell23_2314779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 6, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 6, 5, 2].length) (baseStart_2314779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2314779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2314779 prefixEnd_2314779 := by exact prefixLift 2314779
  have htrace : WordTrace (prefixWord ++ tailWord_2314779) baseStart_2314779 baseEnd_2314779 := by
    simpa [prefixWord, tailWord_2314779, baseEnd_2314779] using wordTrace_append hprefix tailTrace_2314779
  have hstable : (prefixWord ++ tailWord_2314779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2314779).length < 2 ^ (prefixWord ++ tailWord_2314779).sum := by decide
  have hdescent : baseEnd_2314779 < baseStart_2314779 := by decide
  rcases family_descends (prefixWord ++ tailWord_2314779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2314789 : List Nat := [1, 3, 1, 2, 2, 1, 4, 2, 2, 5]
def baseStart_2314789 : Nat := 118140960795 + 2314789 * 2 ^ 59
def prefixEnd_2314789 : Nat := 4983230072969 + 3 ^ 40 * 2314789 * 2
def baseEnd_2314789 : Nat := 396199790246816370363995

theorem tailTrace_2314789 : CollatzResearch.WordTrace tailWord_2314789 prefixEnd_2314789 396199790246816370363995 := by
  unfold tailWord_2314789
  simp only [CollatzResearch.WordTrace]
  refine ⟨84427290810922262332123421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56284860540614841554748947 84427290810922262332123421)
  ·
    refine ⟨31660234054095848374546283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84427290810922262332123421 31660234054095848374546283)
    ·
      refine ⟨47490351081143772561819425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31660234054095848374546283 47490351081143772561819425)
      ·
        refine ⟨35617763310857829421364569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47490351081143772561819425 35617763310857829421364569)
        ·
          refine ⟨26713322483143372066023427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35617763310857829421364569 26713322483143372066023427)
          ·
            refine ⟨40069983724715058099035141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26713322483143372066023427 40069983724715058099035141)
            ·
              refine ⟨7513121948384073393569089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40069983724715058099035141 7513121948384073393569089)
              ·
                refine ⟨5634841461288055045176817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7513121948384073393569089 5634841461288055045176817)
                ·
                  refine ⟨4226131095966041283882613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5634841461288055045176817 4226131095966041283882613)
                  ·
                    refine ⟨396199790246816370363995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4226131095966041283882613 396199790246816370363995)
                    ·
                      rfl

theorem cell23_2314789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4, 2, 2, 5].length) (baseStart_2314789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2314789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2314789 prefixEnd_2314789 := by exact prefixLift 2314789
  have htrace : WordTrace (prefixWord ++ tailWord_2314789) baseStart_2314789 baseEnd_2314789 := by
    simpa [prefixWord, tailWord_2314789, baseEnd_2314789] using wordTrace_append hprefix tailTrace_2314789
  have hstable : (prefixWord ++ tailWord_2314789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2314789).length < 2 ^ (prefixWord ++ tailWord_2314789).sum := by decide
  have hdescent : baseEnd_2314789 < baseStart_2314789 := by decide
  rcases family_descends (prefixWord ++ tailWord_2314789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2314809 : List Nat := [1, 2, 1, 5, 1, 1, 2, 2, 1, 3, 4]
def baseStart_2314809 : Nat := 118140960795 + 2314809 * 2 ^ 59
def prefixEnd_2314809 : Nat := 4983230072969 + 3 ^ 40 * 2314809 * 2
def baseEnd_2314809 : Nat := 1188609640353539032841893

theorem tailTrace_2314809 : CollatzResearch.WordTrace tailWord_2314809 prefixEnd_2314809 1188609640353539032841893 := by
  unfold tailWord_2314809
  simp only [CollatzResearch.WordTrace]
  refine ⟨84428020270849805747851481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56285346847233203831900987 84428020270849805747851481)
  ·
    refine ⟨63321015203137354310888611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84428020270849805747851481 63321015203137354310888611)
    ·
      refine ⟨94981522804706031466332917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63321015203137354310888611 94981522804706031466332917)
      ·
        refine ⟨8904517762941190449968711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 94981522804706031466332917 8904517762941190449968711)
        ·
          refine ⟨13356776644411785674953067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8904517762941190449968711 13356776644411785674953067)
          ·
            refine ⟨20035164966617678512429601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13356776644411785674953067 20035164966617678512429601)
            ·
              refine ⟨15026373724963258884322201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20035164966617678512429601 15026373724963258884322201)
              ·
                refine ⟨11269780293722444163241651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15026373724963258884322201 11269780293722444163241651)
                ·
                  refine ⟨16904670440583666244862477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11269780293722444163241651 16904670440583666244862477)
                  ·
                    refine ⟨6339251415218874841823429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16904670440583666244862477 6339251415218874841823429)
                    ·
                      refine ⟨1188609640353539032841893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6339251415218874841823429 1188609640353539032841893)
                      ·
                        rfl

theorem cell23_2314809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 2, 1, 3, 4].length) (baseStart_2314809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2314809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2314809 prefixEnd_2314809 := by exact prefixLift 2314809
  have htrace : WordTrace (prefixWord ++ tailWord_2314809) baseStart_2314809 baseEnd_2314809 := by
    simpa [prefixWord, tailWord_2314809, baseEnd_2314809] using wordTrace_append hprefix tailTrace_2314809
  have hstable : (prefixWord ++ tailWord_2314809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2314809).length < 2 ^ (prefixWord ++ tailWord_2314809).sum := by decide
  have hdescent : baseEnd_2314809 < baseStart_2314809 := by decide
  rcases family_descends (prefixWord ++ tailWord_2314809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2314826 : List Nat := [3, 1, 2, 1, 1, 4, 3, 1, 2, 1, 4]
def baseStart_2314826 : Nat := 118140960795 + 2314826 * 2 ^ 59
def prefixEnd_2314826 : Nat := 4983230072969 + 3 ^ 40 * 2314826 * 2
def baseEnd_2314826 : Nat := 1188618369524665466329315

theorem tailTrace_2314826 : CollatzResearch.WordTrace tailWord_2314826 prefixEnd_2314826 1188618369524665466329315 := by
  unfold tailWord_2314826
  simp only [CollatzResearch.WordTrace]
  refine ⟨21107160077947054412805083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56285760207858811767480221 21107160077947054412805083)
  ·
    refine ⟨31660740116920581619207625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21107160077947054412805083 31660740116920581619207625)
    ·
      refine ⟨23745555087690436214405719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31660740116920581619207625 23745555087690436214405719)
      ·
        refine ⟨35618332631535654321608579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23745555087690436214405719 35618332631535654321608579)
        ·
          refine ⟨53427498947303481482412869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35618332631535654321608579 53427498947303481482412869)
          ·
            refine ⟨10017656052619402777952413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 53427498947303481482412869 10017656052619402777952413)
            ·
              refine ⟨3756621019732276041732155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10017656052619402777952413 3756621019732276041732155)
              ·
                refine ⟨5634931529598414062598233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3756621019732276041732155 5634931529598414062598233)
                ·
                  refine ⟨4226198647198810546948675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5634931529598414062598233 4226198647198810546948675)
                  ·
                    refine ⟨6339297970798215820423013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4226198647198810546948675 6339297970798215820423013)
                    ·
                      refine ⟨1188618369524665466329315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6339297970798215820423013 1188618369524665466329315)
                      ·
                        rfl

theorem cell23_2314826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 3, 1, 2, 1, 4].length) (baseStart_2314826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2314826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2314826 prefixEnd_2314826 := by exact prefixLift 2314826
  have htrace : WordTrace (prefixWord ++ tailWord_2314826) baseStart_2314826 baseEnd_2314826 := by
    simpa [prefixWord, tailWord_2314826, baseEnd_2314826] using wordTrace_append hprefix tailTrace_2314826
  have hstable : (prefixWord ++ tailWord_2314826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2314826).length < 2 ^ (prefixWord ++ tailWord_2314826).sum := by decide
  have hdescent : baseEnd_2314826 < baseStart_2314826 := by decide
  rcases family_descends (prefixWord ++ tailWord_2314826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2314849 : List Nat := [1, 2, 3, 1, 1, 5, 1, 1, 8]
def baseStart_2314849 : Nat := 118140960795 + 2314849 * 2 ^ 59
def prefixEnd_2314849 : Nat := 4983230072969 + 3 ^ 40 * 2314849 * 2
def baseEnd_2314849 : Nat := 132070019953302097371301

theorem tailTrace_2314849 : CollatzResearch.WordTrace tailWord_2314849 prefixEnd_2314849 132070019953302097371301 := by
  unfold tailWord_2314849
  simp only [CollatzResearch.WordTrace]
  refine ⟨84429479190704892579307601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56286319460469928386205067 84429479190704892579307601)
  ·
    refine ⟨63322109393028669434480701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84429479190704892579307601 63322109393028669434480701)
    ·
      refine ⟨23745791022385751037930263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63322109393028669434480701 23745791022385751037930263)
      ·
        refine ⟨35618686533578626556895395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23745791022385751037930263 35618686533578626556895395)
        ·
          refine ⟨53428029800367939835343093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35618686533578626556895395 53428029800367939835343093)
          ·
            refine ⟨5008877793784494359563415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 53428029800367939835343093 5008877793784494359563415)
            ·
              refine ⟨7513316690676741539345123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5008877793784494359563415 7513316690676741539345123)
              ·
                refine ⟨11269975036015112309017685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7513316690676741539345123 11269975036015112309017685)
                ·
                  refine ⟨132070019953302097371301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 11269975036015112309017685 132070019953302097371301)
                  ·
                    rfl

theorem cell23_2314849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 1, 1, 8].length) (baseStart_2314849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2314849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2314849 prefixEnd_2314849 := by exact prefixLift 2314849
  have htrace : WordTrace (prefixWord ++ tailWord_2314849) baseStart_2314849 baseEnd_2314849 := by
    simpa [prefixWord, tailWord_2314849, baseEnd_2314849] using wordTrace_append hprefix tailTrace_2314849
  have hstable : (prefixWord ++ tailWord_2314849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2314849).length < 2 ^ (prefixWord ++ tailWord_2314849).sum := by decide
  have hdescent : baseEnd_2314849 < baseStart_2314849 := by decide
  rcases family_descends (prefixWord ++ tailWord_2314849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2314853 : List Nat := [1, 3, 1, 3, 4, 1, 2, 1, 3, 4]
def baseStart_2314853 : Nat := 118140960795 + 2314853 * 2 ^ 59
def prefixEnd_2314853 : Nat := 4983230072969 + 3 ^ 40 * 2314853 * 2
def baseEnd_2314853 : Nat := 396210744500778953563897

theorem tailTrace_2314853 : CollatzResearch.WordTrace tailWord_2314853 prefixEnd_2314853 396210744500778953563897 := by
  unfold tailWord_2314853
  simp only [CollatzResearch.WordTrace]
  refine ⟨84429625082690401262453213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56286416721793600841635475 84429625082690401262453213)
  ·
    refine ⟨31661109406008900473419955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84429625082690401262453213 31661109406008900473419955)
    ·
      refine ⟨47491664109013350710129933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31661109406008900473419955 47491664109013350710129933)
      ·
        refine ⟨17809374040880006516298725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47491664109013350710129933 17809374040880006516298725)
        ·
          refine ⟨3339257632665001221806011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17809374040880006516298725 3339257632665001221806011)
          ·
            refine ⟨5008886448997501832709017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3339257632665001221806011 5008886448997501832709017)
            ·
              refine ⟨3756664836748126374531763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5008886448997501832709017 3756664836748126374531763)
              ·
                refine ⟨5634997255122189561797645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3756664836748126374531763 5634997255122189561797645)
                ·
                  refine ⟨2113123970670821085674117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5634997255122189561797645 2113123970670821085674117)
                  ·
                    refine ⟨396210744500778953563897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2113123970670821085674117 396210744500778953563897)
                    ·
                      rfl

theorem cell23_2314853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 2, 1, 3, 4].length) (baseStart_2314853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2314853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2314853 prefixEnd_2314853 := by exact prefixLift 2314853
  have htrace : WordTrace (prefixWord ++ tailWord_2314853) baseStart_2314853 baseEnd_2314853 := by
    simpa [prefixWord, tailWord_2314853, baseEnd_2314853] using wordTrace_append hprefix tailTrace_2314853
  have hstable : (prefixWord ++ tailWord_2314853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2314853).length < 2 ^ (prefixWord ++ tailWord_2314853).sum := by decide
  have hdescent : baseEnd_2314853 < baseStart_2314853 := by decide
  rcases family_descends (prefixWord ++ tailWord_2314853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2314903 : List Nat := [1, 1, 3, 3, 2, 1, 3, 2, 2, 3, 2]
def baseStart_2314903 : Nat := 118140960795 + 2314903 * 2 ^ 59
def prefixEnd_2314903 : Nat := 4983230072969 + 3 ^ 40 * 2314903 * 2
def baseEnd_2314903 : Nat := 1188657907535061665066461

theorem tailTrace_2314903 : CollatzResearch.WordTrace tailWord_2314903 prefixEnd_2314903 1188657907535061665066461 := by
  unfold tailWord_2314903
  simp only [CollatzResearch.WordTrace]
  refine ⟨84431448732509259801773363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56287632488339506534515575 84431448732509259801773363)
  ·
    refine ⟨126647173098763889702660045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84431448732509259801773363 126647173098763889702660045)
    ·
      refine ⟨47492689912036458638497517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 126647173098763889702660045 47492689912036458638497517)
      ·
        refine ⟨17809758717013671989436569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47492689912036458638497517 17809758717013671989436569)
        ·
          refine ⟨13357319037760253992077427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17809758717013671989436569 13357319037760253992077427)
          ·
            refine ⟨20035978556640380988116141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13357319037760253992077427 20035978556640380988116141)
            ·
              refine ⟨7513491958740142870543553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20035978556640380988116141 7513491958740142870543553)
              ·
                refine ⟨5635118969055107152907665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7513491958740142870543553 5635118969055107152907665)
                ·
                  refine ⟨4226339226791330364680749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5635118969055107152907665 4226339226791330364680749)
                  ·
                    refine ⟨1584877210046748886755281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4226339226791330364680749 1584877210046748886755281)
                    ·
                      refine ⟨1188657907535061665066461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1584877210046748886755281 1188657907535061665066461)
                      ·
                        rfl

theorem cell23_2314903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 3, 2, 2, 3, 2].length) (baseStart_2314903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2314903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2314903 prefixEnd_2314903 := by exact prefixLift 2314903
  have htrace : WordTrace (prefixWord ++ tailWord_2314903) baseStart_2314903 baseEnd_2314903 := by
    simpa [prefixWord, tailWord_2314903, baseEnd_2314903] using wordTrace_append hprefix tailTrace_2314903
  have hstable : (prefixWord ++ tailWord_2314903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2314903).length < 2 ^ (prefixWord ++ tailWord_2314903).sum := by decide
  have hdescent : baseEnd_2314903 < baseStart_2314903 := by decide
  rcases family_descends (prefixWord ++ tailWord_2314903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2314916 : List Nat := [2, 3, 1, 2, 2, 1, 2, 2, 3, 1, 4]
def baseStart_2314916 : Nat := 118140960795 + 2314916 * 2 ^ 59
def prefixEnd_2314916 : Nat := 4983230072969 + 3 ^ 40 * 2314916 * 2
def baseEnd_2314916 : Nat := 1188664582783570114203901

theorem tailTrace_2314916 : CollatzResearch.WordTrace tailWord_2314916 prefixEnd_2314916 1188664582783570114203901 := by
  unfold tailWord_2314916
  simp only [CollatzResearch.WordTrace]
  refine ⟨42215961440731081510998301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56287948587641442014664401 42215961440731081510998301)
  ·
    refine ⟨15830985540274155566624363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42215961440731081510998301 15830985540274155566624363)
    ·
      refine ⟨23746478310411233349936545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15830985540274155566624363 23746478310411233349936545)
      ·
        refine ⟨17809858732808425012452409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23746478310411233349936545 17809858732808425012452409)
        ·
          refine ⟨13357394049606318759339307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17809858732808425012452409 13357394049606318759339307)
          ·
            refine ⟨20036091074409478139008961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13357394049606318759339307 20036091074409478139008961)
            ·
              refine ⟨15027068305807108604256721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20036091074409478139008961 15027068305807108604256721)
              ·
                refine ⟨11270301229355331453192541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15027068305807108604256721 11270301229355331453192541)
                ·
                  refine ⟨4226362961008249294947203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11270301229355331453192541 4226362961008249294947203)
                  ·
                    refine ⟨6339544441512373942420805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4226362961008249294947203 6339544441512373942420805)
                    ·
                      refine ⟨1188664582783570114203901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6339544441512373942420805 1188664582783570114203901)
                      ·
                        rfl

theorem cell23_2314916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 2, 3, 1, 4].length) (baseStart_2314916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2314916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2314916 prefixEnd_2314916 := by exact prefixLift 2314916
  have htrace : WordTrace (prefixWord ++ tailWord_2314916) baseStart_2314916 baseEnd_2314916 := by
    simpa [prefixWord, tailWord_2314916, baseEnd_2314916] using wordTrace_append hprefix tailTrace_2314916
  have hstable : (prefixWord ++ tailWord_2314916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2314916).length < 2 ^ (prefixWord ++ tailWord_2314916).sum := by decide
  have hdescent : baseEnd_2314916 < baseStart_2314916 := by decide
  rcases family_descends (prefixWord ++ tailWord_2314916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2314933 : List Nat := [1, 3, 3, 3, 1, 2, 1, 1, 3, 1, 4]
def baseStart_2314933 : Nat := 118140960795 + 2314933 * 2 ^ 59
def prefixEnd_2314933 : Nat := 4983230072969 + 3 ^ 40 * 2314933 * 2
def baseEnd_2314933 : Nat := 1188673311954696547691323

theorem tailTrace_2314933 : CollatzResearch.WordTrace tailWord_2314933 prefixEnd_2314933 1188673311954696547691323 := by
  unfold tailWord_2314933
  simp only [CollatzResearch.WordTrace]
  refine ⟨84432542922400574925365453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56288361948267049950243635 84432542922400574925365453)
  ·
    refine ⟨31662203595900215597012045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84432542922400574925365453 31662203595900215597012045)
    ·
      refine ⟨11873326348462580848879517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31662203595900215597012045 11873326348462580848879517)
      ·
        refine ⟨4452497380673467818329819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11873326348462580848879517 4452497380673467818329819)
        ·
          refine ⟨6678746071010201727494729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4452497380673467818329819 6678746071010201727494729)
          ·
            refine ⟨5009059553257651295621047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6678746071010201727494729 5009059553257651295621047)
            ·
              refine ⟨7513589329886476943431571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5009059553257651295621047 7513589329886476943431571)
              ·
                refine ⟨11270383994829715415147357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7513589329886476943431571 11270383994829715415147357)
                ·
                  refine ⟨4226393998061143280680259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11270383994829715415147357 4226393998061143280680259)
                  ·
                    refine ⟨6339590997091714921020389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4226393998061143280680259 6339590997091714921020389)
                    ·
                      refine ⟨1188673311954696547691323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6339590997091714921020389 1188673311954696547691323)
                      ·
                        rfl

theorem cell23_2314933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_2314933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2314933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2314933 prefixEnd_2314933 := by exact prefixLift 2314933
  have htrace : WordTrace (prefixWord ++ tailWord_2314933) baseStart_2314933 baseEnd_2314933 := by
    simpa [prefixWord, tailWord_2314933, baseEnd_2314933] using wordTrace_append hprefix tailTrace_2314933
  have hstable : (prefixWord ++ tailWord_2314933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2314933).length < 2 ^ (prefixWord ++ tailWord_2314933).sum := by decide
  have hdescent : baseEnd_2314933 < baseStart_2314933 := by decide
  rcases family_descends (prefixWord ++ tailWord_2314933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2314967 : List Nat := [1, 1, 3, 2, 1, 5, 1, 4, 1, 2, 2]
def baseStart_2314967 : Nat := 118140960795 + 2314967 * 2 ^ 59
def prefixEnd_2314967 : Nat := 4983230072969 + 3 ^ 40 * 2314967 * 2
def baseEnd_2314967 : Nat := 1188690770296949414666167

theorem tailTrace_2314967 : CollatzResearch.WordTrace tailWord_2314967 prefixEnd_2314967 1188690770296949414666167 := by
  unfold tailWord_2314967
  simp only [CollatzResearch.WordTrace]
  refine ⟨84433783004277398732103155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56289188669518265821402103 84433783004277398732103155)
  ·
    refine ⟨126650674506416098098154733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84433783004277398732103155 126650674506416098098154733)
    ·
      refine ⟨47494002939906036786808025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 126650674506416098098154733 47494002939906036786808025)
      ·
        refine ⟨35620502204929527590106019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47494002939906036786808025 35620502204929527590106019)
        ·
          refine ⟨53430753307394291385159029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35620502204929527590106019 53430753307394291385159029)
          ·
            refine ⟨5009133122568214817358659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 53430753307394291385159029 5009133122568214817358659)
            ·
              refine ⟨7513699683852322226037989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5009133122568214817358659 7513699683852322226037989)
              ·
                refine ⟨1408818690722310417382123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7513699683852322226037989 1408818690722310417382123)
                ·
                  refine ⟨2113228036083465626073185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1408818690722310417382123 2113228036083465626073185)
                  ·
                    refine ⟨1584921027062599219554889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2113228036083465626073185 1584921027062599219554889)
                    ·
                      refine ⟨1188690770296949414666167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1584921027062599219554889 1188690770296949414666167)
                      ·
                        rfl

theorem cell23_2314967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 1, 4, 1, 2, 2].length) (baseStart_2314967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2314967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2314967 prefixEnd_2314967 := by exact prefixLift 2314967
  have htrace : WordTrace (prefixWord ++ tailWord_2314967) baseStart_2314967 baseEnd_2314967 := by
    simpa [prefixWord, tailWord_2314967, baseEnd_2314967] using wordTrace_append hprefix tailTrace_2314967
  have hstable : (prefixWord ++ tailWord_2314967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2314967).length < 2 ^ (prefixWord ++ tailWord_2314967).sum := by decide
  have hdescent : baseEnd_2314967 < baseStart_2314967 := by decide
  rcases family_descends (prefixWord ++ tailWord_2314967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2314969 : List Nat := [1, 2, 1, 2, 3, 2, 1, 1, 1, 9]
def baseStart_2314969 : Nat := 118140960795 + 2314969 * 2 ^ 59
def prefixEnd_2314969 : Nat := 4983230072969 + 3 ^ 40 * 2314969 * 2
def baseEnd_2314969 : Nat := 396230599086086135613719

theorem tailTrace_2314969 : CollatzResearch.WordTrace tailWord_2314969 prefixEnd_2314969 396230599086086135613719 := by
  unfold tailWord_2314969
  simp only [CollatzResearch.WordTrace]
  refine ⟨84433855950270153073675961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56289237300180102049117307 84433855950270153073675961)
  ·
    refine ⟨63325391962702614805256971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84433855950270153073675961 63325391962702614805256971)
    ·
      refine ⟨94988087944053922207885457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63325391962702614805256971 94988087944053922207885457)
      ·
        refine ⟨71241065958040441655914093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94988087944053922207885457 71241065958040441655914093)
        ·
          refine ⟨26715399734265165620967785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71241065958040441655914093 26715399734265165620967785)
          ·
            refine ⟨20036549800698874215725839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26715399734265165620967785 20036549800698874215725839)
            ·
              refine ⟨30054824701048311323588759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20036549800698874215725839 30054824701048311323588759)
              ·
                refine ⟨45082237051572466985383139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30054824701048311323588759 45082237051572466985383139)
                ·
                  refine ⟨67623355577358700478074709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45082237051572466985383139 67623355577358700478074709)
                  ·
                    refine ⟨396230599086086135613719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 67623355577358700478074709 396230599086086135613719)
                    ·
                      rfl

theorem cell23_2314969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 1, 1, 9].length) (baseStart_2314969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2314969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2314969 prefixEnd_2314969 := by exact prefixLift 2314969
  have htrace : WordTrace (prefixWord ++ tailWord_2314969) baseStart_2314969 baseEnd_2314969 := by
    simpa [prefixWord, tailWord_2314969, baseEnd_2314969] using wordTrace_append hprefix tailTrace_2314969
  have hstable : (prefixWord ++ tailWord_2314969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2314969).length < 2 ^ (prefixWord ++ tailWord_2314969).sum := by decide
  have hdescent : baseEnd_2314969 < baseStart_2314969 := by decide
  rcases family_descends (prefixWord ++ tailWord_2314969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2314993 : List Nat := [1, 2, 2, 2, 2, 2, 1, 3, 3, 3, 2]
def baseStart_2314993 : Nat := 118140960795 + 2314993 * 2 ^ 59
def prefixEnd_2314993 : Nat := 4983230072969 + 3 ^ 40 * 2314993 * 2
def baseEnd_2314993 : Nat := 1188704120793966312941047

theorem tailTrace_2314993 : CollatzResearch.WordTrace tailWord_2314993 prefixEnd_2314993 1188704120793966312941047 := by
  unfold tailWord_2314993
  simp only [CollatzResearch.WordTrace]
  refine ⟨84434731302183205172549633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56289820868122136781699755 84434731302183205172549633)
  ·
    refine ⟨63326048476637403879412225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84434731302183205172549633 63326048476637403879412225)
    ·
      refine ⟨47494536357478052909559169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63326048476637403879412225 47494536357478052909559169)
      ·
        refine ⟨35620902268108539682169377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47494536357478052909559169 35620902268108539682169377)
        ·
          refine ⟨26715676701081404761627033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35620902268108539682169377 26715676701081404761627033)
          ·
            refine ⟨20036757525811053571220275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26715676701081404761627033 20036757525811053571220275)
            ·
              refine ⟨30055136288716580356830413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20036757525811053571220275 30055136288716580356830413)
              ·
                refine ⟨11270676108268717633811405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30055136288716580356830413 11270676108268717633811405)
                ·
                  refine ⟨4226503540600769112679277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11270676108268717633811405 4226503540600769112679277)
                  ·
                    refine ⟨1584938827725288417254729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4226503540600769112679277 1584938827725288417254729)
                    ·
                      refine ⟨1188704120793966312941047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1584938827725288417254729 1188704120793966312941047)
                      ·
                        rfl

theorem cell23_2314993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 3, 3, 3, 2].length) (baseStart_2314993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2314993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2314993 prefixEnd_2314993 := by exact prefixLift 2314993
  have htrace : WordTrace (prefixWord ++ tailWord_2314993) baseStart_2314993 baseEnd_2314993 := by
    simpa [prefixWord, tailWord_2314993, baseEnd_2314993] using wordTrace_append hprefix tailTrace_2314993
  have hstable : (prefixWord ++ tailWord_2314993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2314993).length < 2 ^ (prefixWord ++ tailWord_2314993).sum := by decide
  have hdescent : baseEnd_2314993 < baseStart_2314993 := by decide
  rcases family_descends (prefixWord ++ tailWord_2314993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2314999 : List Nat := [1, 1, 3, 1, 1, 1, 3, 1, 3, 8]
def baseStart_2314999 : Nat := 118140960795 + 2314999 * 2 ^ 59
def prefixEnd_2314999 : Nat := 4983230072969 + 3 ^ 40 * 2314999 * 2
def baseEnd_2314999 : Nat := 396235733892631096488673

theorem tailTrace_2314999 : CollatzResearch.WordTrace tailWord_2314999 prefixEnd_2314999 396235733892631096488673 := by
  unfold tailWord_2314999
  simp only [CollatzResearch.WordTrace]
  refine ⟨84434950140161468197268051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56289966760107645464845367 84434950140161468197268051)
  ·
    refine ⟨126652425210242202295902077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84434950140161468197268051 126652425210242202295902077)
    ·
      refine ⟨47494659453840825860963279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 126652425210242202295902077 47494659453840825860963279)
      ·
        refine ⟨71241989180761238791444919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47494659453840825860963279 71241989180761238791444919)
        ·
          refine ⟨106862983771141858187167379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71241989180761238791444919 106862983771141858187167379)
          ·
            refine ⟨160294475656712787280751069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106862983771141858187167379 160294475656712787280751069)
            ·
              refine ⟨60110428371267295230281651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 160294475656712787280751069 60110428371267295230281651)
              ·
                refine ⟨90165642556900942845422477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60110428371267295230281651 90165642556900942845422477)
                ·
                  refine ⟨33812115958837853567033429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 90165642556900942845422477 33812115958837853567033429)
                  ·
                    refine ⟨396235733892631096488673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 33812115958837853567033429 396235733892631096488673)
                    ·
                      rfl

theorem cell23_2314999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 1, 3, 8].length) (baseStart_2314999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2314999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2314999 prefixEnd_2314999 := by exact prefixLift 2314999
  have htrace : WordTrace (prefixWord ++ tailWord_2314999) baseStart_2314999 baseEnd_2314999 := by
    simpa [prefixWord, tailWord_2314999, baseEnd_2314999] using wordTrace_append hprefix tailTrace_2314999
  have hstable : (prefixWord ++ tailWord_2314999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2314999).length < 2 ^ (prefixWord ++ tailWord_2314999).sum := by decide
  have hdescent : baseEnd_2314999 < baseStart_2314999 := by decide
  rcases family_descends (prefixWord ++ tailWord_2314999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2315016 : List Nat := [2, 1, 3, 2, 2, 2, 1, 2, 2, 6]
def baseStart_2315016 : Nat := 118140960795 + 2315016 * 2 ^ 59
def prefixEnd_2315016 : Nat := 4983230072969 + 3 ^ 40 * 2315016 * 2
def baseEnd_2315016 : Nat := 396238643616339907651147

theorem tailTrace_2315016 : CollatzResearch.WordTrace tailWord_2315016 prefixEnd_2315016 396238643616339907651147 := by
  unfold tailWord_2315016
  simp only [CollatzResearch.WordTrace]
  refine ⟨42217785090549940050318451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56290380120733253400424601 42217785090549940050318451)
  ·
    refine ⟨63326677635824910075477677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42217785090549940050318451 63326677635824910075477677)
    ·
      refine ⟨23747504113434341278304129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63326677635824910075477677 23747504113434341278304129)
      ·
        refine ⟨17810628085075755958728097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23747504113434341278304129 17810628085075755958728097)
        ·
          refine ⟨13357971063806816969046073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17810628085075755958728097 13357971063806816969046073)
          ·
            refine ⟨10018478297855112726784555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13357971063806816969046073 10018478297855112726784555)
            ·
              refine ⟨15027717446782669090176833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10018478297855112726784555 15027717446782669090176833)
              ·
                refine ⟨11270788085087001817632625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15027717446782669090176833 11270788085087001817632625)
                ·
                  refine ⟨8453091063815251363224469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11270788085087001817632625 8453091063815251363224469)
                  ·
                    refine ⟨396238643616339907651147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8453091063815251363224469 396238643616339907651147)
                    ·
                      rfl

theorem cell23_2315016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 2, 2, 6].length) (baseStart_2315016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2315016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2315016 prefixEnd_2315016 := by exact prefixLift 2315016
  have htrace : WordTrace (prefixWord ++ tailWord_2315016) baseStart_2315016 baseEnd_2315016 := by
    simpa [prefixWord, tailWord_2315016, baseEnd_2315016] using wordTrace_append hprefix tailTrace_2315016
  have hstable : (prefixWord ++ tailWord_2315016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2315016).length < 2 ^ (prefixWord ++ tailWord_2315016).sum := by decide
  have hdescent : baseEnd_2315016 < baseStart_2315016 := by decide
  rcases family_descends (prefixWord ++ tailWord_2315016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2315040 : List Nat := [2, 1, 1, 5, 1, 2, 3, 1, 1, 4, 2]
def baseStart_2315040 : Nat := 118140960795 + 2315040 * 2 ^ 59
def prefixEnd_2315040 : Nat := 4983230072969 + 3 ^ 40 * 2315040 * 2
def baseEnd_2315040 : Nat := 1188728254384727629053331

theorem tailTrace_2315040 : CollatzResearch.WordTrace tailWord_2315040 prefixEnd_2315040 1188728254384727629053331 := by
  unfold tailWord_2315040
  simp only [CollatzResearch.WordTrace]
  refine ⟨42218222766506466099755287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56290963688675288133007049 42218222766506466099755287)
  ·
    refine ⟨63327334149759699149632931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42218222766506466099755287 63327334149759699149632931)
    ·
      refine ⟨94991001224639548724449397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63327334149759699149632931 94991001224639548724449397)
      ·
        refine ⟨8905406364809957692917131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 94991001224639548724449397 8905406364809957692917131)
        ·
          refine ⟨13358109547214936539375697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8905406364809957692917131 13358109547214936539375697)
          ·
            refine ⟨10018582160411202404531773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13358109547214936539375697 10018582160411202404531773)
            ·
              refine ⟨3756968310154200901699415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10018582160411202404531773 3756968310154200901699415)
              ·
                refine ⟨5635452465231301352549123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3756968310154200901699415 5635452465231301352549123)
                ·
                  refine ⟨8453178697846952028823685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5635452465231301352549123 8453178697846952028823685)
                  ·
                    refine ⟨1584971005846303505404441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8453178697846952028823685 1584971005846303505404441)
                    ·
                      refine ⟨1188728254384727629053331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1584971005846303505404441 1188728254384727629053331)
                      ·
                        rfl

theorem cell23_2315040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 3, 1, 1, 4, 2].length) (baseStart_2315040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2315040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2315040 prefixEnd_2315040 := by exact prefixLift 2315040
  have htrace : WordTrace (prefixWord ++ tailWord_2315040) baseStart_2315040 baseEnd_2315040 := by
    simpa [prefixWord, tailWord_2315040, baseEnd_2315040] using wordTrace_append hprefix tailTrace_2315040
  have hstable : (prefixWord ++ tailWord_2315040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2315040).length < 2 ^ (prefixWord ++ tailWord_2315040).sum := by decide
  have hdescent : baseEnd_2315040 < baseStart_2315040 := by decide
  rcases family_descends (prefixWord ++ tailWord_2315040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2315056 : List Nat := [2, 1, 1, 1, 2, 2, 1, 4, 1, 5, 3]
def baseStart_2315056 : Nat := 118140960795 + 2315056 * 2 ^ 59
def prefixEnd_2315056 : Nat := 4983230072969 + 3 ^ 40 * 2315056 * 2
def baseEnd_2315056 : Nat := 1188736470075199566453257

theorem tailTrace_2315056 : CollatzResearch.WordTrace tailWord_2315056 prefixEnd_2315056 1188736470075199566453257 := by
  unfold tailWord_2315056
  simp only [CollatzResearch.WordTrace]
  refine ⟨42218514550477483466046511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56291352733969977954728681 42218514550477483466046511)
  ·
    refine ⟨63327771825716225199069767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42218514550477483466046511 63327771825716225199069767)
    ·
      refine ⟨94991657738574337798604651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63327771825716225199069767 94991657738574337798604651)
      ·
        refine ⟨142487486607861506697906977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94991657738574337798604651 142487486607861506697906977)
        ·
          refine ⟨106865614955896130023430233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 142487486607861506697906977 106865614955896130023430233)
          ·
            refine ⟨80149211216922097517572675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 106865614955896130023430233 80149211216922097517572675)
            ·
              refine ⟨120223816825383146276359013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80149211216922097517572675 120223816825383146276359013)
              ·
                refine ⟨22541965654759339926817315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 120223816825383146276359013 22541965654759339926817315)
                ·
                  refine ⟨33812948482139009890225973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22541965654759339926817315 33812948482139009890225973)
                  ·
                    refine ⟨3169963920200532177208685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 33812948482139009890225973 3169963920200532177208685)
                    ·
                      refine ⟨1188736470075199566453257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3169963920200532177208685 1188736470075199566453257)
                      ·
                        rfl

theorem cell23_2315056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 4, 1, 5, 3].length) (baseStart_2315056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2315056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2315056 prefixEnd_2315056 := by exact prefixLift 2315056
  have htrace : WordTrace (prefixWord ++ tailWord_2315056) baseStart_2315056 baseEnd_2315056 := by
    simpa [prefixWord, tailWord_2315056, baseEnd_2315056] using wordTrace_append hprefix tailTrace_2315056
  have hstable : (prefixWord ++ tailWord_2315056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2315056).length < 2 ^ (prefixWord ++ tailWord_2315056).sum := by decide
  have hdescent : baseEnd_2315056 < baseStart_2315056 := by decide
  rcases family_descends (prefixWord ++ tailWord_2315056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2315060 : List Nat := [2, 5, 1, 1, 3, 1, 1, 1, 2, 1, 5]
def baseStart_2315060 : Nat := 118140960795 + 2315060 * 2 ^ 59
def prefixEnd_2315060 : Nat := 4983230072969 + 3 ^ 40 * 2315060 * 2
def baseEnd_2315060 : Nat := 1188738523997817550803239

theorem tailTrace_2315060 : CollatzResearch.WordTrace tailWord_2315060 prefixEnd_2315060 1188738523997817550803239 := by
  unfold tailWord_2315060
  simp only [CollatzResearch.WordTrace]
  refine ⟨42218587496470237807619317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56291449995293650410159089 42218587496470237807619317)
  ·
    refine ⟨3957992577794084794464311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 42218587496470237807619317 3957992577794084794464311)
    ·
      refine ⟨5936988866691127191696467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3957992577794084794464311 5936988866691127191696467)
      ·
        refine ⟨8905483300036690787544701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5936988866691127191696467 8905483300036690787544701)
        ·
          refine ⟨3339556237513759045329263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8905483300036690787544701 3339556237513759045329263)
          ·
            refine ⟨5009334356270638567993895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3339556237513759045329263 5009334356270638567993895)
            ·
              refine ⟨7514001534405957851990843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5009334356270638567993895 7514001534405957851990843)
              ·
                refine ⟨11271002301608936777986265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7514001534405957851990843 11271002301608936777986265)
                ·
                  refine ⟨8453251726206702583489699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11271002301608936777986265 8453251726206702583489699)
                  ·
                    refine ⟨12679877589310053875234549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8453251726206702583489699 12679877589310053875234549)
                    ·
                      refine ⟨1188738523997817550803239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12679877589310053875234549 1188738523997817550803239)
                      ·
                        rfl

theorem cell23_2315060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 1, 1, 2, 1, 5].length) (baseStart_2315060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2315060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2315060 prefixEnd_2315060 := by exact prefixLift 2315060
  have htrace : WordTrace (prefixWord ++ tailWord_2315060) baseStart_2315060 baseEnd_2315060 := by
    simpa [prefixWord, tailWord_2315060, baseEnd_2315060] using wordTrace_append hprefix tailTrace_2315060
  have hstable : (prefixWord ++ tailWord_2315060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2315060).length < 2 ^ (prefixWord ++ tailWord_2315060).sum := by decide
  have hdescent : baseEnd_2315060 < baseStart_2315060 := by decide
  rcases family_descends (prefixWord ++ tailWord_2315060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2315080 : List Nat := [2, 1, 3, 1, 1, 3, 5, 2, 5]
def baseStart_2315080 : Nat := 118140960795 + 2315080 * 2 ^ 59
def prefixEnd_2315080 : Nat := 4983230072969 + 3 ^ 40 * 2315080 * 2
def baseEnd_2315080 : Nat := 132083199290100830283683

theorem tailTrace_2315080 : CollatzResearch.WordTrace tailWord_2315080 prefixEnd_2315080 132083199290100830283683 := by
  unfold tailWord_2315080
  simp only [CollatzResearch.WordTrace]
  refine ⟨42218952226434009515483347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56291936301912012687311129 42218952226434009515483347)
  ·
    refine ⟨63328428339651014273225021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42218952226434009515483347 63328428339651014273225021)
    ·
      refine ⟨23748160627369130352459383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63328428339651014273225021 23748160627369130352459383)
      ·
        refine ⟨35622240941053695528689075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23748160627369130352459383 35622240941053695528689075)
        ·
          refine ⟨53433361411580543293033613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35622240941053695528689075 53433361411580543293033613)
          ·
            refine ⟨20037510529342703734887605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53433361411580543293033613 20037510529342703734887605)
            ·
              refine ⟨1878516612125878475145713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20037510529342703734887605 1878516612125878475145713)
              ·
                refine ⟨1408887459094408856359285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1878516612125878475145713 1408887459094408856359285)
                ·
                  refine ⟨132083199290100830283683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1408887459094408856359285 132083199290100830283683)
                  ·
                    rfl

theorem cell23_2315080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 5, 2, 5].length) (baseStart_2315080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2315080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2315080 prefixEnd_2315080 := by exact prefixLift 2315080
  have htrace : WordTrace (prefixWord ++ tailWord_2315080) baseStart_2315080 baseEnd_2315080 := by
    simpa [prefixWord, tailWord_2315080, baseEnd_2315080] using wordTrace_append hprefix tailTrace_2315080
  have hstable : (prefixWord ++ tailWord_2315080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2315080).length < 2 ^ (prefixWord ++ tailWord_2315080).sum := by decide
  have hdescent : baseEnd_2315080 < baseStart_2315080 := by decide
  rcases family_descends (prefixWord ++ tailWord_2315080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2315096 : List Nat := [2, 1, 2, 2, 1, 1, 1, 3, 3, 3, 4]
def baseStart_2315096 : Nat := 118140960795 + 2315096 * 2 ^ 59
def prefixEnd_2315096 : Nat := 4983230072969 + 3 ^ 40 * 2315096 * 2
def baseEnd_2315096 : Nat := 1188757009301379409953073

theorem tailTrace_2315096 : CollatzResearch.WordTrace tailWord_2315096 prefixEnd_2315096 1188757009301379409953073 := by
  unfold tailWord_2315096
  simp only [CollatzResearch.WordTrace]
  refine ⟨42219244010405026881774571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56292325347206702509032761 42219244010405026881774571)
  ·
    refine ⟨63328866015607540322661857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42219244010405026881774571 63328866015607540322661857)
    ·
      refine ⟨47496649511705655241996393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63328866015607540322661857 47496649511705655241996393)
      ·
        refine ⟨35622487133779241431497295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47496649511705655241996393 35622487133779241431497295)
        ·
          refine ⟨53433730700668862147245943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35622487133779241431497295 53433730700668862147245943)
          ·
            refine ⟨80150596051003293220868915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53433730700668862147245943 80150596051003293220868915)
            ·
              refine ⟨120225894076504939831303373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80150596051003293220868915 120225894076504939831303373)
              ·
                refine ⟨45084710278689352436738765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 120225894076504939831303373 45084710278689352436738765)
                ·
                  refine ⟨16906766354508507163777037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45084710278689352436738765 16906766354508507163777037)
                  ·
                    refine ⟨6340037382940690186416389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16906766354508507163777037 6340037382940690186416389)
                    ·
                      refine ⟨1188757009301379409953073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6340037382940690186416389 1188757009301379409953073)
                      ·
                        rfl

theorem cell23_2315096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 3, 3, 3, 4].length) (baseStart_2315096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2315096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2315096 prefixEnd_2315096 := by exact prefixLift 2315096
  have htrace : WordTrace (prefixWord ++ tailWord_2315096) baseStart_2315096 baseEnd_2315096 := by
    simpa [prefixWord, tailWord_2315096, baseEnd_2315096] using wordTrace_append hprefix tailTrace_2315096
  have hstable : (prefixWord ++ tailWord_2315096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2315096).length < 2 ^ (prefixWord ++ tailWord_2315096).sum := by decide
  have hdescent : baseEnd_2315096 < baseStart_2315096 := by decide
  rcases family_descends (prefixWord ++ tailWord_2315096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2315113 : List Nat := [1, 2, 1, 1, 1, 3, 1, 1, 6, 4, 2]
def baseStart_2315113 : Nat := 118140960795 + 2315113 * 2 ^ 59
def prefixEnd_2315113 : Nat := 4983230072969 + 3 ^ 40 * 2315113 * 2
def baseEnd_2315113 : Nat := 1188765738472505843440495

theorem tailTrace_2315113 : CollatzResearch.WordTrace tailWord_2315113 prefixEnd_2315113 1188765738472505843440495 := by
  unfold tailWord_2315113
  simp only [CollatzResearch.WordTrace]
  refine ⟨84439108061748465666917993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56292738707832310444611995 84439108061748465666917993)
  ·
    refine ⟨63329331046311349250188495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84439108061748465666917993 63329331046311349250188495)
    ·
      refine ⟨94993996569467023875282743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63329331046311349250188495 94993996569467023875282743)
      ·
        refine ⟨142490994854200535812924115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94993996569467023875282743 142490994854200535812924115)
        ·
          refine ⟨213736492281300803719386173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142490994854200535812924115 213736492281300803719386173)
          ·
            refine ⟨80151184605487801394769815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 213736492281300803719386173 80151184605487801394769815)
            ·
              refine ⟨120226776908231702092154723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80151184605487801394769815 120226776908231702092154723)
              ·
                refine ⟨180340165362347553138232085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 120226776908231702092154723 180340165362347553138232085)
                ·
                  refine ⟨8453445251360041553354629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 180340165362347553138232085 8453445251360041553354629)
                  ·
                    refine ⟨1585020984630007791253993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8453445251360041553354629 1585020984630007791253993)
                    ·
                      refine ⟨1188765738472505843440495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1585020984630007791253993 1188765738472505843440495)
                      ·
                        rfl

theorem cell23_2315113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 6, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 6, 4, 2].length) (baseStart_2315113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2315113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2315113 prefixEnd_2315113 := by exact prefixLift 2315113
  have htrace : WordTrace (prefixWord ++ tailWord_2315113) baseStart_2315113 baseEnd_2315113 := by
    simpa [prefixWord, tailWord_2315113, baseEnd_2315113] using wordTrace_append hprefix tailTrace_2315113
  have hstable : (prefixWord ++ tailWord_2315113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2315113).length < 2 ^ (prefixWord ++ tailWord_2315113).sum := by decide
  have hdescent : baseEnd_2315113 < baseStart_2315113 := by decide
  rcases family_descends (prefixWord ++ tailWord_2315113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2315164 : List Nat := [2, 2, 3, 3, 3, 1, 1, 1, 2, 1, 4]
def baseStart_2315164 : Nat := 118140960795 + 2315164 * 2 ^ 59
def prefixEnd_2315164 : Nat := 4983230072969 + 3 ^ 40 * 2315164 * 2
def baseEnd_2315164 : Nat := 1188791925985885143902761

theorem tailTrace_2315164 : CollatzResearch.WordTrace tailWord_2315164 prefixEnd_2315164 1188791925985885143902761 := by
  unfold tailWord_2315164
  simp only [CollatzResearch.WordTrace]
  refine ⟨42220484092281850688512273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56293978789709134251349697 42220484092281850688512273)
  ·
    refine ⟨31665363069211388016384205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42220484092281850688512273 31665363069211388016384205)
    ·
      refine ⟨11874511150954270506144077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31665363069211388016384205 11874511150954270506144077)
      ·
        refine ⟨4452941681607851439804029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11874511150954270506144077 4452941681607851439804029)
        ·
          refine ⟨1669853130602944289926511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4452941681607851439804029 1669853130602944289926511)
          ·
            refine ⟨2504779695904416434889767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1669853130602944289926511 2504779695904416434889767)
            ·
              refine ⟨3757169543856624652334651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2504779695904416434889767 3757169543856624652334651)
              ·
                refine ⟨5635754315784936978501977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3757169543856624652334651 5635754315784936978501977)
                ·
                  refine ⟨4226815736838702733876483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5635754315784936978501977 4226815736838702733876483)
                  ·
                    refine ⟨6340223605258054100814725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4226815736838702733876483 6340223605258054100814725)
                    ·
                      refine ⟨1188791925985885143902761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6340223605258054100814725 1188791925985885143902761)
                      ·
                        rfl

theorem cell23_2315164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 1, 1, 2, 1, 4].length) (baseStart_2315164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2315164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2315164 prefixEnd_2315164 := by exact prefixLift 2315164
  have htrace : WordTrace (prefixWord ++ tailWord_2315164) baseStart_2315164 baseEnd_2315164 := by
    simpa [prefixWord, tailWord_2315164, baseEnd_2315164] using wordTrace_append hprefix tailTrace_2315164
  have hstable : (prefixWord ++ tailWord_2315164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2315164).length < 2 ^ (prefixWord ++ tailWord_2315164).sum := by decide
  have hdescent : baseEnd_2315164 < baseStart_2315164 := by decide
  rcases family_descends (prefixWord ++ tailWord_2315164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2315167 : List Nat := [1, 1, 2, 5, 2, 3, 1, 1, 2, 2, 3]
def baseStart_2315167 : Nat := 118140960795 + 2315167 * 2 ^ 59
def prefixEnd_2315167 : Nat := 4983230072969 + 3 ^ 40 * 2315167 * 2
def baseEnd_2315167 : Nat := 1188793466427848632165247

theorem tailTrace_2315167 : CollatzResearch.WordTrace tailWord_2315167 prefixEnd_2315167 1188793466427848632165247 := by
  unfold tailWord_2315167
  simp only [CollatzResearch.WordTrace]
  refine ⟨84441077603552832889383755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56294051735701888592922503 84441077603552832889383755)
  ·
    refine ⟨126661616405329249334075633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84441077603552832889383755 126661616405329249334075633)
    ·
      refine ⟨94996212303996937000556725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126661616405329249334075633 94996212303996937000556725)
      ·
        refine ⟨8905894903499712843802193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 94996212303996937000556725 8905894903499712843802193)
        ·
          refine ⟨6679421177624784632851645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8905894903499712843802193 6679421177624784632851645)
          ·
            refine ⟨2504782941609294237319367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6679421177624784632851645 2504782941609294237319367)
            ·
              refine ⟨3757174412413941355979051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2504782941609294237319367 3757174412413941355979051)
              ·
                refine ⟨5635761618620912033968577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3757174412413941355979051 5635761618620912033968577)
                ·
                  refine ⟨4226821213965684025476433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5635761618620912033968577 4226821213965684025476433)
                  ·
                    refine ⟨3170115910474263019107325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4226821213965684025476433 3170115910474263019107325)
                    ·
                      refine ⟨1188793466427848632165247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3170115910474263019107325 1188793466427848632165247)
                      ·
                        rfl

theorem cell23_2315167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 1, 1, 2, 2, 3].length) (baseStart_2315167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2315167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2315167 prefixEnd_2315167 := by exact prefixLift 2315167
  have htrace : WordTrace (prefixWord ++ tailWord_2315167) baseStart_2315167 baseEnd_2315167 := by
    simpa [prefixWord, tailWord_2315167, baseEnd_2315167] using wordTrace_append hprefix tailTrace_2315167
  have hstable : (prefixWord ++ tailWord_2315167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2315167).length < 2 ^ (prefixWord ++ tailWord_2315167).sum := by decide
  have hdescent : baseEnd_2315167 < baseStart_2315167 := by decide
  rcases family_descends (prefixWord ++ tailWord_2315167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2315204 : List Nat := [2, 3, 3, 3, 1, 1, 3, 1, 6]
def baseStart_2315204 : Nat := 118140960795 + 2315204 * 2 ^ 59
def prefixEnd_2315204 : Nat := 4983230072969 + 3 ^ 40 * 2315204 * 2
def baseEnd_2315204 : Nat := 132090273912451665266953

theorem tailTrace_2315204 : CollatzResearch.WordTrace tailWord_2315204 prefixEnd_2315204 132090273912451665266953 := by
  unfold tailWord_2315204
  simp only [CollatzResearch.WordTrace]
  refine ⟨42221213552209394104240333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56294951402945858805653777 42221213552209394104240333)
  ·
    refine ⟨15832955082078522789090125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42221213552209394104240333 15832955082078522789090125)
    ·
      refine ⟨5937358155779446045908797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15832955082078522789090125 5937358155779446045908797)
      ·
        refine ⟨2226509308417292267215799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5937358155779446045908797 2226509308417292267215799)
        ·
          refine ⟨3339763962625938400823699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2226509308417292267215799 3339763962625938400823699)
          ·
            refine ⟨5009645943938907601235549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3339763962625938400823699 5009645943938907601235549)
            ·
              refine ⟨1878617228977090350463331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5009645943938907601235549 1878617228977090350463331)
              ·
                refine ⟨2817925843465635525694997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1878617228977090350463331 2817925843465635525694997)
                ·
                  refine ⟨132090273912451665266953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2817925843465635525694997 132090273912451665266953)
                  ·
                    rfl

theorem cell23_2315204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 3, 1, 6].length) (baseStart_2315204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2315204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2315204 prefixEnd_2315204 := by exact prefixLift 2315204
  have htrace : WordTrace (prefixWord ++ tailWord_2315204) baseStart_2315204 baseEnd_2315204 := by
    simpa [prefixWord, tailWord_2315204, baseEnd_2315204] using wordTrace_append hprefix tailTrace_2315204
  have hstable : (prefixWord ++ tailWord_2315204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2315204).length < 2 ^ (prefixWord ++ tailWord_2315204).sum := by decide
  have hdescent : baseEnd_2315204 < baseStart_2315204 := by decide
  rcases family_descends (prefixWord ++ tailWord_2315204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2315231 : List Nat := [1, 1, 2, 3, 5, 2, 1, 3, 1, 1, 3]
def baseStart_2315231 : Nat := 118140960795 + 2315231 * 2 ^ 59
def prefixEnd_2315231 : Nat := 4983230072969 + 3 ^ 40 * 2315231 * 2
def baseEnd_2315231 : Nat := 1188826329189736381764953

theorem tailTrace_2315231 : CollatzResearch.WordTrace tailWord_2315231 prefixEnd_2315231 1188826329189736381764953 := by
  unfold tailWord_2315231
  simp only [CollatzResearch.WordTrace]
  refine ⟨84443411875320971819713547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56295607916880647879809031 84443411875320971819713547)
  ·
    refine ⟨126665117812981457729570321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84443411875320971819713547 126665117812981457729570321)
    ·
      refine ⟨94998838359736093297177741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126665117812981457729570321 94998838359736093297177741)
      ·
        refine ⟨35624564384901034986441653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 94998838359736093297177741 35624564384901034986441653)
        ·
          refine ⟨3339802911084472029978905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 35624564384901034986441653 3339802911084472029978905)
          ·
            refine ⟨2504852183313354022484179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3339802911084472029978905 2504852183313354022484179)
            ·
              refine ⟨3757278274970031033726269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2504852183313354022484179 3757278274970031033726269)
              ·
                refine ⟨1408979353113761637647351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3757278274970031033726269 1408979353113761637647351)
                ·
                  refine ⟨2113469029670642456471027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1408979353113761637647351 2113469029670642456471027)
                  ·
                    refine ⟨3170203544505963684706541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2113469029670642456471027 3170203544505963684706541)
                    ·
                      refine ⟨1188826329189736381764953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3170203544505963684706541 1188826329189736381764953)
                      ·
                        rfl

theorem cell23_2315231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 1, 3, 1, 1, 3].length) (baseStart_2315231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2315231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2315231 prefixEnd_2315231 := by exact prefixLift 2315231
  have htrace : WordTrace (prefixWord ++ tailWord_2315231) baseStart_2315231 baseEnd_2315231 := by
    simpa [prefixWord, tailWord_2315231, baseEnd_2315231] using wordTrace_append hprefix tailTrace_2315231
  have hstable : (prefixWord ++ tailWord_2315231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2315231).length < 2 ^ (prefixWord ++ tailWord_2315231).sum := by decide
  have hdescent : baseEnd_2315231 < baseStart_2315231 := by decide
  rcases family_descends (prefixWord ++ tailWord_2315231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2315233 : List Nat := [1, 2, 3, 1, 2, 1, 1, 3, 3, 2, 4]
def baseStart_2315233 : Nat := 118140960795 + 2315233 * 2 ^ 59
def prefixEnd_2315233 : Nat := 4983230072969 + 3 ^ 40 * 2315233 * 2
def baseEnd_2315233 : Nat := 1188827356151045373939943

theorem tailTrace_2315233 : CollatzResearch.WordTrace tailWord_2315233 prefixEnd_2315233 1188827356151045373939943 := by
  unfold tailWord_2315233
  simp only [CollatzResearch.WordTrace]
  refine ⟨84443484821313726161286353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56295656547542484107524235 84443484821313726161286353)
  ·
    refine ⟨63332613615985294620964765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84443484821313726161286353 63332613615985294620964765)
    ·
      refine ⟨23749730105994485482861787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63332613615985294620964765 23749730105994485482861787)
      ·
        refine ⟨35624595158991728224292681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23749730105994485482861787 35624595158991728224292681)
        ·
          refine ⟨26718446369243796168219511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35624595158991728224292681 26718446369243796168219511)
          ·
            refine ⟨40077669553865694252329267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26718446369243796168219511 40077669553865694252329267)
            ·
              refine ⟨60116504330798541378493901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40077669553865694252329267 60116504330798541378493901)
              ·
                refine ⟨22543689124049453016935213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 60116504330798541378493901 22543689124049453016935213)
                ·
                  refine ⟨8453883421518544881350705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22543689124049453016935213 8453883421518544881350705)
                  ·
                    refine ⟨6340412566138908661013029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8453883421518544881350705 6340412566138908661013029)
                    ·
                      refine ⟨1188827356151045373939943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6340412566138908661013029 1188827356151045373939943)
                      ·
                        rfl

theorem cell23_2315233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 3, 3, 2, 4].length) (baseStart_2315233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2315233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2315233 prefixEnd_2315233 := by exact prefixLift 2315233
  have htrace : WordTrace (prefixWord ++ tailWord_2315233) baseStart_2315233 baseEnd_2315233 := by
    simpa [prefixWord, tailWord_2315233, baseEnd_2315233] using wordTrace_append hprefix tailTrace_2315233
  have hstable : (prefixWord ++ tailWord_2315233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2315233).length < 2 ^ (prefixWord ++ tailWord_2315233).sum := by decide
  have hdescent : baseEnd_2315233 < baseStart_2315233 := by decide
  rcases family_descends (prefixWord ++ tailWord_2315233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2315274 : List Nat := [3, 1, 2, 2, 3, 3, 1, 2, 1, 2, 3]
def baseStart_2315274 : Nat := 118140960795 + 2315274 * 2 ^ 59
def prefixEnd_2315274 : Nat := 4983230072969 + 3 ^ 40 * 2315274 * 2
def baseEnd_2315274 : Nat := 1188848408857879713527255

theorem tailTrace_2315274 : CollatzResearch.WordTrace tailWord_2315274 prefixEnd_2315274 1188848408857879713527255 := by
  unfold tailWord_2315274
  simp only [CollatzResearch.WordTrace]
  refine ⟨21111245053541297540882219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56296653476110126775685917 21111245053541297540882219)
  ·
    refine ⟨31666867580311946311323329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21111245053541297540882219 31666867580311946311323329)
    ·
      refine ⟨23750150685233959733492497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31666867580311946311323329 23750150685233959733492497)
      ·
        refine ⟨17812613013925469800119373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23750150685233959733492497 17812613013925469800119373)
        ·
          refine ⟨6679729880222051175044765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17812613013925469800119373 6679729880222051175044765)
          ·
            refine ⟨2504898705083269190641787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6679729880222051175044765 2504898705083269190641787)
            ·
              refine ⟨3757348057624903785962681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2504898705083269190641787 3757348057624903785962681)
              ·
                refine ⟨2818011043218677839472011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3757348057624903785962681 2818011043218677839472011)
                ·
                  refine ⟨4227016564828016759208017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2818011043218677839472011 4227016564828016759208017)
                  ·
                    refine ⟨3170262423621012569406013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4227016564828016759208017 3170262423621012569406013)
                    ·
                      refine ⟨1188848408857879713527255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3170262423621012569406013 1188848408857879713527255)
                      ·
                        rfl

theorem cell23_2315274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 1, 2, 1, 2, 3].length) (baseStart_2315274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2315274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2315274 prefixEnd_2315274 := by exact prefixLift 2315274
  have htrace : WordTrace (prefixWord ++ tailWord_2315274) baseStart_2315274 baseEnd_2315274 := by
    simpa [prefixWord, tailWord_2315274, baseEnd_2315274] using wordTrace_append hprefix tailTrace_2315274
  have hstable : (prefixWord ++ tailWord_2315274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2315274).length < 2 ^ (prefixWord ++ tailWord_2315274).sum := by decide
  have hdescent : baseEnd_2315274 < baseStart_2315274 := by decide
  rcases family_descends (prefixWord ++ tailWord_2315274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2315287 : List Nat := [1, 1, 3, 5, 1, 2, 1, 2, 1, 3, 3]
def baseStart_2315287 : Nat := 118140960795 + 2315287 * 2 ^ 59
def prefixEnd_2315287 : Nat := 4983230072969 + 3 ^ 40 * 2315287 * 2
def baseEnd_2315287 : Nat := 1188855084106388162664695

theorem tailTrace_2315287 : CollatzResearch.WordTrace tailWord_2315287 prefixEnd_2315287 1188855084106388162664695 := by
  unfold tailWord_2315287
  simp only [CollatzResearch.WordTrace]
  refine ⟨84445454363118093383752115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56296969575412062255834743 84445454363118093383752115)
  ·
    refine ⟨126668181544677140075628173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84445454363118093383752115 126668181544677140075628173)
    ·
      refine ⟨47500568079253927528360565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 126668181544677140075628173 47500568079253927528360565)
      ·
        refine ⟨4453178257430055705783803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 47500568079253927528360565 4453178257430055705783803)
        ·
          refine ⟨6679767386145083558675705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4453178257430055705783803 6679767386145083558675705)
          ·
            refine ⟨5009825539608812669006779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6679767386145083558675705 5009825539608812669006779)
            ·
              refine ⟨7514738309413219003510169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5009825539608812669006779 7514738309413219003510169)
              ·
                refine ⟨5636053732059914252632627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7514738309413219003510169 5636053732059914252632627)
                ·
                  refine ⟨8454080598089871378948941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5636053732059914252632627 8454080598089871378948941)
                  ·
                    refine ⟨3170280224283701767105853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8454080598089871378948941 3170280224283701767105853)
                    ·
                      refine ⟨1188855084106388162664695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3170280224283701767105853 1188855084106388162664695)
                      ·
                        rfl

theorem cell23_2315287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 1, 2, 1, 3, 3].length) (baseStart_2315287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2315287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2315287 prefixEnd_2315287 := by exact prefixLift 2315287
  have htrace : WordTrace (prefixWord ++ tailWord_2315287) baseStart_2315287 baseEnd_2315287 := by
    simpa [prefixWord, tailWord_2315287, baseEnd_2315287] using wordTrace_append hprefix tailTrace_2315287
  have hstable : (prefixWord ++ tailWord_2315287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2315287).length < 2 ^ (prefixWord ++ tailWord_2315287).sum := by decide
  have hdescent : baseEnd_2315287 < baseStart_2315287 := by decide
  rcases family_descends (prefixWord ++ tailWord_2315287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2315310 : List Nat := [4, 1, 3, 1, 1, 1, 1, 1, 1, 5, 4]
def baseStart_2315310 : Nat := 118140960795 + 2315310 * 2 ^ 59
def prefixEnd_2315310 : Nat := 4983230072969 + 3 ^ 40 * 2315310 * 2
def baseEnd_2315310 : Nat := 1188866894161441572677089

theorem tailTrace_2315310 : CollatzResearch.WordTrace tailWord_2315310 prefixEnd_2315310 1188866894161441572677089 := by
  unfold tailWord_2315310
  simp only [CollatzResearch.WordTrace]
  refine ⟨10555786655254346038979923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56297528828023178874559589 10555786655254346038979923)
  ·
    refine ⟨15833679982881519058469885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10555786655254346038979923 15833679982881519058469885)
    ·
      refine ⟨5937629993580569646926207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15833679982881519058469885 5937629993580569646926207)
      ·
        refine ⟨8906444990370854470389311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5937629993580569646926207 8906444990370854470389311)
        ·
          refine ⟨13359667485556281705583967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8906444990370854470389311 13359667485556281705583967)
          ·
            refine ⟨20039501228334422558375951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13359667485556281705583967 20039501228334422558375951)
            ·
              refine ⟨30059251842501633837563927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20039501228334422558375951 30059251842501633837563927)
              ·
                refine ⟨45088877763752450756345891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30059251842501633837563927 45088877763752450756345891)
                ·
                  refine ⟨67633316645628676134518837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45088877763752450756345891 67633316645628676134518837)
                  ·
                    refine ⟨6340623435527688387611141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 67633316645628676134518837 6340623435527688387611141)
                    ·
                      refine ⟨1188866894161441572677089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6340623435527688387611141 1188866894161441572677089)
                      ·
                        rfl

theorem cell23_2315310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 1, 1, 5, 4].length) (baseStart_2315310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2315310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2315310 prefixEnd_2315310 := by exact prefixLift 2315310
  have htrace : WordTrace (prefixWord ++ tailWord_2315310) baseStart_2315310 baseEnd_2315310 := by
    simpa [prefixWord, tailWord_2315310, baseEnd_2315310] using wordTrace_append hprefix tailTrace_2315310
  have hstable : (prefixWord ++ tailWord_2315310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2315310).length < 2 ^ (prefixWord ++ tailWord_2315310).sum := by decide
  have hdescent : baseEnd_2315310 < baseStart_2315310 := by decide
  rcases family_descends (prefixWord ++ tailWord_2315310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2315320 : List Nat := [2, 1, 2, 1, 5, 2, 1, 1, 2, 6]
def baseStart_2315320 : Nat := 118140960795 + 2315320 * 2 ^ 59
def prefixEnd_2315320 : Nat := 4983230072969 + 3 ^ 40 * 2315320 * 2
def baseEnd_2315320 : Nat := 396290676322662177850681

theorem tailTrace_2315320 : CollatzResearch.WordTrace tailWord_2315320 prefixEnd_2315320 396290676322662177850681 := by
  unfold tailWord_2315320
  simp only [CollatzResearch.WordTrace]
  refine ⟨42223328985999270009851707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56297771981332360013135609 42223328985999270009851707)
  ·
    refine ⟨63334993478998905014777561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42223328985999270009851707 63334993478998905014777561)
    ·
      refine ⟨47501245109249178761083171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63334993478998905014777561 47501245109249178761083171)
      ·
        refine ⟨71251867663873768141624757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47501245109249178761083171 71251867663873768141624757)
        ·
          refine ⟨6679862593488165763277321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 71251867663873768141624757 6679862593488165763277321)
          ·
            refine ⟨5009896945116124322457991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6679862593488165763277321 5009896945116124322457991)
            ·
              refine ⟨7514845417674186483686987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5009896945116124322457991 7514845417674186483686987)
              ·
                refine ⟨11272268126511279725530481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7514845417674186483686987 11272268126511279725530481)
                ·
                  refine ⟨8454201094883459794147861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11272268126511279725530481 8454201094883459794147861)
                  ·
                    refine ⟨396290676322662177850681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8454201094883459794147861 396290676322662177850681)
                    ·
                      rfl

theorem cell23_2315320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 1, 1, 2, 6].length) (baseStart_2315320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2315320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2315320 prefixEnd_2315320 := by exact prefixLift 2315320
  have htrace : WordTrace (prefixWord ++ tailWord_2315320) baseStart_2315320 baseEnd_2315320 := by
    simpa [prefixWord, tailWord_2315320, baseEnd_2315320] using wordTrace_append hprefix tailTrace_2315320
  have hstable : (prefixWord ++ tailWord_2315320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2315320).length < 2 ^ (prefixWord ++ tailWord_2315320).sum := by decide
  have hdescent : baseEnd_2315320 < baseStart_2315320 := by decide
  rcases family_descends (prefixWord ++ tailWord_2315320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2315327 : List Nat := [1, 1, 2, 2, 3, 1, 1, 2, 6, 2, 2]
def baseStart_2315327 : Nat := 118140960795 + 2315327 * 2 ^ 59
def prefixEnd_2315327 : Nat := 4983230072969 + 3 ^ 40 * 2315327 * 2
def baseEnd_2315327 : Nat := 1188875623332568006164511

theorem tailTrace_2315327 : CollatzResearch.WordTrace tailWord_2315327 prefixEnd_2315327 1188875623332568006164511 := by
  unfold tailWord_2315327
  simp only [CollatzResearch.WordTrace]
  refine ⟨84446913282973180215208235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56297942188648786810138823 84446913282973180215208235)
  ·
    refine ⟨126670369924459770322812353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84446913282973180215208235 126670369924459770322812353)
    ·
      refine ⟨95002777443344827742109265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126670369924459770322812353 95002777443344827742109265)
      ·
        refine ⟨71252083082508620806581949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95002777443344827742109265 71252083082508620806581949)
        ·
          refine ⟨26719531155940732802468231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71252083082508620806581949 26719531155940732802468231)
          ·
            refine ⟨40079296733911099203702347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26719531155940732802468231 40079296733911099203702347)
            ·
              refine ⟨60118945100866648805553521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40079296733911099203702347 60118945100866648805553521)
              ·
                refine ⟨45089208825649986604165141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60118945100866648805553521 45089208825649986604165141)
                ·
                  refine ⟨2113556663702343122070241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 45089208825649986604165141 2113556663702343122070241)
                  ·
                    refine ⟨1585167497776757341552681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2113556663702343122070241 1585167497776757341552681)
                    ·
                      refine ⟨1188875623332568006164511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1585167497776757341552681 1188875623332568006164511)
                      ·
                        rfl

theorem cell23_2315327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 2, 6, 2, 2].length) (baseStart_2315327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2315327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2315327 prefixEnd_2315327 := by exact prefixLift 2315327
  have htrace : WordTrace (prefixWord ++ tailWord_2315327) baseStart_2315327 baseEnd_2315327 := by
    simpa [prefixWord, tailWord_2315327, baseEnd_2315327] using wordTrace_append hprefix tailTrace_2315327
  have hstable : (prefixWord ++ tailWord_2315327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2315327).length < 2 ^ (prefixWord ++ tailWord_2315327).sum := by decide
  have hdescent : baseEnd_2315327 < baseStart_2315327 := by decide
  rcases family_descends (prefixWord ++ tailWord_2315327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2315333 : List Nat := [1, 3, 1, 1, 1, 3, 3, 1, 9]
def baseStart_2315333 : Nat := 118140960795 + 2315333 * 2 ^ 59
def prefixEnd_2315333 : Nat := 4983230072969 + 3 ^ 40 * 2315333 * 2
def baseEnd_2315333 : Nat := 132097633801832775854387

theorem tailTrace_2315333 : CollatzResearch.WordTrace tailWord_2315333 prefixEnd_2315333 132097633801832775854387 := by
  unfold tailWord_2315333
  simp only [CollatzResearch.WordTrace]
  refine ⟨84447132120951443239926653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56298088080634295493284435 84447132120951443239926653)
  ·
    refine ⟨31667674545356791214972495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84447132120951443239926653 31667674545356791214972495)
    ·
      refine ⟨47501511818035186822458743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31667674545356791214972495 47501511818035186822458743)
      ·
        refine ⟨71252267727052780233688115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47501511818035186822458743 71252267727052780233688115)
        ·
          refine ⟨106878401590579170350532173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71252267727052780233688115 106878401590579170350532173)
          ·
            refine ⟨40079400596467188881449565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 106878401590579170350532173 40079400596467188881449565)
            ·
              refine ⟨15029775223675195830543587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40079400596467188881449565 15029775223675195830543587)
              ·
                refine ⟨22544662835512793745815381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15029775223675195830543587 22544662835512793745815381)
                ·
                  refine ⟨132097633801832775854387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 22544662835512793745815381 132097633801832775854387)
                  ·
                    rfl

theorem cell23_2315333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 1, 9].length) (baseStart_2315333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2315333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2315333 prefixEnd_2315333 := by exact prefixLift 2315333
  have htrace : WordTrace (prefixWord ++ tailWord_2315333) baseStart_2315333 baseEnd_2315333 := by
    simpa [prefixWord, tailWord_2315333, baseEnd_2315333] using wordTrace_append hprefix tailTrace_2315333
  have hstable : (prefixWord ++ tailWord_2315333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2315333).length < 2 ^ (prefixWord ++ tailWord_2315333).sum := by decide
  have hdescent : baseEnd_2315333 < baseStart_2315333 := by decide
  rcases family_descends (prefixWord ++ tailWord_2315333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2315360 : List Nat := [2, 1, 1, 3, 2, 2, 1, 1, 4, 3, 3]
def baseStart_2315360 : Nat := 118140960795 + 2315360 * 2 ^ 59
def prefixEnd_2315360 : Nat := 4983230072969 + 3 ^ 40 * 2315360 * 2
def baseEnd_2315360 : Nat := 1188892568194166377051859

theorem tailTrace_2315360 : CollatzResearch.WordTrace tailWord_2315360 prefixEnd_2315360 1188892568194166377051859 := by
  unfold tailWord_2315360
  simp only [CollatzResearch.WordTrace]
  refine ⟨42224058445926813425579767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56298744594569084567439689 42224058445926813425579767)
  ·
    refine ⟨63336087668890220138369651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42224058445926813425579767 63336087668890220138369651)
    ·
      refine ⟨95004131503335330207554477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63336087668890220138369651 95004131503335330207554477)
      ·
        refine ⟨35626549313750748827832929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95004131503335330207554477 35626549313750748827832929)
        ·
          refine ⟨26719911985313061620874697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35626549313750748827832929 26719911985313061620874697)
          ·
            refine ⟨20039933988984796215656023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26719911985313061620874697 20039933988984796215656023)
            ·
              refine ⟨30059900983477194323484035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20039933988984796215656023 30059900983477194323484035)
              ·
                refine ⟨45089851475215791485226053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30059900983477194323484035 45089851475215791485226053)
                ·
                  refine ⟨8454347151602960903479885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45089851475215791485226053 8454347151602960903479885)
                  ·
                    refine ⟨3170380181851110338804957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8454347151602960903479885 3170380181851110338804957)
                    ·
                      refine ⟨1188892568194166377051859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3170380181851110338804957 1188892568194166377051859)
                      ·
                        rfl

theorem cell23_2315360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 1, 4, 3, 3].length) (baseStart_2315360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2315360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2315360 prefixEnd_2315360 := by exact prefixLift 2315360
  have htrace : WordTrace (prefixWord ++ tailWord_2315360) baseStart_2315360 baseEnd_2315360 := by
    simpa [prefixWord, tailWord_2315360, baseEnd_2315360] using wordTrace_append hprefix tailTrace_2315360
  have hstable : (prefixWord ++ tailWord_2315360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2315360).length < 2 ^ (prefixWord ++ tailWord_2315360).sum := by decide
  have hdescent : baseEnd_2315360 < baseStart_2315360 := by decide
  rcases family_descends (prefixWord ++ tailWord_2315360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2315367 : List Nat := [1, 1, 5, 1, 1, 3, 2, 4, 5]
def baseStart_2315367 : Nat := 118140960795 + 2315367 * 2 ^ 59
def prefixEnd_2315367 : Nat := 4983230072969 + 3 ^ 40 * 2315367 * 2
def baseEnd_2315367 : Nat := 132099573617638649962703

theorem tailTrace_2315367 : CollatzResearch.WordTrace tailWord_2315367 prefixEnd_2315367 132099573617638649962703 := by
  unfold tailWord_2315367
  simp only [CollatzResearch.WordTrace]
  refine ⟨84448372202828267046664355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56298914801885511364442903 84448372202828267046664355)
  ·
    refine ⟨126672558304242400569996533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84448372202828267046664355 126672558304242400569996533)
    ·
      refine ⟨11875552341022725053437175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 126672558304242400569996533 11875552341022725053437175)
      ·
        refine ⟨17813328511534087580155763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11875552341022725053437175 17813328511534087580155763)
        ·
          refine ⟨26719992767301131370233645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17813328511534087580155763 26719992767301131370233645)
          ·
            refine ⟨10019997287737924263837617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26719992767301131370233645 10019997287737924263837617)
            ·
              refine ⟨7514997965803443197878213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10019997287737924263837617 7514997965803443197878213)
              ·
                refine ⟨1409062118588145599602165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7514997965803443197878213 1409062118588145599602165)
                ·
                  refine ⟨132099573617638649962703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1409062118588145599602165 132099573617638649962703)
                  ·
                    rfl

theorem cell23_2315367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 2, 4, 5].length) (baseStart_2315367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2315367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2315367 prefixEnd_2315367 := by exact prefixLift 2315367
  have htrace : WordTrace (prefixWord ++ tailWord_2315367) baseStart_2315367 baseEnd_2315367 := by
    simpa [prefixWord, tailWord_2315367, baseEnd_2315367] using wordTrace_append hprefix tailTrace_2315367
  have hstable : (prefixWord ++ tailWord_2315367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2315367).length < 2 ^ (prefixWord ++ tailWord_2315367).sum := by decide
  have hdescent : baseEnd_2315367 < baseStart_2315367 := by decide
  rcases family_descends (prefixWord ++ tailWord_2315367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2315440 : List Nat := [2, 1, 1, 1, 2, 1, 2, 7, 6]
def baseStart_2315440 : Nat := 118140960795 + 2315440 * 2 ^ 59
def prefixEnd_2315440 : Nat := 4983230072969 + 3 ^ 40 * 2315440 * 2
def baseEnd_2315440 : Nat := 132103738516280673783499

theorem tailTrace_2315440 : CollatzResearch.WordTrace tailWord_2315440 prefixEnd_2315440 132103738516280673783499 := by
  unfold tailWord_2315440
  simp only [CollatzResearch.WordTrace]
  refine ⟨42225517365781900257035887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56300689821042533676047849 42225517365781900257035887)
  ·
    refine ⟨63338276048672850385553831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42225517365781900257035887 63338276048672850385553831)
    ·
      refine ⟨95007414073009275578330747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63338276048672850385553831 95007414073009275578330747)
      ·
        refine ⟨142511121109513913367496121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95007414073009275578330747 142511121109513913367496121)
        ·
          refine ⟨106883340832135435025622091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 142511121109513913367496121 106883340832135435025622091)
          ·
            refine ⟨160325011248203152538433137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106883340832135435025622091 160325011248203152538433137)
            ·
              refine ⟨120243758436152364403824853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 160325011248203152538433137 120243758436152364403824853)
              ·
                refine ⟨2818213088347321040714645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 120243758436152364403824853 2818213088347321040714645)
                ·
                  refine ⟨132103738516280673783499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2818213088347321040714645 132103738516280673783499)
                  ·
                    rfl

theorem cell23_2315440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 7, 6].length) (baseStart_2315440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2315440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2315440 prefixEnd_2315440 := by exact prefixLift 2315440
  have htrace : WordTrace (prefixWord ++ tailWord_2315440) baseStart_2315440 baseEnd_2315440 := by
    simpa [prefixWord, tailWord_2315440, baseEnd_2315440] using wordTrace_append hprefix tailTrace_2315440
  have hstable : (prefixWord ++ tailWord_2315440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2315440).length < 2 ^ (prefixWord ++ tailWord_2315440).sum := by decide
  have hdescent : baseEnd_2315440 < baseStart_2315440 := by decide
  rcases family_descends (prefixWord ++ tailWord_2315440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2315454 : List Nat := [4, 2, 1, 1, 3, 1, 1, 3, 2, 2, 3]
def baseStart_2315454 : Nat := 118140960795 + 2315454 * 2 ^ 59
def prefixEnd_2315454 : Nat := 4983230072969 + 3 ^ 40 * 2315454 * 2
def baseEnd_2315454 : Nat := 1188940835375689009276427

theorem tailTrace_2315454 : CollatzResearch.WordTrace tailWord_2315454 prefixEnd_2315454 1188940835375689009276427 := by
  unfold tailWord_2315454
  simp only [CollatzResearch.WordTrace]
  refine ⟨10556443169189135113135177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56301030235675387270054277 10556443169189135113135177)
  ·
    refine ⟨7917332376891851334851383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10556443169189135113135177 7917332376891851334851383)
    ·
      refine ⟨11875998565337777002277075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7917332376891851334851383 11875998565337777002277075)
      ·
        refine ⟨17813997848006665503415613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11875998565337777002277075 17813997848006665503415613)
        ·
          refine ⟨6680249193002499563780855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17813997848006665503415613 6680249193002499563780855)
          ·
            refine ⟨10020373789503749345671283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6680249193002499563780855 10020373789503749345671283)
            ·
              refine ⟨15030560684255624018506925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10020373789503749345671283 15030560684255624018506925)
              ·
                refine ⟨5636460256595859006940097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15030560684255624018506925 5636460256595859006940097)
                ·
                  refine ⟨4227345192446894255205073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5636460256595859006940097 4227345192446894255205073)
                  ·
                    refine ⟨3170508894335170691403805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4227345192446894255205073 3170508894335170691403805)
                    ·
                      refine ⟨1188940835375689009276427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3170508894335170691403805 1188940835375689009276427)
                      ·
                        rfl

theorem cell23_2315454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 3, 2, 2, 3].length) (baseStart_2315454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2315454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2315454 prefixEnd_2315454 := by exact prefixLift 2315454
  have htrace : WordTrace (prefixWord ++ tailWord_2315454) baseStart_2315454 baseEnd_2315454 := by
    simpa [prefixWord, tailWord_2315454, baseEnd_2315454] using wordTrace_append hprefix tailTrace_2315454
  have hstable : (prefixWord ++ tailWord_2315454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2315454).length < 2 ^ (prefixWord ++ tailWord_2315454).sum := by decide
  have hdescent : baseEnd_2315454 < baseStart_2315454 := by decide
  rcases family_descends (prefixWord ++ tailWord_2315454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2315467 : List Nat := [1, 1, 1, 1, 3, 2, 2, 1, 7, 1, 3]
def baseStart_2315467 : Nat := 118140960795 + 2315467 * 2 ^ 59
def prefixEnd_2315467 : Nat := 4983230072969 + 3 ^ 40 * 2315467 * 2
def baseEnd_2315467 : Nat := 1188947510624197458413867

theorem tailTrace_2315467 : CollatzResearch.WordTrace tailWord_2315467 prefixEnd_2315467 1188947510624197458413867 := by
  unfold tailWord_2315467
  simp only [CollatzResearch.WordTrace]
  refine ⟨84452019502465984125304655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56301346334977322750203103 84452019502465984125304655)
  ·
    refine ⟨126678029253698976187956983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84452019502465984125304655 126678029253698976187956983)
    ·
      refine ⟨190017043880548464281935475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126678029253698976187956983 190017043880548464281935475)
      ·
        refine ⟨285025565820822696422903213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190017043880548464281935475 285025565820822696422903213)
        ·
          refine ⟨106884587182808511158588705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 285025565820822696422903213 106884587182808511158588705)
          ·
            refine ⟨80163440387106383368941529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 106884587182808511158588705 80163440387106383368941529)
            ·
              refine ⟨60122580290329787526706147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80163440387106383368941529 60122580290329787526706147)
              ·
                refine ⟨90183870435494681290059221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60122580290329787526706147 90183870435494681290059221)
                ·
                  refine ⟨2113684463331906592735763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 90183870435494681290059221 2113684463331906592735763)
                  ·
                    refine ⟨3170526694997859889103645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2113684463331906592735763 3170526694997859889103645)
                    ·
                      refine ⟨1188947510624197458413867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3170526694997859889103645 1188947510624197458413867)
                      ·
                        rfl

theorem cell23_2315467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 1, 7, 1, 3].length) (baseStart_2315467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2315467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2315467 prefixEnd_2315467 := by exact prefixLift 2315467
  have htrace : WordTrace (prefixWord ++ tailWord_2315467) baseStart_2315467 baseEnd_2315467 := by
    simpa [prefixWord, tailWord_2315467, baseEnd_2315467] using wordTrace_append hprefix tailTrace_2315467
  have hstable : (prefixWord ++ tailWord_2315467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2315467).length < 2 ^ (prefixWord ++ tailWord_2315467).sum := by decide
  have hdescent : baseEnd_2315467 < baseStart_2315467 := by decide
  rcases family_descends (prefixWord ++ tailWord_2315467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2315501 : List Nat := [1, 5, 1, 2, 2, 2, 1, 2, 3, 1, 3]
def baseStart_2315501 : Nat := 118140960795 + 2315501 * 2 ^ 59
def prefixEnd_2315501 : Nat := 4983230072969 + 3 ^ 40 * 2315501 * 2
def baseEnd_2315501 : Nat := 1188964968966450325388711

theorem tailTrace_2315501 : CollatzResearch.WordTrace tailWord_2315501 prefixEnd_2315501 1188964968966450325388711 := by
  unfold tailWord_2315501
  simp only [CollatzResearch.WordTrace]
  refine ⟨84453259584342807932042357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56302173056228538621361571 84453259584342807932042357)
  ·
    refine ⟨7917493086032138243628971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 84453259584342807932042357 7917493086032138243628971)
    ·
      refine ⟨11876239629048207365443457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7917493086032138243628971 11876239629048207365443457)
      ·
        refine ⟨8907179721786155524082593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11876239629048207365443457 8907179721786155524082593)
        ·
          refine ⟨6680384791339616643061945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8907179721786155524082593 6680384791339616643061945)
          ·
            refine ⟨5010288593504712482296459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6680384791339616643061945 5010288593504712482296459)
            ·
              refine ⟨7515432890257068723444689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5010288593504712482296459 7515432890257068723444689)
              ·
                refine ⟨5636574667692801542583517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7515432890257068723444689 5636574667692801542583517)
                ·
                  refine ⟨2113715500384800578468819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5636574667692801542583517 2113715500384800578468819)
                  ·
                    refine ⟨3170573250577200867703229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2113715500384800578468819 3170573250577200867703229)
                    ·
                      refine ⟨1188964968966450325388711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3170573250577200867703229 1188964968966450325388711)
                      ·
                        rfl

theorem cell23_2315501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 1, 2, 3, 1, 3].length) (baseStart_2315501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2315501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2315501 prefixEnd_2315501 := by exact prefixLift 2315501
  have htrace : WordTrace (prefixWord ++ tailWord_2315501) baseStart_2315501 baseEnd_2315501 := by
    simpa [prefixWord, tailWord_2315501, baseEnd_2315501] using wordTrace_append hprefix tailTrace_2315501
  have hstable : (prefixWord ++ tailWord_2315501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2315501).length < 2 ^ (prefixWord ++ tailWord_2315501).sum := by decide
  have hdescent : baseEnd_2315501 < baseStart_2315501 := by decide
  rcases family_descends (prefixWord ++ tailWord_2315501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2315507 : List Nat := [1, 1, 1, 2, 2, 5, 2, 1, 3, 1, 4]
def baseStart_2315507 : Nat := 118140960795 + 2315507 * 2 ^ 59
def prefixEnd_2315507 : Nat := 4983230072969 + 3 ^ 40 * 2315507 * 2
def baseEnd_2315507 : Nat := 1188968049850377301913683

theorem tailTrace_2315507 : CollatzResearch.WordTrace tailWord_2315507 prefixEnd_2315507 1188968049850377301913683 := by
  unfold tailWord_2315507
  simp only [CollatzResearch.WordTrace]
  refine ⟨84453478422321070956760775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56302318948214047304507183 84453478422321070956760775)
  ·
    refine ⟨126680217633481606435141163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84453478422321070956760775 126680217633481606435141163)
    ·
      refine ⟨190020326450222409652711745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126680217633481606435141163 190020326450222409652711745)
      ·
        refine ⟨142515244837666807239533809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 190020326450222409652711745 142515244837666807239533809)
        ·
          refine ⟨106886433628250105429650357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 142515244837666807239533809 106886433628250105429650357)
          ·
            refine ⟨10020603152648447384029721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 106886433628250105429650357 10020603152648447384029721)
            ·
              refine ⟨7515452364486335538022291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10020603152648447384029721 7515452364486335538022291)
              ·
                refine ⟨11273178546729503307033437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7515452364486335538022291 11273178546729503307033437)
                ·
                  refine ⟨4227441955023563740137539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11273178546729503307033437 4227441955023563740137539)
                  ·
                    refine ⟨6341162932535345610206309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4227441955023563740137539 6341162932535345610206309)
                    ·
                      refine ⟨1188968049850377301913683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6341162932535345610206309 1188968049850377301913683)
                      ·
                        rfl

theorem cell23_2315507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 2, 1, 3, 1, 4].length) (baseStart_2315507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2315507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2315507 prefixEnd_2315507 := by exact prefixLift 2315507
  have htrace : WordTrace (prefixWord ++ tailWord_2315507) baseStart_2315507 baseEnd_2315507 := by
    simpa [prefixWord, tailWord_2315507, baseEnd_2315507] using wordTrace_append hprefix tailTrace_2315507
  have hstable : (prefixWord ++ tailWord_2315507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2315507).length < 2 ^ (prefixWord ++ tailWord_2315507).sum := by decide
  have hdescent : baseEnd_2315507 < baseStart_2315507 := by decide
  rcases family_descends (prefixWord ++ tailWord_2315507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2315518 : List Nat := [4, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3]
def baseStart_2315518 : Nat := 118140960795 + 2315518 * 2 ^ 59
def prefixEnd_2315518 : Nat := 4983230072969 + 3 ^ 40 * 2315518 * 2
def baseEnd_2315518 : Nat := 1188973698137576758876133

theorem tailTrace_2315518 : CollatzResearch.WordTrace tailWord_2315518 prefixEnd_2315518 1188973698137576758876133 := by
  unfold tailWord_2315518
  simp only [CollatzResearch.WordTrace]
  refine ⟨10556734953160152479426401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56302586416854146556940805 10556734953160152479426401)
  ·
    refine ⟨7917551214870114359569801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10556734953160152479426401 7917551214870114359569801)
    ·
      refine ⟨5938163411152585769677351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7917551214870114359569801 5938163411152585769677351)
      ·
        refine ⟨8907245116728878654516027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5938163411152585769677351 8907245116728878654516027)
        ·
          refine ⟨13360867675093317981774041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8907245116728878654516027 13360867675093317981774041)
          ·
            refine ⟨10020650756319988486330531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13360867675093317981774041 10020650756319988486330531)
            ·
              refine ⟨15030976134479982729495797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10020650756319988486330531 15030976134479982729495797)
              ·
                refine ⟨1409154012607498380890231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15030976134479982729495797 1409154012607498380890231)
                ·
                  refine ⟨2113731018911247571335347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1409154012607498380890231 2113731018911247571335347)
                  ·
                    refine ⟨3170596528366871357003021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2113731018911247571335347 3170596528366871357003021)
                    ·
                      refine ⟨1188973698137576758876133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3170596528366871357003021 1188973698137576758876133)
                      ·
                        rfl

theorem cell23_2315518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3].length) (baseStart_2315518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2315518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2315518 prefixEnd_2315518 := by exact prefixLift 2315518
  have htrace : WordTrace (prefixWord ++ tailWord_2315518) baseStart_2315518 baseEnd_2315518 := by
    simpa [prefixWord, tailWord_2315518, baseEnd_2315518] using wordTrace_append hprefix tailTrace_2315518
  have hstable : (prefixWord ++ tailWord_2315518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2315518).length < 2 ^ (prefixWord ++ tailWord_2315518).sum := by decide
  have hdescent : baseEnd_2315518 < baseStart_2315518 := by decide
  rcases family_descends (prefixWord ++ tailWord_2315518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2315520 : List Nat := [2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 6]
def baseStart_2315520 : Nat := 118140960795 + 2315520 * 2 ^ 59
def prefixEnd_2315520 : Nat := 4983230072969 + 3 ^ 40 * 2315520 * 2
def baseEnd_2315520 : Nat := 1188974725098885751051123

theorem tailTrace_2315520 : CollatzResearch.WordTrace tailWord_2315520 prefixEnd_2315520 1188974725098885751051123 := by
  unfold tailWord_2315520
  simp only [CollatzResearch.WordTrace]
  refine ⟨42226976285636987088492007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56302635047515982784656009 42226976285636987088492007)
  ·
    refine ⟨63340464428455480632738011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42226976285636987088492007 63340464428455480632738011)
    ·
      refine ⟨95010696642683220949107017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63340464428455480632738011 95010696642683220949107017)
      ·
        refine ⟨71258022482012415711830263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95010696642683220949107017 71258022482012415711830263)
        ·
          refine ⟨106887033723018623567745395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71258022482012415711830263 106887033723018623567745395)
          ·
            refine ⟨160330550584527935351618093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106887033723018623567745395 160330550584527935351618093)
            ·
              refine ⟨60123956469197975756856785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 160330550584527935351618093 60123956469197975756856785)
              ·
                refine ⟨45092967351898481817642589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60123956469197975756856785 45092967351898481817642589)
                ·
                  refine ⟨16909862756961930681615971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45092967351898481817642589 16909862756961930681615971)
                  ·
                    refine ⟨25364794135442896022423957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16909862756961930681615971 25364794135442896022423957)
                    ·
                      refine ⟨1188974725098885751051123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 25364794135442896022423957 1188974725098885751051123)
                      ·
                        rfl

theorem cell23_2315520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 6].length) (baseStart_2315520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2315520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2315520 prefixEnd_2315520 := by exact prefixLift 2315520
  have htrace : WordTrace (prefixWord ++ tailWord_2315520) baseStart_2315520 baseEnd_2315520 := by
    simpa [prefixWord, tailWord_2315520, baseEnd_2315520] using wordTrace_append hprefix tailTrace_2315520
  have hstable : (prefixWord ++ tailWord_2315520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2315520).length < 2 ^ (prefixWord ++ tailWord_2315520).sum := by decide
  have hdescent : baseEnd_2315520 < baseStart_2315520 := by decide
  rcases family_descends (prefixWord ++ tailWord_2315520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2315521 : List Nat := [1, 2, 4, 1, 1, 5, 2, 1, 1, 5]
def baseStart_2315521 : Nat := 118140960795 + 2315521 * 2 ^ 59
def prefixEnd_2315521 : Nat := 4983230072969 + 3 ^ 40 * 2315521 * 2
def baseEnd_2315521 : Nat := 396325079526513415712873

theorem tailTrace_2315521 : CollatzResearch.WordTrace tailWord_2315521 prefixEnd_2315521 396325079526513415712873 := by
  unfold tailWord_2315521
  simp only [CollatzResearch.WordTrace]
  refine ⟨84453989044270351347770417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56302659362846900898513611 84453989044270351347770417)
  ·
    refine ⟨63340491783202763510827813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84453989044270351347770417 63340491783202763510827813)
    ·
      refine ⟨11876342209350518158280215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 63340491783202763510827813 11876342209350518158280215)
      ·
        refine ⟨17814513314025777237420323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11876342209350518158280215 17814513314025777237420323)
        ·
          refine ⟨26721769971038665856130485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17814513314025777237420323 26721769971038665856130485)
          ·
            refine ⟨2505165934784874924012233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 26721769971038665856130485 2505165934784874924012233)
            ·
              refine ⟨1878874451088656193009175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2505165934784874924012233 1878874451088656193009175)
              ·
                refine ⟨2818311676632984289513763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1878874451088656193009175 2818311676632984289513763)
                ·
                  refine ⟨4227467514949476434270645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2818311676632984289513763 4227467514949476434270645)
                  ·
                    refine ⟨396325079526513415712873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4227467514949476434270645 396325079526513415712873)
                    ·
                      rfl

theorem cell23_2315521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 2, 1, 1, 5].length) (baseStart_2315521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2315521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2315521 prefixEnd_2315521 := by exact prefixLift 2315521
  have htrace : WordTrace (prefixWord ++ tailWord_2315521) baseStart_2315521 baseEnd_2315521 := by
    simpa [prefixWord, tailWord_2315521, baseEnd_2315521] using wordTrace_append hprefix tailTrace_2315521
  have hstable : (prefixWord ++ tailWord_2315521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2315521).length < 2 ^ (prefixWord ++ tailWord_2315521).sum := by decide
  have hdescent : baseEnd_2315521 < baseStart_2315521 := by decide
  rcases family_descends (prefixWord ++ tailWord_2315521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2315534 : List Nat := [4, 1, 1, 2, 1, 4, 1, 1, 4, 4]
def baseStart_2315534 : Nat := 118140960795 + 2315534 * 2 ^ 59
def prefixEnd_2315534 : Nat := 4983230072969 + 3 ^ 40 * 2315534 * 2
def baseEnd_2315534 : Nat := 396327304609349565425353

theorem tailTrace_2315534 : CollatzResearch.WordTrace tailWord_2315534 prefixEnd_2315534 396327304609349565425353 := by
  unfold tailWord_2315534
  simp only [CollatzResearch.WordTrace]
  refine ⟨10556807899152906820999207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56302975462148836378662437 10556807899152906820999207)
  ·
    refine ⟨15835211848729360231498811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10556807899152906820999207 15835211848729360231498811)
    ·
      refine ⟨23752817773094040347248217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15835211848729360231498811 23752817773094040347248217)
      ·
        refine ⟨17814613329820530260436163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23752817773094040347248217 17814613329820530260436163)
        ·
          refine ⟨26721919994730795390654245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17814613329820530260436163 26721919994730795390654245)
          ·
            refine ⟨5010359999012024135747671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26721919994730795390654245 5010359999012024135747671)
            ·
              refine ⟨7515539998518036203621507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5010359999012024135747671 7515539998518036203621507)
              ·
                refine ⟨11273309997777054305432261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7515539998518036203621507 11273309997777054305432261)
                ·
                  refine ⟨2113745624583197682268549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11273309997777054305432261 2113745624583197682268549)
                  ·
                    refine ⟨396327304609349565425353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2113745624583197682268549 396327304609349565425353)
                    ·
                      rfl

theorem cell23_2315534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 1, 1, 4, 4].length) (baseStart_2315534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2315534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2315534 prefixEnd_2315534 := by exact prefixLift 2315534
  have htrace : WordTrace (prefixWord ++ tailWord_2315534) baseStart_2315534 baseEnd_2315534 := by
    simpa [prefixWord, tailWord_2315534, baseEnd_2315534] using wordTrace_append hprefix tailTrace_2315534
  have hstable : (prefixWord ++ tailWord_2315534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2315534).length < 2 ^ (prefixWord ++ tailWord_2315534).sum := by decide
  have hdescent : baseEnd_2315534 < baseStart_2315534 := by decide
  rcases family_descends (prefixWord ++ tailWord_2315534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2315551 : List Nat := [1, 1, 2, 4, 5, 1, 1, 1, 1, 6]
def baseStart_2315551 : Nat := 118140960795 + 2315551 * 2 ^ 59
def prefixEnd_2315551 : Nat := 4983230072969 + 3 ^ 40 * 2315551 * 2
def baseEnd_2315551 : Nat := 396330214333058376587827

theorem tailTrace_2315551 : CollatzResearch.WordTrace tailWord_2315551 prefixEnd_2315551 396330214333058376587827 := by
  unfold tailWord_2315551
  simp only [CollatzResearch.WordTrace]
  refine ⟨84455083234161666471362507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56303388822774444314241671 84455083234161666471362507)
  ·
    refine ⟨126682624851242499707043761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84455083234161666471362507 126682624851242499707043761)
    ·
      refine ⟨95011968638431874780282821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126682624851242499707043761 95011968638431874780282821)
      ·
        refine ⟨17814744119705976521303029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 95011968638431874780282821 17814744119705976521303029)
        ·
          refine ⟨1670132261222435298872159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 17814744119705976521303029 1670132261222435298872159)
          ·
            refine ⟨2505198391833652948308239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1670132261222435298872159 2505198391833652948308239)
            ·
              refine ⟨3757797587750479422462359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2505198391833652948308239 3757797587750479422462359)
              ·
                refine ⟨5636696381625719133693539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3757797587750479422462359 5636696381625719133693539)
                ·
                  refine ⟨8455044572438578700540309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5636696381625719133693539 8455044572438578700540309)
                  ·
                    refine ⟨396330214333058376587827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8455044572438578700540309 396330214333058376587827)
                    ·
                      rfl

theorem cell23_2315551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 1, 1, 1, 6].length) (baseStart_2315551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2315551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2315551 prefixEnd_2315551 := by exact prefixLift 2315551
  have htrace : WordTrace (prefixWord ++ tailWord_2315551) baseStart_2315551 baseEnd_2315551 := by
    simpa [prefixWord, tailWord_2315551, baseEnd_2315551] using wordTrace_append hprefix tailTrace_2315551
  have hstable : (prefixWord ++ tailWord_2315551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2315551).length < 2 ^ (prefixWord ++ tailWord_2315551).sum := by decide
  have hdescent : baseEnd_2315551 < baseStart_2315551 := by decide
  rcases family_descends (prefixWord ++ tailWord_2315551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2315554 : List Nat := [3, 3, 1, 1, 4, 1, 1, 1, 1, 1, 6]
def baseStart_2315554 : Nat := 118140960795 + 2315554 * 2 ^ 59
def prefixEnd_2315554 : Nat := 4983230072969 + 3 ^ 40 * 2315554 * 2
def baseEnd_2315554 : Nat := 1188992183441138618025967

theorem tailTrace_2315554 : CollatzResearch.WordTrace tailWord_2315554 prefixEnd_2315554 1188992183441138618025967 := by
  unfold tailWord_2315554
  simp only [CollatzResearch.WordTrace]
  refine ⟨21113798163287699495930429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56303461768767198655814477 21113798163287699495930429)
  ·
    refine ⟨7917674311232887310973911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21113798163287699495930429 7917674311232887310973911)
    ·
      refine ⟨11876511466849330966460867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7917674311232887310973911 11876511466849330966460867)
      ·
        refine ⟨17814767200273996449691301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11876511466849330966460867 17814767200273996449691301)
        ·
          refine ⟨3340268850051374334317119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17814767200273996449691301 3340268850051374334317119)
          ·
            refine ⟨5010403275077061501475679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3340268850051374334317119 5010403275077061501475679)
            ·
              refine ⟨7515604912615592252213519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5010403275077061501475679 7515604912615592252213519)
              ·
                refine ⟨11273407368923388378320279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7515604912615592252213519 11273407368923388378320279)
                ·
                  refine ⟨16910111053385082567480419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11273407368923388378320279 16910111053385082567480419)
                  ·
                    refine ⟨25365166580077623851220629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16910111053385082567480419 25365166580077623851220629)
                    ·
                      refine ⟨1188992183441138618025967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 25365166580077623851220629 1188992183441138618025967)
                      ·
                        rfl

theorem cell23_2315554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 1, 1, 1, 1, 6].length) (baseStart_2315554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2315554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2315554 prefixEnd_2315554 := by exact prefixLift 2315554
  have htrace : WordTrace (prefixWord ++ tailWord_2315554) baseStart_2315554 baseEnd_2315554 := by
    simpa [prefixWord, tailWord_2315554, baseEnd_2315554] using wordTrace_append hprefix tailTrace_2315554
  have hstable : (prefixWord ++ tailWord_2315554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2315554).length < 2 ^ (prefixWord ++ tailWord_2315554).sum := by decide
  have hdescent : baseEnd_2315554 < baseStart_2315554 := by decide
  rcases family_descends (prefixWord ++ tailWord_2315554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2315581 : List Nat := [1, 4, 1, 5, 2, 1, 9]
def baseStart_2315581 : Nat := 118140960795 + 2315581 * 2 ^ 59
def prefixEnd_2315581 : Nat := 4983230072969 + 3 ^ 40 * 2315581 * 2
def baseEnd_2315581 : Nat := 14679087005170493980103

theorem tailTrace_2315581 : CollatzResearch.WordTrace tailWord_2315581 prefixEnd_2315581 14679087005170493980103 := by
  unfold tailWord_2315581
  simp only [CollatzResearch.WordTrace]
  refine ⟨84456177424052981594954597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56304118282701987729969731 84456177424052981594954597)
  ·
    refine ⟨15835533267009934049053987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 84456177424052981594954597 15835533267009934049053987)
    ·
      refine ⟨23753299900514901073580981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15835533267009934049053987 23753299900514901073580981)
      ·
        refine ⟨2226871865673271975648217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 23753299900514901073580981 2226871865673271975648217)
        ·
          refine ⟨1670153899254953981736163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2226871865673271975648217 1670153899254953981736163)
          ·
            refine ⟨2505230848882430972604245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1670153899254953981736163 2505230848882430972604245)
            ·
              refine ⟨14679087005170493980103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2505230848882430972604245 14679087005170493980103)
              ·
                rfl

theorem cell23_2315581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 9].length) (baseStart_2315581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2315581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2315581 prefixEnd_2315581 := by exact prefixLift 2315581
  have htrace : WordTrace (prefixWord ++ tailWord_2315581) baseStart_2315581 baseEnd_2315581 := by
    simpa [prefixWord, tailWord_2315581, baseEnd_2315581] using wordTrace_append hprefix tailTrace_2315581
  have hstable : (prefixWord ++ tailWord_2315581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2315581).length < 2 ^ (prefixWord ++ tailWord_2315581).sum := by decide
  have hdescent : baseEnd_2315581 < baseStart_2315581 := by decide
  rcases family_descends (prefixWord ++ tailWord_2315581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2315704 : List Nat := [2, 1, 2, 1, 2, 2, 2, 4, 2, 1, 4]
def baseStart_2315704 : Nat := 118140960795 + 2315704 * 2 ^ 59
def prefixEnd_2315704 : Nat := 4983230072969 + 3 ^ 40 * 2315704 * 2
def baseEnd_2315704 : Nat := 1189069205539313031150277

theorem tailTrace_2315704 : CollatzResearch.WordTrace tailWord_2315704 prefixEnd_2315704 1189069205539313031150277 := by
  unfold tailWord_2315704
  simp only [CollatzResearch.WordTrace]
  refine ⟨42230331801303686800841083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56307109068404915734454777 42230331801303686800841083)
  ·
    refine ⟨63345497701955530201261625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42230331801303686800841083 63345497701955530201261625)
    ·
      refine ⟨47509123276466647650946219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63345497701955530201261625 47509123276466647650946219)
      ·
        refine ⟨71263684914699971476419329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47509123276466647650946219 71263684914699971476419329)
        ·
          refine ⟨53447763686024978607314497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71263684914699971476419329 53447763686024978607314497)
          ·
            refine ⟨40085822764518733955485873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53447763686024978607314497 40085822764518733955485873)
            ·
              refine ⟨30064367073389050466614405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40085822764518733955485873 30064367073389050466614405)
              ·
                refine ⟨5637068826260446962490201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30064367073389050466614405 5637068826260446962490201)
                ·
                  refine ⟨4227801619695335221867651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5637068826260446962490201 4227801619695335221867651)
                  ·
                    refine ⟨6341702429543002832801477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4227801619695335221867651 6341702429543002832801477)
                    ·
                      refine ⟨1189069205539313031150277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6341702429543002832801477 1189069205539313031150277)
                      ·
                        rfl

theorem cell23_2315704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 4, 2, 1, 4].length) (baseStart_2315704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2315704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2315704 prefixEnd_2315704 := by exact prefixLift 2315704
  have htrace : WordTrace (prefixWord ++ tailWord_2315704) baseStart_2315704 baseEnd_2315704 := by
    simpa [prefixWord, tailWord_2315704, baseEnd_2315704] using wordTrace_append hprefix tailTrace_2315704
  have hstable : (prefixWord ++ tailWord_2315704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2315704).length < 2 ^ (prefixWord ++ tailWord_2315704).sum := by decide
  have hdescent : baseEnd_2315704 < baseStart_2315704 := by decide
  rcases family_descends (prefixWord ++ tailWord_2315704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2315741 : List Nat := [1, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3]
def baseStart_2315741 : Nat := 118140960795 + 2315741 * 2 ^ 59
def prefixEnd_2315741 : Nat := 4983230072969 + 3 ^ 40 * 2315741 * 2
def baseEnd_2315741 : Nat := 1189088204323529386387607

theorem tailTrace_2315741 : CollatzResearch.WordTrace tailWord_2315741 prefixEnd_2315741 1189088204323529386387607 := by
  unfold tailWord_2315741
  simp only [CollatzResearch.WordTrace]
  refine ⟨84462013103473328920779077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56308008735648885947186051 84462013103473328920779077)
  ·
    refine ⟨15836627456901249172646077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 84462013103473328920779077 15836627456901249172646077)
    ·
      refine ⟨5938735296337968439742279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15836627456901249172646077 5938735296337968439742279)
      ·
        refine ⟨8908102944506952659613419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5938735296337968439742279 8908102944506952659613419)
        ·
          refine ⟨13362154416760428989420129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8908102944506952659613419 13362154416760428989420129)
          ·
            refine ⟨10021615812570321742065097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13362154416760428989420129 10021615812570321742065097)
            ·
              refine ⟨7516211859427741306548823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10021615812570321742065097 7516211859427741306548823)
              ·
                refine ⟨11274317789141611959823235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7516211859427741306548823 11274317789141611959823235)
                ·
                  refine ⟨16911476683712417939734853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11274317789141611959823235 16911476683712417939734853)
                  ·
                    refine ⟨3170901878196078363700285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16911476683712417939734853 3170901878196078363700285)
                    ·
                      refine ⟨1189088204323529386387607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3170901878196078363700285 1189088204323529386387607)
                      ·
                        rfl

theorem cell23_2315741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3].length) (baseStart_2315741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2315741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2315741 prefixEnd_2315741 := by exact prefixLift 2315741
  have htrace : WordTrace (prefixWord ++ tailWord_2315741) baseStart_2315741 baseEnd_2315741 := by
    simpa [prefixWord, tailWord_2315741, baseEnd_2315741] using wordTrace_append hprefix tailTrace_2315741
  have hstable : (prefixWord ++ tailWord_2315741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2315741).length < 2 ^ (prefixWord ++ tailWord_2315741).sum := by decide
  have hdescent : baseEnd_2315741 < baseStart_2315741 := by decide
  rcases family_descends (prefixWord ++ tailWord_2315741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2315765 : List Nat := [1, 3, 5, 1, 1, 3, 1, 1, 3, 4]
def baseStart_2315765 : Nat := 118140960795 + 2315765 * 2 ^ 59
def prefixEnd_2315765 : Nat := 4983230072969 + 3 ^ 40 * 2315765 * 2
def baseEnd_2315765 : Nat := 396366842619745764162499

theorem tailTrace_2315765 : CollatzResearch.WordTrace tailWord_2315765 prefixEnd_2315765 396366842619745764162499 := by
  unfold tailWord_2315765
  simp only [CollatzResearch.WordTrace]
  refine ⟨84462888455386381019652749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56308592303590920679768499 84462888455386381019652749)
  ·
    refine ⟨31673583170769892882369781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84462888455386381019652749 31673583170769892882369781)
    ·
      refine ⟨2969398422259677457722167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 31673583170769892882369781 2969398422259677457722167)
      ·
        refine ⟨4454097633389516186583251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2969398422259677457722167 4454097633389516186583251)
        ·
          refine ⟨6681146450084274279874877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4454097633389516186583251 6681146450084274279874877)
          ·
            refine ⟨2505429918781602854953079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6681146450084274279874877 2505429918781602854953079)
            ·
              refine ⟨3758144878172404282429619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2505429918781602854953079 3758144878172404282429619)
              ·
                refine ⟨5637217317258606423644429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3758144878172404282429619 5637217317258606423644429)
                ·
                  refine ⟨2113956493971977408866661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5637217317258606423644429 2113956493971977408866661)
                  ·
                    refine ⟨396366842619745764162499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2113956493971977408866661 396366842619745764162499)
                    ·
                      rfl

theorem cell23_2315765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 1, 1, 3, 4].length) (baseStart_2315765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2315765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2315765 prefixEnd_2315765 := by exact prefixLift 2315765
  have htrace : WordTrace (prefixWord ++ tailWord_2315765) baseStart_2315765 baseEnd_2315765 := by
    simpa [prefixWord, tailWord_2315765, baseEnd_2315765] using wordTrace_append hprefix tailTrace_2315765
  have hstable : (prefixWord ++ tailWord_2315765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2315765).length < 2 ^ (prefixWord ++ tailWord_2315765).sum := by decide
  have hdescent : baseEnd_2315765 < baseStart_2315765 := by decide
  rcases family_descends (prefixWord ++ tailWord_2315765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2315778 : List Nat := [3, 4, 1, 2, 1, 2, 1, 3, 6]
def baseStart_2315778 : Nat := 118140960795 + 2315778 * 2 ^ 59
def prefixEnd_2315778 : Nat := 4983230072969 + 3 ^ 40 * 2315778 * 2
def baseEnd_2315778 : Nat := 132123022567527304624993

theorem tailTrace_2315778 : CollatzResearch.WordTrace tailWord_2315778 prefixEnd_2315778 132123022567527304624993 := by
  unfold tailWord_2315778
  simp only [CollatzResearch.WordTrace]
  refine ⟨21115840651084821059968997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56308908402892856159917325 21115840651084821059968997)
  ·
    refine ⟨3959220122078403948744187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21115840651084821059968997 3959220122078403948744187)
    ·
      refine ⟨5938830183117605923116281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3959220122078403948744187 5938830183117605923116281)
      ·
        refine ⟨4454122637338204442337211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5938830183117605923116281 4454122637338204442337211)
        ·
          refine ⟨6681183956007306663505817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4454122637338204442337211 6681183956007306663505817)
          ·
            refine ⟨5010887967005479997629363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6681183956007306663505817 5010887967005479997629363)
            ·
              refine ⟨7516331950508219996444045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5010887967005479997629363 7516331950508219996444045)
              ·
                refine ⟨2818624481440582498666517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7516331950508219996444045 2818624481440582498666517)
                ·
                  refine ⟨132123022567527304624993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2818624481440582498666517 132123022567527304624993)
                  ·
                    rfl

theorem cell23_2315778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 1, 3, 6].length) (baseStart_2315778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2315778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2315778 prefixEnd_2315778 := by exact prefixLift 2315778
  have htrace : WordTrace (prefixWord ++ tailWord_2315778) baseStart_2315778 baseEnd_2315778 := by
    simpa [prefixWord, tailWord_2315778, baseEnd_2315778] using wordTrace_append hprefix tailTrace_2315778
  have hstable : (prefixWord ++ tailWord_2315778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2315778).length < 2 ^ (prefixWord ++ tailWord_2315778).sum := by decide
  have hdescent : baseEnd_2315778 < baseStart_2315778 := by decide
  rcases family_descends (prefixWord ++ tailWord_2315778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2315781 : List Nat := [1, 3, 1, 1, 2, 2, 1, 1, 6, 3, 2]
def baseStart_2315781 : Nat := 118140960795 + 2315781 * 2 ^ 59
def prefixEnd_2315781 : Nat := 4983230072969 + 3 ^ 40 * 2315781 * 2
def baseEnd_2315781 : Nat := 1189108743549709229887423

theorem tailTrace_2315781 : CollatzResearch.WordTrace tailWord_2315781 prefixEnd_2315781 1189108743549709229887423 := by
  unfold tailWord_2315781
  simp only [CollatzResearch.WordTrace]
  refine ⟨84463472023328415752235197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56308981348885610501490131 84463472023328415752235197)
  ·
    refine ⟨31673802008748155907088199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84463472023328415752235197 31673802008748155907088199)
    ·
      refine ⟨47510703013122233860632299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31673802008748155907088199 47510703013122233860632299)
      ·
        refine ⟨71266054519683350790948449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47510703013122233860632299 71266054519683350790948449)
        ·
          refine ⟨53449540889762513093211337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71266054519683350790948449 53449540889762513093211337)
          ·
            refine ⟨40087155667321884819908503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53449540889762513093211337 40087155667321884819908503)
            ·
              refine ⟨60130733500982827229862755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40087155667321884819908503 60130733500982827229862755)
              ·
                refine ⟨90196100251474240844794133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60130733500982827229862755 90196100251474240844794133)
                ·
                  refine ⟨4227942199287855039599725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 90196100251474240844794133 4227942199287855039599725)
                  ·
                    refine ⟨1585478324732945639849897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4227942199287855039599725 1585478324732945639849897)
                    ·
                      refine ⟨1189108743549709229887423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1585478324732945639849897 1189108743549709229887423)
                      ·
                        rfl

theorem cell23_2315781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 1, 6, 3, 2].length) (baseStart_2315781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2315781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2315781 prefixEnd_2315781 := by exact prefixLift 2315781
  have htrace : WordTrace (prefixWord ++ tailWord_2315781) baseStart_2315781 baseEnd_2315781 := by
    simpa [prefixWord, tailWord_2315781, baseEnd_2315781] using wordTrace_append hprefix tailTrace_2315781
  have hstable : (prefixWord ++ tailWord_2315781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2315781).length < 2 ^ (prefixWord ++ tailWord_2315781).sum := by decide
  have hdescent : baseEnd_2315781 < baseStart_2315781 := by decide
  rcases family_descends (prefixWord ++ tailWord_2315781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2315805 : List Nat := [1, 4, 2, 2, 1, 1, 2, 5, 1, 1, 3]
def baseStart_2315805 : Nat := 118140960795 + 2315805 * 2 ^ 59
def prefixEnd_2315805 : Nat := 4983230072969 + 3 ^ 40 * 2315805 * 2
def baseEnd_2315805 : Nat := 1189121067085417135987313

theorem tailTrace_2315805 : CollatzResearch.WordTrace tailWord_2315805 prefixEnd_2315805 1189121067085417135987313 := by
  unfold tailWord_2315805
  simp only [CollatzResearch.WordTrace]
  refine ⟨84464347375241467851108869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56309564916827645234072579 84464347375241467851108869)
  ·
    refine ⟨15837065132857775222082913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 84464347375241467851108869 15837065132857775222082913)
    ·
      refine ⟨11877798849643331416562185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15837065132857775222082913 11877798849643331416562185)
      ·
        refine ⟨8908349137232498562421639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11877798849643331416562185 8908349137232498562421639)
        ·
          refine ⟨13362523705848747843632459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8908349137232498562421639 13362523705848747843632459)
          ·
            refine ⟨20043785558773121765448689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13362523705848747843632459 20043785558773121765448689)
            ·
              refine ⟨15032839169079841324086517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20043785558773121765448689 15032839169079841324086517)
              ·
                refine ⟨1409328672101235124133111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15032839169079841324086517 1409328672101235124133111)
                ·
                  refine ⟨2113993008151852686199667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1409328672101235124133111 2113993008151852686199667)
                  ·
                    refine ⟨3170989512227779029299501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2113993008151852686199667 3170989512227779029299501)
                    ·
                      refine ⟨1189121067085417135987313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3170989512227779029299501 1189121067085417135987313)
                      ·
                        rfl

theorem cell23_2315805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 5, 1, 1, 3].length) (baseStart_2315805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2315805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2315805 prefixEnd_2315805 := by exact prefixLift 2315805
  have htrace : WordTrace (prefixWord ++ tailWord_2315805) baseStart_2315805 baseEnd_2315805 := by
    simpa [prefixWord, tailWord_2315805, baseEnd_2315805] using wordTrace_append hprefix tailTrace_2315805
  have hstable : (prefixWord ++ tailWord_2315805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2315805).length < 2 ^ (prefixWord ++ tailWord_2315805).sum := by decide
  have hdescent : baseEnd_2315805 < baseStart_2315805 := by decide
  rcases family_descends (prefixWord ++ tailWord_2315805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2315822 : List Nat := [4, 1, 3, 1, 2, 2, 1, 4, 1, 1, 3]
def baseStart_2315822 : Nat := 118140960795 + 2315822 * 2 ^ 59
def prefixEnd_2315822 : Nat := 4983230072969 + 3 ^ 40 * 2315822 * 2
def baseEnd_2315822 : Nat := 1189129796256543569474735

theorem tailTrace_2315822 : CollatzResearch.WordTrace tailWord_2315822 prefixEnd_2315822 1189129796256543569474735 := by
  unfold tailWord_2315822
  simp only [CollatzResearch.WordTrace]
  refine ⟨10558120927022484969309715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56309978277453253169651813 10558120927022484969309715)
  ·
    refine ⟨15837181390533727453964573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10558120927022484969309715 15837181390533727453964573)
    ·
      refine ⟨5938943021450147795236715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15837181390533727453964573 5938943021450147795236715)
      ·
        refine ⟨8908414532175221692855073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5938943021450147795236715 8908414532175221692855073)
        ·
          refine ⟨6681310899131416269641305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8908414532175221692855073 6681310899131416269641305)
          ·
            refine ⟨5010983174348562202230979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6681310899131416269641305 5010983174348562202230979)
            ·
              refine ⟨7516474761522843303346469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5010983174348562202230979 7516474761522843303346469)
              ·
                refine ⟨1409339017785533119377463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7516474761522843303346469 1409339017785533119377463)
                ·
                  refine ⟨2114008526678299679066195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1409339017785533119377463 2114008526678299679066195)
                  ·
                    refine ⟨3171012790017449518599293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2114008526678299679066195 3171012790017449518599293)
                    ·
                      refine ⟨1189129796256543569474735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3171012790017449518599293 1189129796256543569474735)
                      ·
                        rfl

theorem cell23_2315822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 1, 4, 1, 1, 3].length) (baseStart_2315822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2315822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2315822 prefixEnd_2315822 := by exact prefixLift 2315822
  have htrace : WordTrace (prefixWord ++ tailWord_2315822) baseStart_2315822 baseEnd_2315822 := by
    simpa [prefixWord, tailWord_2315822, baseEnd_2315822] using wordTrace_append hprefix tailTrace_2315822
  have hstable : (prefixWord ++ tailWord_2315822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2315822).length < 2 ^ (prefixWord ++ tailWord_2315822).sum := by decide
  have hdescent : baseEnd_2315822 < baseStart_2315822 := by decide
  rcases family_descends (prefixWord ++ tailWord_2315822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2315824 : List Nat := [2, 1, 1, 1, 2, 3, 1, 1, 5, 2, 4]
def baseStart_2315824 : Nat := 118140960795 + 2315824 * 2 ^ 59
def prefixEnd_2315824 : Nat := 4983230072969 + 3 ^ 40 * 2315824 * 2
def baseEnd_2315824 : Nat := 1189130823217852561649725

theorem tailTrace_2315824 : CollatzResearch.WordTrace tailWord_2315824 prefixEnd_2315824 1189130823217852561649725 := by
  unfold tailWord_2315824
  simp only [CollatzResearch.WordTrace]
  refine ⟨42232520181086317048025263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56310026908115089397367017 42232520181086317048025263)
  ·
    refine ⟨63348780271629475572037895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42232520181086317048025263 63348780271629475572037895)
    ·
      refine ⟨95023170407444213358056843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63348780271629475572037895 95023170407444213358056843)
      ·
        refine ⟨142534755611166320037085265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95023170407444213358056843 142534755611166320037085265)
        ·
          refine ⟨106901066708374740027813949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 142534755611166320037085265 106901066708374740027813949)
          ·
            refine ⟨40087900015640527510430231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 106901066708374740027813949 40087900015640527510430231)
            ·
              refine ⟨60131850023460791265645347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40087900015640527510430231 60131850023460791265645347)
              ·
                refine ⟨90197775035191186898468021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60131850023460791265645347 90197775035191186898468021)
                ·
                  refine ⟨8456041409549173771731377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 90197775035191186898468021 8456041409549173771731377)
                  ·
                    refine ⟨6342031057161880328798533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8456041409549173771731377 6342031057161880328798533)
                    ·
                      refine ⟨1189130823217852561649725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6342031057161880328798533 1189130823217852561649725)
                      ·
                        rfl

theorem cell23_2315824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 5, 2, 4].length) (baseStart_2315824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2315824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2315824 prefixEnd_2315824 := by exact prefixLift 2315824
  have htrace : WordTrace (prefixWord ++ tailWord_2315824) baseStart_2315824 baseEnd_2315824 := by
    simpa [prefixWord, tailWord_2315824, baseEnd_2315824] using wordTrace_append hprefix tailTrace_2315824
  have hstable : (prefixWord ++ tailWord_2315824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2315824).length < 2 ^ (prefixWord ++ tailWord_2315824).sum := by decide
  have hdescent : baseEnd_2315824 < baseStart_2315824 := by decide
  rcases family_descends (prefixWord ++ tailWord_2315824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2315831 : List Nat := [1, 1, 3, 1, 2, 4, 1, 2, 3, 2, 3]
def baseStart_2315831 : Nat := 118140960795 + 2315831 * 2 ^ 59
def prefixEnd_2315831 : Nat := 4983230072969 + 3 ^ 40 * 2315831 * 2
def baseEnd_2315831 : Nat := 1189134417582434034262193

theorem tailTrace_2315831 : CollatzResearch.WordTrace tailWord_2315831 prefixEnd_2315831 1189134417582434034262193 := by
  unfold tailWord_2315831
  simp only [CollatzResearch.WordTrace]
  refine ⟨84465295673147274291555347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56310197115431516194370231 84465295673147274291555347)
  ·
    refine ⟨126697943509720911437333021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84465295673147274291555347 126697943509720911437333021)
    ·
      refine ⟨47511728816145341788999883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 126697943509720911437333021 47511728816145341788999883)
      ·
        refine ⟨71267593224218012683499825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47511728816145341788999883 71267593224218012683499825)
        ·
          refine ⟨53450694918163509512624869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71267593224218012683499825 53450694918163509512624869)
          ·
            refine ⟨10022005297155658033617163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 53450694918163509512624869 10022005297155658033617163)
            ·
              refine ⟨15033007945733487050425745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10022005297155658033617163 15033007945733487050425745)
              ·
                refine ⟨11274755959300115287819309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15033007945733487050425745 11274755959300115287819309)
                ·
                  refine ⟨4228033484737543232932241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11274755959300115287819309 4228033484737543232932241)
                  ·
                    refine ⟨3171025113553157424699181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4228033484737543232932241 3171025113553157424699181)
                    ·
                      refine ⟨1189134417582434034262193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3171025113553157424699181 1189134417582434034262193)
                      ·
                        rfl

theorem cell23_2315831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 2, 3, 2, 3].length) (baseStart_2315831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2315831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2315831 prefixEnd_2315831 := by exact prefixLift 2315831
  have htrace : WordTrace (prefixWord ++ tailWord_2315831) baseStart_2315831 baseEnd_2315831 := by
    simpa [prefixWord, tailWord_2315831, baseEnd_2315831] using wordTrace_append hprefix tailTrace_2315831
  have hstable : (prefixWord ++ tailWord_2315831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2315831).length < 2 ^ (prefixWord ++ tailWord_2315831).sum := by decide
  have hdescent : baseEnd_2315831 < baseStart_2315831 := by decide
  rcases family_descends (prefixWord ++ tailWord_2315831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2315905 : List Nat := [1, 2, 4, 2, 1, 2, 1, 4, 1, 3, 2]
def baseStart_2315905 : Nat := 118140960795 + 2315905 * 2 ^ 59
def prefixEnd_2315905 : Nat := 4983230072969 + 3 ^ 40 * 2315905 * 2
def baseEnd_2315905 : Nat := 1189172415150866744736853

theorem tailTrace_2315905 : CollatzResearch.WordTrace tailWord_2315905 prefixEnd_2315905 1189172415150866744736853 := by
  unfold tailWord_2315905
  simp only [CollatzResearch.WordTrace]
  refine ⟨84467994674879184929749169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56311996449919456619832779 84467994674879184929749169)
  ·
    refine ⟨63350996006159388697311877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84467994674879184929749169 63350996006159388697311877)
    ·
      refine ⟨11878311751154885380745977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 63350996006159388697311877 11878311751154885380745977)
      ·
        refine ⟨8908733813366164035559483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11878311751154885380745977 8908733813366164035559483)
        ·
          refine ⟨13363100720049246053339225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8908733813366164035559483 13363100720049246053339225)
          ·
            refine ⟨10022325540036934540004419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13363100720049246053339225 10022325540036934540004419)
            ·
              refine ⟨15033488310055401810006629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10022325540036934540004419 15033488310055401810006629)
              ·
                refine ⟨2818779058135387839376243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15033488310055401810006629 2818779058135387839376243)
                ·
                  refine ⟨4228168587203081759064365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2818779058135387839376243 4228168587203081759064365)
                  ·
                    refine ⟨1585563220201155659649137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4228168587203081759064365 1585563220201155659649137)
                    ·
                      refine ⟨1189172415150866744736853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1585563220201155659649137 1189172415150866744736853)
                      ·
                        rfl

theorem cell23_2315905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 4, 1, 3, 2].length) (baseStart_2315905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2315905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2315905 prefixEnd_2315905 := by exact prefixLift 2315905
  have htrace : WordTrace (prefixWord ++ tailWord_2315905) baseStart_2315905 baseEnd_2315905 := by
    simpa [prefixWord, tailWord_2315905, baseEnd_2315905] using wordTrace_append hprefix tailTrace_2315905
  have hstable : (prefixWord ++ tailWord_2315905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2315905).length < 2 ^ (prefixWord ++ tailWord_2315905).sum := by decide
  have hdescent : baseEnd_2315905 < baseStart_2315905 := by decide
  rcases family_descends (prefixWord ++ tailWord_2315905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2315941 : List Nat := [1, 3, 1, 2, 1, 2, 5, 1, 7]
def baseStart_2315941 : Nat := 118140960795 + 2315941 * 2 ^ 59
def prefixEnd_2315941 : Nat := 4983230072969 + 3 ^ 40 * 2315941 * 2
def baseEnd_2315941 : Nat := 132132322272714289320743

theorem tailTrace_2315941 : CollatzResearch.WordTrace tailWord_2315941 prefixEnd_2315941 132132322272714289320743 := by
  unfold tailWord_2315941
  simp only [CollatzResearch.WordTrace]
  refine ⟨84469307702748763078059677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56312871801832508718706451 84469307702748763078059677)
  ·
    refine ⟨31675990388530786154272379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84469307702748763078059677 31675990388530786154272379)
    ·
      refine ⟨47513985582796179231408569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31675990388530786154272379 47513985582796179231408569)
      ·
        refine ⟨35635489187097134423556427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47513985582796179231408569 35635489187097134423556427)
        ·
          refine ⟨53453233780645701635334641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35635489187097134423556427 53453233780645701635334641)
          ·
            refine ⟨40089925335484276226500981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53453233780645701635334641 40089925335484276226500981)
            ·
              refine ⟨3758430500201650896234467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 40089925335484276226500981 3758430500201650896234467)
              ·
                refine ⟨5637645750302476344351701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3758430500201650896234467 5637645750302476344351701)
                ·
                  refine ⟨132132322272714289320743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5637645750302476344351701 132132322272714289320743)
                  ·
                    rfl

theorem cell23_2315941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 5, 1, 7].length) (baseStart_2315941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2315941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2315941 prefixEnd_2315941 := by exact prefixLift 2315941
  have htrace : WordTrace (prefixWord ++ tailWord_2315941) baseStart_2315941 baseEnd_2315941 := by
    simpa [prefixWord, tailWord_2315941, baseEnd_2315941] using wordTrace_append hprefix tailTrace_2315941
  have hstable : (prefixWord ++ tailWord_2315941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2315941).length < 2 ^ (prefixWord ++ tailWord_2315941).sum := by decide
  have hdescent : baseEnd_2315941 < baseStart_2315941 := by decide
  rcases family_descends (prefixWord ++ tailWord_2315941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2315951 : List Nat := [1, 1, 2, 1, 2, 4, 2, 1, 1, 5, 3]
def baseStart_2315951 : Nat := 118140960795 + 2315951 * 2 ^ 59
def prefixEnd_2315951 : Nat := 4983230072969 + 3 ^ 40 * 2315951 * 2
def baseEnd_2315951 : Nat := 1189196035260973564761641

theorem tailTrace_2315951 : CollatzResearch.WordTrace tailWord_2315951 prefixEnd_2315951 1189196035260973564761641 := by
  unfold tailWord_2315951
  simp only [CollatzResearch.WordTrace]
  refine ⟨84469672432712534785923707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56313114955141689857282471 84469672432712534785923707)
  ·
    refine ⟨126704508649068802178885561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84469672432712534785923707 126704508649068802178885561)
    ·
      refine ⟨95028381486801601634164171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126704508649068802178885561 95028381486801601634164171)
      ·
        refine ⟨142542572230202402451246257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95028381486801601634164171 142542572230202402451246257)
        ·
          refine ⟨106906929172651801838434693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 142542572230202402451246257 106906929172651801838434693)
          ·
            refine ⟨20045049219872212844706505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 106906929172651801838434693 20045049219872212844706505)
            ·
              refine ⟨15033786914904159633529879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20045049219872212844706505 15033786914904159633529879)
              ·
                refine ⟨22550680372356239450294819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15033786914904159633529879 22550680372356239450294819)
                ·
                  refine ⟨33826020558534359175442229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22550680372356239450294819 33826020558534359175442229)
                  ·
                    refine ⟨3171189427362596172697709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 33826020558534359175442229 3171189427362596172697709)
                    ·
                      refine ⟨1189196035260973564761641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3171189427362596172697709 1189196035260973564761641)
                      ·
                        rfl

theorem cell23_2315951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 1, 1, 5, 3].length) (baseStart_2315951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2315951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2315951 prefixEnd_2315951 := by exact prefixLift 2315951
  have htrace : WordTrace (prefixWord ++ tailWord_2315951) baseStart_2315951 baseEnd_2315951 := by
    simpa [prefixWord, tailWord_2315951, baseEnd_2315951] using wordTrace_append hprefix tailTrace_2315951
  have hstable : (prefixWord ++ tailWord_2315951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2315951).length < 2 ^ (prefixWord ++ tailWord_2315951).sum := by decide
  have hdescent : baseEnd_2315951 < baseStart_2315951 := by decide
  rcases family_descends (prefixWord ++ tailWord_2315951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2315952 : List Nat := [2, 1, 1, 1, 2, 1, 8, 1, 2, 2, 2]
def baseStart_2315952 : Nat := 118140960795 + 2315952 * 2 ^ 59
def prefixEnd_2315952 : Nat := 4983230072969 + 3 ^ 40 * 2315952 * 2
def baseEnd_2315952 : Nat := 1189196548741628060849137

theorem tailTrace_2315952 : CollatzResearch.WordTrace tailWord_2315952 prefixEnd_2315952 1189196548741628060849137 := by
  unfold tailWord_2315952
  simp only [CollatzResearch.WordTrace]
  refine ⟨42234854452854455978355055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56313139270472607971140073 42234854452854455978355055)
  ·
    refine ⟨63352281679281683967532583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42234854452854455978355055 63352281679281683967532583)
    ·
      refine ⟨95028422518922525951298875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63352281679281683967532583 95028422518922525951298875)
      ·
        refine ⟨142542633778383788926948313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95028422518922525951298875 142542633778383788926948313)
        ·
          refine ⟨106906975333787841695211235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 142542633778383788926948313 106906975333787841695211235)
          ·
            refine ⟨160360463000681762542816853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106906975333787841695211235 160360463000681762542816853)
            ·
              refine ⟨1879224175789239404798635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 160360463000681762542816853 1879224175789239404798635)
              ·
                refine ⟨2818836263683859107197953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1879224175789239404798635 2818836263683859107197953)
                ·
                  refine ⟨2114127197762894330398465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2818836263683859107197953 2114127197762894330398465)
                  ·
                    refine ⟨1585595398322170747798849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2114127197762894330398465 1585595398322170747798849)
                    ·
                      refine ⟨1189196548741628060849137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1585595398322170747798849 1189196548741628060849137)
                      ·
                        rfl

theorem cell23_2315952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 8, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 8, 1, 2, 2, 2].length) (baseStart_2315952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2315952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2315952 prefixEnd_2315952 := by exact prefixLift 2315952
  have htrace : WordTrace (prefixWord ++ tailWord_2315952) baseStart_2315952 baseEnd_2315952 := by
    simpa [prefixWord, tailWord_2315952, baseEnd_2315952] using wordTrace_append hprefix tailTrace_2315952
  have hstable : (prefixWord ++ tailWord_2315952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2315952).length < 2 ^ (prefixWord ++ tailWord_2315952).sum := by decide
  have hdescent : baseEnd_2315952 < baseStart_2315952 := by decide
  rcases family_descends (prefixWord ++ tailWord_2315952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2316028 : List Nat := [2, 2, 2, 1, 3, 1, 3, 1, 1, 4, 3]
def baseStart_2316028 : Nat := 118140960795 + 2316028 * 2 ^ 59
def prefixEnd_2316028 : Nat := 4983230072969 + 3 ^ 40 * 2316028 * 2
def baseEnd_2316028 : Nat := 1189235573271369763498787

theorem tailTrace_2316028 : CollatzResearch.WordTrace tailWord_2316028 prefixEnd_2316028 1189235573271369763498787 := by
  unfold tailWord_2316028
  simp only [CollatzResearch.WordTrace]
  refine ⟨42236240426716788468238369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56314987235622384624317825 42236240426716788468238369)
  ·
    refine ⟨31677180320037591351178777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42236240426716788468238369 31677180320037591351178777)
    ·
      refine ⟨23757885240028193513384083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31677180320037591351178777 23757885240028193513384083)
      ·
        refine ⟨35636827860042290270076125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23757885240028193513384083 35636827860042290270076125)
        ·
          refine ⟨13363810447515858851278547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35636827860042290270076125 13363810447515858851278547)
          ·
            refine ⟨20045715671273788276917821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13363810447515858851278547 20045715671273788276917821)
            ·
              refine ⟨7517143376727670603844183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20045715671273788276917821 7517143376727670603844183)
              ·
                refine ⟨11275715065091505905766275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7517143376727670603844183 11275715065091505905766275)
                ·
                  refine ⟨16913572597637258858649413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11275715065091505905766275 16913572597637258858649413)
                  ·
                    refine ⟨3171294862056986035996765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16913572597637258858649413 3171294862056986035996765)
                    ·
                      refine ⟨1189235573271369763498787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3171294862056986035996765 1189235573271369763498787)
                      ·
                        rfl

theorem cell23_2316028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 3, 1, 1, 4, 3].length) (baseStart_2316028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2316028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2316028 prefixEnd_2316028 := by exact prefixLift 2316028
  have htrace : WordTrace (prefixWord ++ tailWord_2316028) baseStart_2316028 baseEnd_2316028 := by
    simpa [prefixWord, tailWord_2316028, baseEnd_2316028] using wordTrace_append hprefix tailTrace_2316028
  have hstable : (prefixWord ++ tailWord_2316028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2316028).length < 2 ^ (prefixWord ++ tailWord_2316028).sum := by decide
  have hdescent : baseEnd_2316028 < baseStart_2316028 := by decide
  rcases family_descends (prefixWord ++ tailWord_2316028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2316035 : List Nat := [1, 1, 1, 3, 2, 2, 3, 5, 1, 4]
def baseStart_2316035 : Nat := 118140960795 + 2316035 * 2 ^ 59
def prefixEnd_2316035 : Nat := 4983230072969 + 3 ^ 40 * 2316035 * 2
def baseEnd_2316035 : Nat := 396413055878650412037085

theorem tailTrace_2316035 : CollatzResearch.WordTrace tailWord_2316035 prefixEnd_2316035 396413055878650412037085 := by
  unfold tailWord_2316035
  simp only [CollatzResearch.WordTrace]
  refine ⟨84472736164408217131981559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56315157442938811421321039 84472736164408217131981559)
  ·
    refine ⟨126709104246612325697972339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84472736164408217131981559 126709104246612325697972339)
    ·
      refine ⟨190063656369918488546958509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126709104246612325697972339 190063656369918488546958509)
      ·
        refine ⟨71273871138719433205109441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 190063656369918488546958509 71273871138719433205109441)
        ·
          refine ⟨53455403354039574903832081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71273871138719433205109441 53455403354039574903832081)
          ·
            refine ⟨40091552515529681177874061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53455403354039574903832081 40091552515529681177874061)
            ·
              refine ⟨15034332193323630441702773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40091552515529681177874061 15034332193323630441702773)
              ·
                refine ⟨1409468643124090353909635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15034332193323630441702773 1409468643124090353909635)
                ·
                  refine ⟨2114202964686135530864453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1409468643124090353909635 2114202964686135530864453)
                  ·
                    refine ⟨396413055878650412037085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2114202964686135530864453 396413055878650412037085)
                    ·
                      rfl

theorem cell23_2316035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 5, 1, 4].length) (baseStart_2316035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2316035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2316035 prefixEnd_2316035 := by exact prefixLift 2316035
  have htrace : WordTrace (prefixWord ++ tailWord_2316035) baseStart_2316035 baseEnd_2316035 := by
    simpa [prefixWord, tailWord_2316035, baseEnd_2316035] using wordTrace_append hprefix tailTrace_2316035
  have hstable : (prefixWord ++ tailWord_2316035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2316035).length < 2 ^ (prefixWord ++ tailWord_2316035).sum := by decide
  have hdescent : baseEnd_2316035 < baseStart_2316035 := by decide
  rcases family_descends (prefixWord ++ tailWord_2316035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2316065 : List Nat := [1, 2, 3, 2, 1, 4, 3, 1, 6]
def baseStart_2316065 : Nat := 118140960795 + 2316065 * 2 ^ 59
def prefixEnd_2316065 : Nat := 4983230072969 + 3 ^ 40 * 2316065 * 2
def baseEnd_2316065 : Nat := 132139396895065124304013

theorem tailTrace_2316065 : CollatzResearch.WordTrace tailWord_2316065 prefixEnd_2316065 132139396895065124304013 := by
  unfold tailWord_2316065
  simp only [CollatzResearch.WordTrace]
  refine ⟨84473830354299532255573649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56315886902866354837049099 84473830354299532255573649)
  ·
    refine ⟨63355372765724649191680237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84473830354299532255573649 63355372765724649191680237)
    ·
      refine ⟨23758264787146743446880089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63355372765724649191680237 23758264787146743446880089)
      ·
        refine ⟨17818698590360057585160067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23758264787146743446880089 17818698590360057585160067)
        ·
          refine ⟨26728047885540086377740101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17818698590360057585160067 26728047885540086377740101)
          ·
            refine ⟨5011508978538766195826269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26728047885540086377740101 5011508978538766195826269)
            ·
              refine ⟨1879315866952037323434851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5011508978538766195826269 1879315866952037323434851)
              ·
                refine ⟨2818973800428055985152277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1879315866952037323434851 2818973800428055985152277)
                ·
                  refine ⟨132139396895065124304013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2818973800428055985152277 132139396895065124304013)
                  ·
                    rfl

theorem cell23_2316065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 3, 1, 6].length) (baseStart_2316065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2316065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2316065 prefixEnd_2316065 := by exact prefixLift 2316065
  have htrace : WordTrace (prefixWord ++ tailWord_2316065) baseStart_2316065 baseEnd_2316065 := by
    simpa [prefixWord, tailWord_2316065, baseEnd_2316065] using wordTrace_append hprefix tailTrace_2316065
  have hstable : (prefixWord ++ tailWord_2316065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2316065).length < 2 ^ (prefixWord ++ tailWord_2316065).sum := by decide
  have hdescent : baseEnd_2316065 < baseStart_2316065 := by decide
  rcases family_descends (prefixWord ++ tailWord_2316065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2316086 : List Nat := [5, 1, 2, 2, 1, 3, 1, 3, 1, 4]
def baseStart_2316086 : Nat := 118140960795 + 2316086 * 2 ^ 59
def prefixEnd_2316086 : Nat := 4983230072969 + 3 ^ 40 * 2316086 * 2
def baseEnd_2316086 : Nat := 396421785049776845524507

theorem tailTrace_2316086 : CollatzResearch.WordTrace tailWord_2316086 prefixEnd_2316086 396421785049776845524507 := by
  unfold tailWord_2316086
  simp only [CollatzResearch.WordTrace]
  refine ⟨5279662267951465802630507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 56316397524815635228058741 5279662267951465802630507)
  ·
    refine ⟨7919493401927198703945761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5279662267951465802630507 7919493401927198703945761)
    ·
      refine ⟨5939620051445399027959321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7919493401927198703945761 5939620051445399027959321)
      ·
        refine ⟨4454715038584049270969491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5939620051445399027959321 4454715038584049270969491)
        ·
          refine ⟨6682072557876073906454237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4454715038584049270969491 6682072557876073906454237)
          ·
            refine ⟨2505777209203527714920339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6682072557876073906454237 2505777209203527714920339)
            ·
              refine ⟨3758665813805291572380509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2505777209203527714920339 3758665813805291572380509)
              ·
                refine ⟨1409499680176984339642691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3758665813805291572380509 1409499680176984339642691)
                ·
                  refine ⟨2114249520265476509464037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1409499680176984339642691 2114249520265476509464037)
                  ·
                    refine ⟨396421785049776845524507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2114249520265476509464037 396421785049776845524507)
                    ·
                      rfl

theorem cell23_2316086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 1, 3, 1, 4].length) (baseStart_2316086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2316086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2316086 prefixEnd_2316086 := by exact prefixLift 2316086
  have htrace : WordTrace (prefixWord ++ tailWord_2316086) baseStart_2316086 baseEnd_2316086 := by
    simpa [prefixWord, tailWord_2316086, baseEnd_2316086] using wordTrace_append hprefix tailTrace_2316086
  have hstable : (prefixWord ++ tailWord_2316086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2316086).length < 2 ^ (prefixWord ++ tailWord_2316086).sum := by decide
  have hdescent : baseEnd_2316086 < baseStart_2316086 := by decide
  rcases family_descends (prefixWord ++ tailWord_2316086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2316109 : List Nat := [1, 6, 1, 2, 1, 1, 3, 1, 3, 1, 3]
def baseStart_2316109 : Nat := 118140960795 + 2316109 * 2 ^ 59
def prefixEnd_2316109 : Nat := 4983230072969 + 3 ^ 40 * 2316109 * 2
def baseEnd_2316109 : Nat := 1189277165204383946585915

theorem tailTrace_2316109 : CollatzResearch.WordTrace tailWord_2316109 prefixEnd_2316109 1189277165204383946585915 := by
  unfold tailWord_2316109
  simp only [CollatzResearch.WordTrace]
  refine ⟨84475435166140127770175381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56316956777426751846783587 84475435166140127770175381)
  ·
    refine ⟨3959786023412818489226971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 84475435166140127770175381 3959786023412818489226971)
    ·
      refine ⟨5939679035119227733840457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3959786023412818489226971 5939679035119227733840457)
      ·
        refine ⟨4454759276339420800380343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5939679035119227733840457 4454759276339420800380343)
        ·
          refine ⟨6682138914509131200570515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4454759276339420800380343 6682138914509131200570515)
          ·
            refine ⟨10023208371763696800855773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6682138914509131200570515 10023208371763696800855773)
            ·
              refine ⟨3758703139411386300320915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10023208371763696800855773 3758703139411386300320915)
              ·
                refine ⟨5638054709117079450481373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3758703139411386300320915 5638054709117079450481373)
                ·
                  refine ⟨2114270515918904793930515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5638054709117079450481373 2114270515918904793930515)
                  ·
                    refine ⟨3171405773878357190895773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2114270515918904793930515 3171405773878357190895773)
                    ·
                      refine ⟨1189277165204383946585915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3171405773878357190895773 1189277165204383946585915)
                      ·
                        rfl

theorem cell23_2316109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 3, 1, 3, 1, 3].length) (baseStart_2316109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2316109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2316109 prefixEnd_2316109 := by exact prefixLift 2316109
  have htrace : WordTrace (prefixWord ++ tailWord_2316109) baseStart_2316109 baseEnd_2316109 := by
    simpa [prefixWord, tailWord_2316109, baseEnd_2316109] using wordTrace_append hprefix tailTrace_2316109
  have hstable : (prefixWord ++ tailWord_2316109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2316109).length < 2 ^ (prefixWord ++ tailWord_2316109).sum := by decide
  have hdescent : baseEnd_2316109 < baseStart_2316109 := by decide
  rcases family_descends (prefixWord ++ tailWord_2316109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2316128 : List Nat := [2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 6]
def baseStart_2316128 : Nat := 118140960795 + 2316128 * 2 ^ 59
def prefixEnd_2316128 : Nat := 4983230072969 + 3 ^ 40 * 2316128 * 2
def baseEnd_2316128 : Nat := 1189286921336819372248327

theorem tailTrace_2316128 : CollatzResearch.WordTrace tailWord_2316128 prefixEnd_2316128 1189286921336819372248327 := by
  unfold tailWord_2316128
  simp only [CollatzResearch.WordTrace]
  refine ⟨42238064076535647007558519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56317418768714196010078025 42238064076535647007558519)
  ·
    refine ⟨63357096114803470511337779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42238064076535647007558519 63357096114803470511337779)
    ·
      refine ⟨95035644172205205767006669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63357096114803470511337779 95035644172205205767006669)
      ·
        refine ⟨35638366564576952162627501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95035644172205205767006669 35638366564576952162627501)
        ·
          refine ⟨13364387461716357060985313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35638366564576952162627501 13364387461716357060985313)
          ·
            refine ⟨10023290596287267795738985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13364387461716357060985313 10023290596287267795738985)
            ·
              refine ⟨7517467947215450846804239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10023290596287267795738985 7517467947215450846804239)
              ·
                refine ⟨11276201920823176270206359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7517467947215450846804239 11276201920823176270206359)
                ·
                  refine ⟨16914302881234764405309539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11276201920823176270206359 16914302881234764405309539)
                  ·
                    refine ⟨25371454321852146607964309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16914302881234764405309539 25371454321852146607964309)
                    ·
                      refine ⟨1189286921336819372248327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 25371454321852146607964309 1189286921336819372248327)
                      ·
                        rfl

theorem cell23_2316128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 6].length) (baseStart_2316128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2316128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2316128 prefixEnd_2316128 := by exact prefixLift 2316128
  have htrace : WordTrace (prefixWord ++ tailWord_2316128) baseStart_2316128 baseEnd_2316128 := by
    simpa [prefixWord, tailWord_2316128, baseEnd_2316128] using wordTrace_append hprefix tailTrace_2316128
  have hstable : (prefixWord ++ tailWord_2316128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2316128).length < 2 ^ (prefixWord ++ tailWord_2316128).sum := by decide
  have hdescent : baseEnd_2316128 < baseStart_2316128 := by decide
  rcases family_descends (prefixWord ++ tailWord_2316128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2316135 : List Nat := [1, 1, 5, 1, 2, 1, 3, 1, 3, 2, 3]
def baseStart_2316135 : Nat := 118140960795 + 2316135 * 2 ^ 59
def prefixEnd_2316135 : Nat := 4983230072969 + 3 ^ 40 * 2316135 * 2
def baseEnd_2316135 : Nat := 1189290515701400844860795

theorem tailTrace_2316135 : CollatzResearch.WordTrace tailWord_2316135 prefixEnd_2316135 1189290515701400844860795 := by
  unfold tailWord_2316135
  simp only [CollatzResearch.WordTrace]
  refine ⟨84476383464045934210621859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56317588976030622807081239 84476383464045934210621859)
  ·
    refine ⟨126714575196068901315932789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84476383464045934210621859 126714575196068901315932789)
    ·
      refine ⟨11879491424631459498368699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 126714575196068901315932789 11879491424631459498368699)
      ·
        refine ⟨17819237136947189247553049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11879491424631459498368699 17819237136947189247553049)
        ·
          refine ⟨13364427852710391935664787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17819237136947189247553049 13364427852710391935664787)
          ·
            refine ⟨20046641779065587903497181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13364427852710391935664787 20046641779065587903497181)
            ·
              refine ⟨7517490667149595463811443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20046641779065587903497181 7517490667149595463811443)
              ·
                refine ⟨11276236000724393195717165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7517490667149595463811443 11276236000724393195717165)
                ·
                  refine ⟨4228588500271647448393937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11276236000724393195717165 4228588500271647448393937)
                  ·
                    refine ⟨3171441375203735586295453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4228588500271647448393937 3171441375203735586295453)
                    ·
                      refine ⟨1189290515701400844860795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3171441375203735586295453 1189290515701400844860795)
                      ·
                        rfl

theorem cell23_2316135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 3, 1, 3, 2, 3].length) (baseStart_2316135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2316135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2316135 prefixEnd_2316135 := by exact prefixLift 2316135
  have htrace : WordTrace (prefixWord ++ tailWord_2316135) baseStart_2316135 baseEnd_2316135 := by
    simpa [prefixWord, tailWord_2316135, baseEnd_2316135] using wordTrace_append hprefix tailTrace_2316135
  have hstable : (prefixWord ++ tailWord_2316135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2316135).length < 2 ^ (prefixWord ++ tailWord_2316135).sum := by decide
  have hdescent : baseEnd_2316135 < baseStart_2316135 := by decide
  rcases family_descends (prefixWord ++ tailWord_2316135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2316192 : List Nat := [2, 1, 1, 4, 1, 1, 1, 6, 1, 3, 2]
def baseStart_2316192 : Nat := 118140960795 + 2316192 * 2 ^ 59
def prefixEnd_2316192 : Nat := 4983230072969 + 3 ^ 40 * 2316192 * 2
def baseEnd_2316192 : Nat := 1189319784098707121848033

theorem tailTrace_2316192 : CollatzResearch.WordTrace tailWord_2316192 prefixEnd_2316192 1189319784098707121848033 := by
  unfold tailWord_2316192
  simp only [CollatzResearch.WordTrace]
  refine ⟨42239231212419716472723415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56318974949892955296964553 42239231212419716472723415)
  ·
    refine ⟨63358846818629574709085123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42239231212419716472723415 63358846818629574709085123)
    ·
      refine ⟨95038270227944362063627685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63358846818629574709085123 95038270227944362063627685)
      ·
        refine ⟨17819675667739567886930191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 95038270227944362063627685 17819675667739567886930191)
        ·
          refine ⟨26729513501609351830395287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17819675667739567886930191 26729513501609351830395287)
          ·
            refine ⟨40094270252414027745592931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26729513501609351830395287 40094270252414027745592931)
            ·
              refine ⟨60141405378621041618389397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40094270252414027745592931 60141405378621041618389397)
              ·
                refine ⟨2819128377122861325862003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 60141405378621041618389397 2819128377122861325862003)
                ·
                  refine ⟨4228692565684291988793005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2819128377122861325862003 4228692565684291988793005)
                  ·
                    refine ⟨1585759712131609495797377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4228692565684291988793005 1585759712131609495797377)
                    ·
                      refine ⟨1189319784098707121848033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1585759712131609495797377 1189319784098707121848033)
                      ·
                        rfl

theorem cell23_2316192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 6, 1, 3, 2].length) (baseStart_2316192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2316192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2316192 prefixEnd_2316192 := by exact prefixLift 2316192
  have htrace : WordTrace (prefixWord ++ tailWord_2316192) baseStart_2316192 baseEnd_2316192 := by
    simpa [prefixWord, tailWord_2316192, baseEnd_2316192] using wordTrace_append hprefix tailTrace_2316192
  have hstable : (prefixWord ++ tailWord_2316192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2316192).length < 2 ^ (prefixWord ++ tailWord_2316192).sum := by decide
  have hdescent : baseEnd_2316192 < baseStart_2316192 := by decide
  rcases family_descends (prefixWord ++ tailWord_2316192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2316200 : List Nat := [2, 1, 6, 2, 1, 1, 2, 3, 1, 2, 2]
def baseStart_2316200 : Nat := 118140960795 + 2316200 * 2 ^ 59
def prefixEnd_2316200 : Nat := 4983230072969 + 3 ^ 40 * 2316200 * 2
def baseEnd_2316200 : Nat := 1189323891943943090547997

theorem tailTrace_2316200 : CollatzResearch.WordTrace tailWord_2316200 prefixEnd_2316200 1189323891943943090547997 := by
  unfold tailWord_2316200
  simp only [CollatzResearch.WordTrace]
  refine ⟨42239377104405225155869027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56319169472540300207825369 42239377104405225155869027)
  ·
    refine ⟨63359065656607837733803541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42239377104405225155869027 63359065656607837733803541)
    ·
      refine ⟨2969956202653492393772041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 63359065656607837733803541 2969956202653492393772041)
      ·
        refine ⟨2227467151990119295329031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2969956202653492393772041 2227467151990119295329031)
        ·
          refine ⟨3341200727985178942993547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2227467151990119295329031 3341200727985178942993547)
          ·
            refine ⟨5011801091977768414490321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3341200727985178942993547 5011801091977768414490321)
            ·
              refine ⟨3758850818983326310867741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5011801091977768414490321 3758850818983326310867741)
              ·
                refine ⟨1409569057118747366575403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3758850818983326310867741 1409569057118747366575403)
                ·
                  refine ⟨2114353585678121049863105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1409569057118747366575403 2114353585678121049863105)
                  ·
                    refine ⟨1585765189258590787397329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2114353585678121049863105 1585765189258590787397329)
                    ·
                      refine ⟨1189323891943943090547997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1585765189258590787397329 1189323891943943090547997)
                      ·
                        rfl

theorem cell23_2316200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 2, 3, 1, 2, 2].length) (baseStart_2316200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2316200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2316200 prefixEnd_2316200 := by exact prefixLift 2316200
  have htrace : WordTrace (prefixWord ++ tailWord_2316200) baseStart_2316200 baseEnd_2316200 := by
    simpa [prefixWord, tailWord_2316200, baseEnd_2316200] using wordTrace_append hprefix tailTrace_2316200
  have hstable : (prefixWord ++ tailWord_2316200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2316200).length < 2 ^ (prefixWord ++ tailWord_2316200).sum := by decide
  have hdescent : baseEnd_2316200 < baseStart_2316200 := by decide
  rcases family_descends (prefixWord ++ tailWord_2316200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2316209 : List Nat := [1, 2, 2, 4, 2, 2, 1, 3, 1, 3, 2]
def baseStart_2316209 : Nat := 118140960795 + 2316209 * 2 ^ 59
def prefixEnd_2316209 : Nat := 4983230072969 + 3 ^ 40 * 2316209 * 2
def baseEnd_2316209 : Nat := 1189328513269833555335455

theorem tailTrace_2316209 : CollatzResearch.WordTrace tailWord_2316209 prefixEnd_2316209 1189328513269833555335455 := by
  unfold tailWord_2316209
  simp only [CollatzResearch.WordTrace]
  refine ⟨84479082465777844848815681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56319388310518563232543787 84479082465777844848815681)
  ·
    refine ⟨63359311849333383636611761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84479082465777844848815681 63359311849333383636611761)
    ·
      refine ⟨47519483887000037727458821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63359311849333383636611761 47519483887000037727458821)
      ·
        refine ⟨8909903228812507073898529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47519483887000037727458821 8909903228812507073898529)
        ·
          refine ⟨6682427421609380305423897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8909903228812507073898529 6682427421609380305423897)
          ·
            refine ⟨5011820566207035229067923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6682427421609380305423897 5011820566207035229067923)
            ·
              refine ⟨7517730849310552843601885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5011820566207035229067923 7517730849310552843601885)
              ·
                refine ⟨2819149068491457316350707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7517730849310552843601885 2819149068491457316350707)
                ·
                  refine ⟨4228723602737185974526061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2819149068491457316350707 4228723602737185974526061)
                  ·
                    refine ⟨1585771351026444740447273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4228723602737185974526061 1585771351026444740447273)
                    ·
                      refine ⟨1189328513269833555335455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1585771351026444740447273 1189328513269833555335455)
                      ·
                        rfl

theorem cell23_2316209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 1, 3, 1, 3, 2].length) (baseStart_2316209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2316209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2316209 prefixEnd_2316209 := by exact prefixLift 2316209
  have htrace : WordTrace (prefixWord ++ tailWord_2316209) baseStart_2316209 baseEnd_2316209 := by
    simpa [prefixWord, tailWord_2316209, baseEnd_2316209] using wordTrace_append hprefix tailTrace_2316209
  have hstable : (prefixWord ++ tailWord_2316209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2316209).length < 2 ^ (prefixWord ++ tailWord_2316209).sum := by decide
  have hdescent : baseEnd_2316209 < baseStart_2316209 := by decide
  rcases family_descends (prefixWord ++ tailWord_2316209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2316245 : List Nat := [1, 3, 2, 3, 2, 1, 2, 2, 7]
def baseStart_2316245 : Nat := 118140960795 + 2316245 * 2 ^ 59
def prefixEnd_2316245 : Nat := 4983230072969 + 3 ^ 40 * 2316245 * 2
def baseEnd_2316245 : Nat := 132149666508155046053921

theorem tailTrace_2316245 : CollatzResearch.WordTrace tailWord_2316245 prefixEnd_2316245 132149666508155046053921 := by
  unfold tailWord_2316245
  simp only [CollatzResearch.WordTrace]
  refine ⟨84480395493647422997126189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56320263662431615331417459 84480395493647422997126189)
  ·
    refine ⟨31680148310117783623922321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84480395493647422997126189 31680148310117783623922321)
    ·
      refine ⟨23760111232588337717941741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31680148310117783623922321 23760111232588337717941741)
      ·
        refine ⟨8910041712220626644228153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23760111232588337717941741 8910041712220626644228153)
        ·
          refine ⟨6682531284165469983171115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8910041712220626644228153 6682531284165469983171115)
          ·
            refine ⟨10023796926248204974756673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6682531284165469983171115 10023796926248204974756673)
            ·
              refine ⟨7517847694686153731067505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10023796926248204974756673 7517847694686153731067505)
              ·
                refine ⟨5638385771014615298300629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7517847694686153731067505 5638385771014615298300629)
                ·
                  refine ⟨132149666508155046053921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5638385771014615298300629 132149666508155046053921)
                  ·
                    rfl

theorem cell23_2316245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 2, 2, 7].length) (baseStart_2316245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2316245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2316245 prefixEnd_2316245 := by exact prefixLift 2316245
  have htrace : WordTrace (prefixWord ++ tailWord_2316245) baseStart_2316245 baseEnd_2316245 := by
    simpa [prefixWord, tailWord_2316245, baseEnd_2316245] using wordTrace_append hprefix tailTrace_2316245
  have hstable : (prefixWord ++ tailWord_2316245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2316245).length < 2 ^ (prefixWord ++ tailWord_2316245).sum := by decide
  have hdescent : baseEnd_2316245 < baseStart_2316245 := by decide
  rcases family_descends (prefixWord ++ tailWord_2316245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2316268 : List Nat := [2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 7]
def baseStart_2316268 : Nat := 118140960795 + 2316268 * 2 ^ 59
def prefixEnd_2316268 : Nat := 4983230072969 + 3 ^ 40 * 2316268 * 2
def baseEnd_2316268 : Nat := 1189358808628448824497683

theorem tailTrace_2316268 : CollatzResearch.WordTrace tailWord_2316268 prefixEnd_2316268 1189358808628448824497683 := by
  unfold tailWord_2316268
  simp only [CollatzResearch.WordTrace]
  refine ⟨42240617186282048962606729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56320822915042731950142305 42240617186282048962606729)
  ·
    refine ⟨31680462889711536721955047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42240617186282048962606729 31680462889711536721955047)
    ·
      refine ⟨47520694334567305082932571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31680462889711536721955047 47520694334567305082932571)
      ·
        refine ⟨71281041501850957624398857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47520694334567305082932571 71281041501850957624398857)
        ·
          refine ⟨53460781126388218218299143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71281041501850957624398857 53460781126388218218299143)
          ·
            refine ⟨80191171689582327327448715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53460781126388218218299143 80191171689582327327448715)
            ·
              refine ⟨120286757534373490991173073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80191171689582327327448715 120286757534373490991173073)
              ·
                refine ⟨90215068150780118243379805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 120286757534373490991173073 90215068150780118243379805)
                ·
                  refine ⟨33830650556542544341267427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 90215068150780118243379805 33830650556542544341267427)
                  ·
                    refine ⟨50745975834813816511901141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 33830650556542544341267427 50745975834813816511901141)
                    ·
                      refine ⟨1189358808628448824497683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 50745975834813816511901141 1189358808628448824497683)
                      ·
                        rfl

theorem cell23_2316268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 7].length) (baseStart_2316268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2316268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2316268 prefixEnd_2316268 := by exact prefixLift 2316268
  have htrace : WordTrace (prefixWord ++ tailWord_2316268) baseStart_2316268 baseEnd_2316268 := by
    simpa [prefixWord, tailWord_2316268, baseEnd_2316268] using wordTrace_append hprefix tailTrace_2316268
  have hstable : (prefixWord ++ tailWord_2316268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2316268).length < 2 ^ (prefixWord ++ tailWord_2316268).sum := by decide
  have hdescent : baseEnd_2316268 < baseStart_2316268 := by decide
  rcases family_descends (prefixWord ++ tailWord_2316268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2316288 : List Nat := [2, 1, 1, 2, 1, 1, 1, 4, 2, 8]
def baseStart_2316288 : Nat := 118140960795 + 2316288 * 2 ^ 59
def prefixEnd_2316288 : Nat := 4983230072969 + 3 ^ 40 * 2316288 * 2
def baseEnd_2316288 : Nat := 396456359413846248749197

theorem tailTrace_2316288 : CollatzResearch.WordTrace tailWord_2316288 prefixEnd_2316288 396456359413846248749197 := by
  unfold tailWord_2316288
  simp only [CollatzResearch.WordTrace]
  refine ⟨42240981916245820670470759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56321309221661094227294345 42240981916245820670470759)
  ·
    refine ⟨63361472874368731005706139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42240981916245820670470759 63361472874368731005706139)
    ·
      refine ⟨95042209311553096508559209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63361472874368731005706139 95042209311553096508559209)
      ·
        refine ⟨71281656983664822381419407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95042209311553096508559209 71281656983664822381419407)
        ·
          refine ⟨106922485475497233572129111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71281656983664822381419407 106922485475497233572129111)
          ·
            refine ⟨160383728213245850358193667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106922485475497233572129111 160383728213245850358193667)
            ·
              refine ⟨240575592319868775537290501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 160383728213245850358193667 240575592319868775537290501)
              ·
                refine ⟨45107923559975395413241969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 240575592319868775537290501 45107923559975395413241969)
                ·
                  refine ⟨33830942669981546559931477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45107923559975395413241969 33830942669981546559931477)
                  ·
                    refine ⟨396456359413846248749197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 33830942669981546559931477 396456359413846248749197)
                    ·
                      rfl

theorem cell23_2316288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 4, 2, 8].length) (baseStart_2316288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2316288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2316288 prefixEnd_2316288 := by exact prefixLift 2316288
  have htrace : WordTrace (prefixWord ++ tailWord_2316288) baseStart_2316288 baseEnd_2316288 := by
    simpa [prefixWord, tailWord_2316288, baseEnd_2316288] using wordTrace_append hprefix tailTrace_2316288
  have hstable : (prefixWord ++ tailWord_2316288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2316288).length < 2 ^ (prefixWord ++ tailWord_2316288).sum := by decide
  have hdescent : baseEnd_2316288 < baseStart_2316288 := by decide
  rcases family_descends (prefixWord ++ tailWord_2316288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2316294 : List Nat := [6, 2, 1, 2, 2, 1, 1, 2, 1, 3, 2]
def baseStart_2316294 : Nat := 118140960795 + 2316294 * 2 ^ 59
def prefixEnd_2316294 : Nat := 4983230072969 + 3 ^ 40 * 2316294 * 2
def baseEnd_2316294 : Nat := 1189372159125465722772565

theorem tailTrace_2316294 : CollatzResearch.WordTrace tailWord_2316294 prefixEnd_2316294 1189372159125465722772565 := by
  unfold tailWord_2316294
  simp only [CollatzResearch.WordTrace]
  refine ⟨2640068208452184511426873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 56321455113646602910439957 2640068208452184511426873)
  ·
    refine ⟨1980051156339138383570155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2640068208452184511426873 1980051156339138383570155)
    ·
      refine ⟨2970076734508707575355233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1980051156339138383570155 2970076734508707575355233)
      ·
        refine ⟨2227557550881530681516425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2970076734508707575355233 2227557550881530681516425)
        ·
          refine ⟨1670668163161148011137319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2227557550881530681516425 1670668163161148011137319)
          ·
            refine ⟨2506002244741722016705979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1670668163161148011137319 2506002244741722016705979)
            ·
              refine ⟨3759003367112583025058969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2506002244741722016705979 3759003367112583025058969)
              ·
                refine ⟨2819252525334437268794227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3759003367112583025058969 2819252525334437268794227)
                ·
                  refine ⟨4228878788001655903191341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2819252525334437268794227 4228878788001655903191341)
                  ·
                    refine ⟨1585829545500620963696753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4228878788001655903191341 1585829545500620963696753)
                    ·
                      refine ⟨1189372159125465722772565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1585829545500620963696753 1189372159125465722772565)
                      ·
                        rfl

theorem cell23_2316294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 1, 2, 1, 3, 2].length) (baseStart_2316294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2316294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2316294 prefixEnd_2316294 := by exact prefixLift 2316294
  have htrace : WordTrace (prefixWord ++ tailWord_2316294) baseStart_2316294 baseEnd_2316294 := by
    simpa [prefixWord, tailWord_2316294, baseEnd_2316294] using wordTrace_append hprefix tailTrace_2316294
  have hstable : (prefixWord ++ tailWord_2316294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2316294).length < 2 ^ (prefixWord ++ tailWord_2316294).sum := by decide
  have hdescent : baseEnd_2316294 < baseStart_2316294 := by decide
  rcases family_descends (prefixWord ++ tailWord_2316294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2316312 : List Nat := [2, 1, 2, 3, 2, 1, 4, 1, 2, 1, 4]
def baseStart_2316312 : Nat := 118140960795 + 2316312 * 2 ^ 59
def prefixEnd_2316312 : Nat := 4983230072969 + 3 ^ 40 * 2316312 * 2
def baseEnd_2316312 : Nat := 1189381401777246652347481

theorem tailTrace_2316312 : CollatzResearch.WordTrace tailWord_2316312 prefixEnd_2316312 1189381401777246652347481 := by
  unfold tailWord_2316312
  simp only [CollatzResearch.WordTrace]
  refine ⟨42241419592202346719907595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56321892789603128959876793 42241419592202346719907595)
  ·
    refine ⟨63362129388303520079861393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42241419592202346719907595 63362129388303520079861393)
    ·
      refine ⟨47521597041227640059896045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63362129388303520079861393 47521597041227640059896045)
      ·
        refine ⟨17820598890460365022461017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47521597041227640059896045 17820598890460365022461017)
        ·
          refine ⟨13365449167845273766845763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17820598890460365022461017 13365449167845273766845763)
          ·
            refine ⟨20048173751767910650268645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13365449167845273766845763 20048173751767910650268645)
            ·
              refine ⟨3759032578456483246925371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20048173751767910650268645 3759032578456483246925371)
              ·
                refine ⟨5638548867684724870388057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3759032578456483246925371 5638548867684724870388057)
                ·
                  refine ⟨4228911650763543652791043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5638548867684724870388057 4228911650763543652791043)
                  ·
                    refine ⟨6343367476145315479186565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4228911650763543652791043 6343367476145315479186565)
                    ·
                      refine ⟨1189381401777246652347481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6343367476145315479186565 1189381401777246652347481)
                      ·
                        rfl

theorem cell23_2316312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 4, 1, 2, 1, 4].length) (baseStart_2316312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2316312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2316312 prefixEnd_2316312 := by exact prefixLift 2316312
  have htrace : WordTrace (prefixWord ++ tailWord_2316312) baseStart_2316312 baseEnd_2316312 := by
    simpa [prefixWord, tailWord_2316312, baseEnd_2316312] using wordTrace_append hprefix tailTrace_2316312
  have hstable : (prefixWord ++ tailWord_2316312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2316312).length < 2 ^ (prefixWord ++ tailWord_2316312).sum := by decide
  have hdescent : baseEnd_2316312 < baseStart_2316312 := by decide
  rcases family_descends (prefixWord ++ tailWord_2316312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2316386 : List Nat := [3, 3, 2, 2, 2, 2, 1, 2, 6]
def baseStart_2316386 : Nat := 118140960795 + 2316386 * 2 ^ 59
def prefixEnd_2316386 : Nat := 4983230072969 + 3 ^ 40 * 2316386 * 2
def baseEnd_2316386 : Nat := 132157711038408818091349

theorem tailTrace_2316386 : CollatzResearch.WordTrace tailWord_2316386 prefixEnd_2316386 132157711038408818091349 := by
  unfold tailWord_2316386
  simp only [CollatzResearch.WordTrace]
  refine ⟨21121384546534151019502253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56323692124091069385339341 21121384546534151019502253)
  ·
    refine ⟨7920519204950306632313345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21121384546534151019502253 7920519204950306632313345)
    ·
      refine ⟨5940389403712729974235009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7920519204950306632313345 5940389403712729974235009)
      ·
        refine ⟨4455292052784547480676257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5940389403712729974235009 4455292052784547480676257)
        ·
          refine ⟨3341469039588410610507193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4455292052784547480676257 3341469039588410610507193)
          ·
            refine ⟨2506101779691307957880395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3341469039588410610507193 2506101779691307957880395)
            ·
              refine ⟨3759152669536961936820593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2506101779691307957880395 3759152669536961936820593)
              ·
                refine ⟨2819364502152721452615445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3759152669536961936820593 2819364502152721452615445)
                ·
                  refine ⟨132157711038408818091349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2819364502152721452615445 132157711038408818091349)
                  ·
                    rfl

theorem cell23_2316386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 1, 2, 6].length) (baseStart_2316386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2316386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2316386 prefixEnd_2316386 := by exact prefixLift 2316386
  have htrace : WordTrace (prefixWord ++ tailWord_2316386) baseStart_2316386 baseEnd_2316386 := by
    simpa [prefixWord, tailWord_2316386, baseEnd_2316386] using wordTrace_append hprefix tailTrace_2316386
  have hstable : (prefixWord ++ tailWord_2316386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2316386).length < 2 ^ (prefixWord ++ tailWord_2316386).sum := by decide
  have hdescent : baseEnd_2316386 < baseStart_2316386 := by decide
  rcases family_descends (prefixWord ++ tailWord_2316386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2316396 : List Nat := [2, 2, 1, 1, 3, 3, 2, 4, 1, 1, 3]
def baseStart_2316396 : Nat := 118140960795 + 2316396 * 2 ^ 59
def prefixEnd_2316396 : Nat := 4983230072969 + 3 ^ 40 * 2316396 * 2
def baseEnd_2316396 : Nat := 1189424534152224323697095

theorem tailTrace_2316396 : CollatzResearch.WordTrace tailWord_2316396 prefixEnd_2316396 1189424534152224323697095 := by
  unfold tailWord_2316396
  simp only [CollatzResearch.WordTrace]
  refine ⟨42242951458050187892936521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56323935277400250523915361 42242951458050187892936521)
  ·
    refine ⟨31682213593537640919702391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42242951458050187892936521 31682213593537640919702391)
    ·
      refine ⟨47523320390306461379553587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31682213593537640919702391 47523320390306461379553587)
      ·
        refine ⟨71284980585459692069330381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47523320390306461379553587 71284980585459692069330381)
        ·
          refine ⟨26731867719547384525998893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71284980585459692069330381 26731867719547384525998893)
          ·
            refine ⟨10024450394830269197249585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26731867719547384525998893 10024450394830269197249585)
            ·
              refine ⟨7518337796122701897937189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10024450394830269197249585 7518337796122701897937189)
              ·
                refine ⟨1409688336773006605863223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7518337796122701897937189 1409688336773006605863223)
                ·
                  refine ⟨2114532505159509908794835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1409688336773006605863223 2114532505159509908794835)
                  ·
                    refine ⟨3171798757739264863192253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2114532505159509908794835 3171798757739264863192253)
                    ·
                      refine ⟨1189424534152224323697095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3171798757739264863192253 1189424534152224323697095)
                      ·
                        rfl

theorem cell23_2316396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2, 4, 1, 1, 3].length) (baseStart_2316396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2316396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2316396 prefixEnd_2316396 := by exact prefixLift 2316396
  have htrace : WordTrace (prefixWord ++ tailWord_2316396) baseStart_2316396 baseEnd_2316396 := by
    simpa [prefixWord, tailWord_2316396, baseEnd_2316396] using wordTrace_append hprefix tailTrace_2316396
  have hstable : (prefixWord ++ tailWord_2316396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2316396).length < 2 ^ (prefixWord ++ tailWord_2316396).sum := by decide
  have hdescent : baseEnd_2316396 < baseStart_2316396 := by decide
  rcases family_descends (prefixWord ++ tailWord_2316396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2316412 : List Nat := [2, 2, 2, 1, 1, 4, 3, 1, 1, 6]
def baseStart_2316412 : Nat := 118140960795 + 2316412 * 2 ^ 59
def prefixEnd_2316412 : Nat := 4983230072969 + 3 ^ 40 * 2316412 * 2
def baseEnd_2316412 : Nat := 396477583280898753699007

theorem tailTrace_2316412 : CollatzResearch.WordTrace tailWord_2316412 prefixEnd_2316412 396477583280898753699007 := by
  unfold tailWord_2316412
  simp only [CollatzResearch.WordTrace]
  refine ⟨42243243242021205259227745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56324324322694940345636993 42243243242021205259227745)
  ·
    refine ⟨31682432431515903944420809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42243243242021205259227745 31682432431515903944420809)
    ·
      refine ⟨23761824323636927958315607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31682432431515903944420809 23761824323636927958315607)
      ·
        refine ⟨35642736485455391937473411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23761824323636927958315607 35642736485455391937473411)
        ·
          refine ⟨53464104728183087906210117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35642736485455391937473411 53464104728183087906210117)
          ·
            refine ⟨10024519636534328982414397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 53464104728183087906210117 10024519636534328982414397)
            ·
              refine ⟨3759194863700373368405399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10024519636534328982414397 3759194863700373368405399)
              ·
                refine ⟨5638792295550560052608099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3759194863700373368405399 5638792295550560052608099)
                ·
                  refine ⟨8458188443325840078912149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5638792295550560052608099 8458188443325840078912149)
                  ·
                    refine ⟨396477583280898753699007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8458188443325840078912149 396477583280898753699007)
                    ·
                      rfl

theorem cell23_2316412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 3, 1, 1, 6].length) (baseStart_2316412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2316412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2316412 prefixEnd_2316412 := by exact prefixLift 2316412
  have htrace : WordTrace (prefixWord ++ tailWord_2316412) baseStart_2316412 baseEnd_2316412 := by
    simpa [prefixWord, tailWord_2316412, baseEnd_2316412] using wordTrace_append hprefix tailTrace_2316412
  have hstable : (prefixWord ++ tailWord_2316412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2316412).length < 2 ^ (prefixWord ++ tailWord_2316412).sum := by decide
  have hdescent : baseEnd_2316412 < baseStart_2316412 := by decide
  rcases family_descends (prefixWord ++ tailWord_2316412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2316419 : List Nat := [1, 1, 1, 3, 3, 4, 2, 2, 1, 1, 4]
def baseStart_2316419 : Nat := 118140960795 + 2316419 * 2 ^ 59
def prefixEnd_2316419 : Nat := 4983230072969 + 3 ^ 40 * 2316419 * 2
def baseEnd_2316419 : Nat := 1189436344207277733709489

theorem tailTrace_2316419 : CollatzResearch.WordTrace tailWord_2316419 prefixEnd_2316419 1189436344207277733709489 := by
  unfold tailWord_2316419
  simp only [CollatzResearch.WordTrace]
  refine ⟨84486741795017050713960311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56324494530011367142640207 84486741795017050713960311)
  ·
    refine ⟨126730112692525576070940467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84486741795017050713960311 126730112692525576070940467)
    ·
      refine ⟨190095169038788364106410701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126730112692525576070940467 190095169038788364106410701)
      ·
        refine ⟨71285688389545636539904013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 190095169038788364106410701 71285688389545636539904013)
        ·
          refine ⟨26732133146079613702464005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71285688389545636539904013 26732133146079613702464005)
          ·
            refine ⟨5012274964889927569212001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26732133146079613702464005 5012274964889927569212001)
            ·
              refine ⟨3759206223667445676909001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5012274964889927569212001 3759206223667445676909001)
              ·
                refine ⟨2819404667750584257681751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3759206223667445676909001 2819404667750584257681751)
                ·
                  refine ⟨4229107001625876386522627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2819404667750584257681751 4229107001625876386522627)
                  ·
                    refine ⟨6343660502438814579783941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4229107001625876386522627 6343660502438814579783941)
                    ·
                      refine ⟨1189436344207277733709489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6343660502438814579783941 1189436344207277733709489)
                      ·
                        rfl

theorem cell23_2316419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 2, 2, 1, 1, 4].length) (baseStart_2316419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2316419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2316419 prefixEnd_2316419 := by exact prefixLift 2316419
  have htrace : WordTrace (prefixWord ++ tailWord_2316419) baseStart_2316419 baseEnd_2316419 := by
    simpa [prefixWord, tailWord_2316419, baseEnd_2316419] using wordTrace_append hprefix tailTrace_2316419
  have hstable : (prefixWord ++ tailWord_2316419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2316419).length < 2 ^ (prefixWord ++ tailWord_2316419).sum := by decide
  have hdescent : baseEnd_2316419 < baseStart_2316419 := by decide
  rcases family_descends (prefixWord ++ tailWord_2316419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2316425 : List Nat := [1, 2, 1, 1, 4, 2, 3, 9]
def baseStart_2316425 : Nat := 118140960795 + 2316425 * 2 ^ 59
def prefixEnd_2316425 : Nat := 4983230072969 + 3 ^ 40 * 2316425 * 2
def baseEnd_2316425 : Nat := 44053312040414989267943

theorem tailTrace_2316425 : CollatzResearch.WordTrace tailWord_2316425 prefixEnd_2316425 44053312040414989267943 := by
  unfold tailWord_2316425
  simp only [CollatzResearch.WordTrace]
  refine ⟨84486960632995313738678729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56324640421996875825785819 84486960632995313738678729)
  ·
    refine ⟨63365220474746485304009047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84486960632995313738678729 63365220474746485304009047)
    ·
      refine ⟨95047830712119727956013571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63365220474746485304009047 95047830712119727956013571)
      ·
        refine ⟨142571746068179591934020357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95047830712119727956013571 142571746068179591934020357)
        ·
          refine ⟨26732202387783673487628817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 142571746068179591934020357 26732202387783673487628817)
          ·
            refine ⟨20049151790837755115721613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26732202387783673487628817 20049151790837755115721613)
            ·
              refine ⟨7518431921564158168395605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20049151790837755115721613 7518431921564158168395605)
              ·
                refine ⟨44053312040414989267943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 7518431921564158168395605 44053312040414989267943)
                ·
                  rfl

theorem cell23_2316425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3, 9].length) (baseStart_2316425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2316425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2316425 prefixEnd_2316425 := by exact prefixLift 2316425
  have htrace : WordTrace (prefixWord ++ tailWord_2316425) baseStart_2316425 baseEnd_2316425 := by
    simpa [prefixWord, tailWord_2316425, baseEnd_2316425] using wordTrace_append hprefix tailTrace_2316425
  have hstable : (prefixWord ++ tailWord_2316425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2316425).length < 2 ^ (prefixWord ++ tailWord_2316425).sum := by decide
  have hdescent : baseEnd_2316425 < baseStart_2316425 := by decide
  rcases family_descends (prefixWord ++ tailWord_2316425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2316430 : List Nat := [4, 1, 1, 3, 3, 2, 1, 3, 1, 1, 3]
def baseStart_2316430 : Nat := 118140960795 + 2316430 * 2 ^ 59
def prefixEnd_2316430 : Nat := 4983230072969 + 3 ^ 40 * 2316430 * 2
def baseEnd_2316430 : Nat := 1189441992494477190671939

theorem tailTrace_2316430 : CollatzResearch.WordTrace tailWord_2316430 prefixEnd_2316430 1189441992494477190671939 := by
  unfold tailWord_2316430
  simp only [CollatzResearch.WordTrace]
  refine ⟨10560892874747149949076343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56324761998651466395073829 10560892874747149949076343)
  ·
    refine ⟨15841339312120724923614515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10560892874747149949076343 15841339312120724923614515)
    ·
      refine ⟨23762008968181087385421773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15841339312120724923614515 23762008968181087385421773)
      ·
        refine ⟨8910753363067907769533165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23762008968181087385421773 8910753363067907769533165)
        ·
          refine ⟨3341532511150465413574937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8910753363067907769533165 3341532511150465413574937)
          ·
            refine ⟨2506149383362849060181203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3341532511150465413574937 2506149383362849060181203)
            ·
              refine ⟨3759224075044273590271805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2506149383362849060181203 3759224075044273590271805)
              ·
                refine ⟨1409709028141602596351927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3759224075044273590271805 1409709028141602596351927)
                ·
                  refine ⟨2114563542212403894527891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1409709028141602596351927 2114563542212403894527891)
                  ·
                    refine ⟨3171845313318605841791837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2114563542212403894527891 3171845313318605841791837)
                    ·
                      refine ⟨1189441992494477190671939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3171845313318605841791837 1189441992494477190671939)
                      ·
                        rfl

theorem cell23_2316430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 1, 3, 1, 1, 3].length) (baseStart_2316430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2316430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2316430 prefixEnd_2316430 := by exact prefixLift 2316430
  have htrace : WordTrace (prefixWord ++ tailWord_2316430) baseStart_2316430 baseEnd_2316430 := by
    simpa [prefixWord, tailWord_2316430, baseEnd_2316430] using wordTrace_append hprefix tailTrace_2316430
  have hstable : (prefixWord ++ tailWord_2316430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2316430).length < 2 ^ (prefixWord ++ tailWord_2316430).sum := by decide
  have hdescent : baseEnd_2316430 < baseStart_2316430 := by decide
  rcases family_descends (prefixWord ++ tailWord_2316430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2316439 : List Nat := [1, 1, 3, 3, 4, 1, 2, 1, 1, 1, 5]
def baseStart_2316439 : Nat := 118140960795 + 2316439 * 2 ^ 59
def prefixEnd_2316439 : Nat := 4983230072969 + 3 ^ 40 * 2316439 * 2
def baseEnd_2316439 : Nat := 1189446613820367655459397

theorem tailTrace_2316439 : CollatzResearch.WordTrace tailWord_2316439 prefixEnd_2316439 1189446613820367655459397 := by
  unfold tailWord_2316439
  simp only [CollatzResearch.WordTrace]
  refine ⟨84487471254944594129688371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56324980836629729419792247 84487471254944594129688371)
  ·
    refine ⟨126731206882416891194532557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84487471254944594129688371 126731206882416891194532557)
    ·
      refine ⟨47524202580906334197949709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 126731206882416891194532557 47524202580906334197949709)
      ·
        refine ⟨17821575967839875324231141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47524202580906334197949709 17821575967839875324231141)
        ·
          refine ⟨3341545493969976623293339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17821575967839875324231141 3341545493969976623293339)
          ·
            refine ⟨5012318240954964934940009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3341545493969976623293339 5012318240954964934940009)
            ·
              refine ⟨3759238680716223701205007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5012318240954964934940009 3759238680716223701205007)
              ·
                refine ⟨5638858021074335551807511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3759238680716223701205007 5638858021074335551807511)
                ·
                  refine ⟨8458287031611503327711267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5638858021074335551807511 8458287031611503327711267)
                  ·
                    refine ⟨12687430547417254991566901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8458287031611503327711267 12687430547417254991566901)
                    ·
                      refine ⟨1189446613820367655459397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12687430547417254991566901 1189446613820367655459397)
                      ·
                        rfl

theorem cell23_2316439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 2, 1, 1, 1, 5].length) (baseStart_2316439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2316439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2316439 prefixEnd_2316439 := by exact prefixLift 2316439
  have htrace : WordTrace (prefixWord ++ tailWord_2316439) baseStart_2316439 baseEnd_2316439 := by
    simpa [prefixWord, tailWord_2316439, baseEnd_2316439] using wordTrace_append hprefix tailTrace_2316439
  have hstable : (prefixWord ++ tailWord_2316439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2316439).length < 2 ^ (prefixWord ++ tailWord_2316439).sum := by decide
  have hdescent : baseEnd_2316439 < baseStart_2316439 := by decide
  rcases family_descends (prefixWord ++ tailWord_2316439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2316509 : List Nat := [1, 4, 3, 2, 1, 1, 1, 1, 2, 3, 4]
def baseStart_2316509 : Nat := 118140960795 + 2316509 * 2 ^ 59
def prefixEnd_2316509 : Nat := 4983230072969 + 3 ^ 40 * 2316509 * 2
def baseEnd_2316509 : Nat := 1189482557466182381584075

theorem tailTrace_2316509 : CollatzResearch.WordTrace tailWord_2316509 prefixEnd_2316509 1189482557466182381584075 := by
  unfold tailWord_2316509
  simp only [CollatzResearch.WordTrace]
  refine ⟨84490024364690996084736581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56326682909793997389824387 84490024364690996084736581)
  ·
    refine ⟨15841879568379561765888109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 84490024364690996084736581 15841879568379561765888109)
    ·
      refine ⟨5940704838142335662208041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15841879568379561765888109 5940704838142335662208041)
      ·
        refine ⟨4455528628606751746656031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5940704838142335662208041 4455528628606751746656031)
        ·
          refine ⟨6683292942910127619984047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4455528628606751746656031 6683292942910127619984047)
          ·
            refine ⟨10024939414365191429976071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6683292942910127619984047 10024939414365191429976071)
            ·
              refine ⟨15037409121547787144964107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10024939414365191429976071 15037409121547787144964107)
              ·
                refine ⟨22556113682321680717446161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15037409121547787144964107 22556113682321680717446161)
                ·
                  refine ⟨16917085261741260538084621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22556113682321680717446161 16917085261741260538084621)
                  ·
                    refine ⟨6343906973152972701781733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16917085261741260538084621 6343906973152972701781733)
                    ·
                      refine ⟨1189482557466182381584075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6343906973152972701781733 1189482557466182381584075)
                      ·
                        rfl

theorem cell23_2316509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_2316509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2316509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2316509 prefixEnd_2316509 := by exact prefixLift 2316509
  have htrace : WordTrace (prefixWord ++ tailWord_2316509) baseStart_2316509 baseEnd_2316509 := by
    simpa [prefixWord, tailWord_2316509, baseEnd_2316509] using wordTrace_append hprefix tailTrace_2316509
  have hstable : (prefixWord ++ tailWord_2316509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2316509).length < 2 ^ (prefixWord ++ tailWord_2316509).sum := by decide
  have hdescent : baseEnd_2316509 < baseStart_2316509 := by decide
  rcases family_descends (prefixWord ++ tailWord_2316509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2316512 : List Nat := [2, 1, 1, 3, 1, 3, 1, 1, 1, 6, 3]
def baseStart_2316512 : Nat := 118140960795 + 2316512 * 2 ^ 59
def prefixEnd_2316512 : Nat := 4983230072969 + 3 ^ 40 * 2316512 * 2
def baseEnd_2316512 : Nat := 1189484097908145869846561

theorem tailTrace_2316512 : CollatzResearch.WordTrace tailWord_2316512 prefixEnd_2316512 1189484097908145869846561 := by
  unfold tailWord_2316512
  simp only [CollatzResearch.WordTrace]
  refine ⟨42245066891840063798547895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56326755855786751731397193 42245066891840063798547895)
  ·
    refine ⟨63367600337760095697821843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42245066891840063798547895 63367600337760095697821843)
    ·
      refine ⟨95051400506640143546732765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63367600337760095697821843 95051400506640143546732765)
      ·
        refine ⟨35644275189990053830024787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95051400506640143546732765 35644275189990053830024787)
        ·
          refine ⟨53466412784985080745037181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35644275189990053830024787 53466412784985080745037181)
          ·
            refine ⟨20049904794369405279388943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53466412784985080745037181 20049904794369405279388943)
            ·
              refine ⟨30074857191554107919083415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20049904794369405279388943 30074857191554107919083415)
              ·
                refine ⟨45112285787331161878625123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30074857191554107919083415 45112285787331161878625123)
                ·
                  refine ⟨67668428680996742817937685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45112285787331161878625123 67668428680996742817937685)
                  ·
                    refine ⟨3171957594421722319590829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 67668428680996742817937685 3171957594421722319590829)
                    ·
                      refine ⟨1189484097908145869846561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3171957594421722319590829 1189484097908145869846561)
                      ·
                        rfl

theorem cell23_2316512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 1, 1, 6, 3].length) (baseStart_2316512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2316512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2316512 prefixEnd_2316512 := by exact prefixLift 2316512
  have htrace : WordTrace (prefixWord ++ tailWord_2316512) baseStart_2316512 baseEnd_2316512 := by
    simpa [prefixWord, tailWord_2316512, baseEnd_2316512] using wordTrace_append hprefix tailTrace_2316512
  have hstable : (prefixWord ++ tailWord_2316512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2316512).length < 2 ^ (prefixWord ++ tailWord_2316512).sum := by decide
  have hdescent : baseEnd_2316512 < baseStart_2316512 := by decide
  rcases family_descends (prefixWord ++ tailWord_2316512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2316519 : List Nat := [1, 1, 5, 3, 1, 2, 1, 1, 2, 6]
def baseStart_2316519 : Nat := 118140960795 + 2316519 * 2 ^ 59
def prefixEnd_2316519 : Nat := 4983230072969 + 3 ^ 40 * 2316519 * 2
def baseEnd_2316519 : Nat := 396495897424242447486343

theorem tailTrace_2316519 : CollatzResearch.WordTrace tailWord_2316519 prefixEnd_2316519 396495897424242447486343 := by
  unfold tailWord_2316519
  simp only [CollatzResearch.WordTrace]
  refine ⟨84490389094654767792600611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56326926063103178528400407 84490389094654767792600611)
  ·
    refine ⟨126735583641982151688900917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84490389094654767792600611 126735583641982151688900917)
    ·
      refine ⟨11881460966435826720834461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 126735583641982151688900917 11881460966435826720834461)
      ·
        refine ⟨4455547862413435020312923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11881460966435826720834461 4455547862413435020312923)
        ·
          refine ⟨6683321793620152530469385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4455547862413435020312923 6683321793620152530469385)
          ·
            refine ⟨5012491345215114397852039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6683321793620152530469385 5012491345215114397852039)
            ·
              refine ⟨7518737017822671596778059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5012491345215114397852039 7518737017822671596778059)
              ·
                refine ⟨11278105526734007395167089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7518737017822671596778059 11278105526734007395167089)
                ·
                  refine ⟨8458579145050505546375317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11278105526734007395167089 8458579145050505546375317)
                  ·
                    refine ⟨396495897424242447486343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8458579145050505546375317 396495897424242447486343)
                    ·
                      rfl

theorem cell23_2316519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 1, 1, 2, 6].length) (baseStart_2316519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2316519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2316519 prefixEnd_2316519 := by exact prefixLift 2316519
  have htrace : WordTrace (prefixWord ++ tailWord_2316519) baseStart_2316519 baseEnd_2316519 := by
    simpa [prefixWord, tailWord_2316519, baseEnd_2316519] using wordTrace_append hprefix tailTrace_2316519
  have hstable : (prefixWord ++ tailWord_2316519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2316519).length < 2 ^ (prefixWord ++ tailWord_2316519).sum := by decide
  have hdescent : baseEnd_2316519 < baseStart_2316519 := by decide
  rcases family_descends (prefixWord ++ tailWord_2316519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2316526 : List Nat := [4, 1, 2, 1, 1, 1, 1, 2, 6, 2, 2]
def baseStart_2316526 : Nat := 118140960795 + 2316526 * 2 ^ 59
def prefixEnd_2316526 : Nat := 4983230072969 + 3 ^ 40 * 2316526 * 2
def baseEnd_2316526 : Nat := 1189491286637308815071497

theorem tailTrace_2316526 : CollatzResearch.WordTrace tailWord_2316526 prefixEnd_2316526 1189491286637308815071497 := by
  unfold tailWord_2316526
  simp only [CollatzResearch.WordTrace]
  refine ⟨10561330550703675998513179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56327096270419605325403621 10561330550703675998513179)
  ·
    refine ⟨15841995826055513997769769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10561330550703675998513179 15841995826055513997769769)
    ·
      refine ⟨11881496869541635498327327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15841995826055513997769769 11881496869541635498327327)
      ·
        refine ⟨17822245304312453247490991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11881496869541635498327327 17822245304312453247490991)
        ·
          refine ⟨26733367956468679871236487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17822245304312453247490991 26733367956468679871236487)
          ·
            refine ⟨40100051934703019806854731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26733367956468679871236487 40100051934703019806854731)
            ·
              refine ⟨60150077902054529710282097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40100051934703019806854731 60150077902054529710282097)
              ·
                refine ⟨45112558426540897282711573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60150077902054529710282097 45112558426540897282711573)
                ·
                  refine ⟨2114651176244104560127105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 45112558426540897282711573 2114651176244104560127105)
                  ·
                    refine ⟨1585988382183078420095329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2114651176244104560127105 1585988382183078420095329)
                    ·
                      refine ⟨1189491286637308815071497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1585988382183078420095329 1189491286637308815071497)
                      ·
                        rfl

theorem cell23_2316526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 2, 6, 2, 2].length) (baseStart_2316526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2316526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2316526 prefixEnd_2316526 := by exact prefixLift 2316526
  have htrace : WordTrace (prefixWord ++ tailWord_2316526) baseStart_2316526 baseEnd_2316526 := by
    simpa [prefixWord, tailWord_2316526, baseEnd_2316526] using wordTrace_append hprefix tailTrace_2316526
  have hstable : (prefixWord ++ tailWord_2316526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2316526).length < 2 ^ (prefixWord ++ tailWord_2316526).sum := by decide
  have hdescent : baseEnd_2316526 < baseStart_2316526 := by decide
  rcases family_descends (prefixWord ++ tailWord_2316526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2316572 : List Nat := [2, 2, 3, 1, 1, 1, 1, 3, 1, 1, 7]
def baseStart_2316572 : Nat := 118140960795 + 2316572 * 2 ^ 59
def prefixEnd_2316572 : Nat := 4983230072969 + 3 ^ 40 * 2316572 * 2
def baseEnd_2316572 : Nat := 1189514906747415635096285

theorem tailTrace_2316572 : CollatzResearch.WordTrace tailWord_2316572 prefixEnd_2316572 1189514906747415635096285 := by
  unfold tailWord_2316572
  simp only [CollatzResearch.WordTrace]
  refine ⟨42246161081731378922139985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56328214775641838562853313 42246161081731378922139985)
  ·
    refine ⟨31684620811298534191604989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42246161081731378922139985 31684620811298534191604989)
    ·
      refine ⟨11881732804236950321851871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31684620811298534191604989 11881732804236950321851871)
      ·
        refine ⟨17822599206355425482777807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11881732804236950321851871 17822599206355425482777807)
        ·
          refine ⟨26733898809533138224166711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17822599206355425482777807 26733898809533138224166711)
          ·
            refine ⟨40100848214299707336250067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26733898809533138224166711 40100848214299707336250067)
            ·
              refine ⟨60151272321449561004375101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40100848214299707336250067 60151272321449561004375101)
              ·
                refine ⟨22556727120543585376640663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 60151272321449561004375101 22556727120543585376640663)
                ·
                  refine ⟨33835090680815378064960995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22556727120543585376640663 33835090680815378064960995)
                  ·
                    refine ⟨50752636021223067097441493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 33835090680815378064960995 50752636021223067097441493)
                    ·
                      refine ⟨1189514906747415635096285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 50752636021223067097441493 1189514906747415635096285)
                      ·
                        rfl

theorem cell23_2316572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 3, 1, 1, 7].length) (baseStart_2316572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2316572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2316572 prefixEnd_2316572 := by exact prefixLift 2316572
  have htrace : WordTrace (prefixWord ++ tailWord_2316572) baseStart_2316572 baseEnd_2316572 := by
    simpa [prefixWord, tailWord_2316572, baseEnd_2316572] using wordTrace_append hprefix tailTrace_2316572
  have hstable : (prefixWord ++ tailWord_2316572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2316572).length < 2 ^ (prefixWord ++ tailWord_2316572).sum := by decide
  have hdescent : baseEnd_2316572 < baseStart_2316572 := by decide
  rcases family_descends (prefixWord ++ tailWord_2316572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2316599 : List Nat := [1, 1, 3, 1, 2, 1, 1, 4, 1, 6, 2]
def baseStart_2316599 : Nat := 118140960795 + 2316599 * 2 ^ 59
def prefixEnd_2316599 : Nat := 4983230072969 + 3 ^ 40 * 2316599 * 2
def baseEnd_2316599 : Nat := 1189528770725087029458661

theorem tailTrace_2316599 : CollatzResearch.WordTrace tailWord_2316599 prefixEnd_2316599 1189528770725087029458661 := by
  unfold tailWord_2316599
  simp only [CollatzResearch.WordTrace]
  refine ⟨84493306934364941455512851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56328871289576627637008567 84493306934364941455512851)
  ·
    refine ⟨126739960401547412183269277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84493306934364941455512851 126739960401547412183269277)
    ·
      refine ⟨47527485150580279568725979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 126739960401547412183269277 47527485150580279568725979)
      ·
        refine ⟨71291227725870419353088969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47527485150580279568725979 71291227725870419353088969)
        ·
          refine ⟨53468420794402814514816727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71291227725870419353088969 53468420794402814514816727)
          ·
            refine ⟨80202631191604221772225091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53468420794402814514816727 80202631191604221772225091)
            ·
              refine ⟨120303946787406332658337637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80202631191604221772225091 120303946787406332658337637)
              ·
                refine ⟨22556990022638687373438307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 120303946787406332658337637 22556990022638687373438307)
                ·
                  refine ⟨33835485033958031060157461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22556990022638687373438307 33835485033958031060157461)
                  ·
                    refine ⟨1586038360966782705944881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 33835485033958031060157461 1586038360966782705944881)
                    ·
                      refine ⟨1189528770725087029458661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1586038360966782705944881 1189528770725087029458661)
                      ·
                        rfl

theorem cell23_2316599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 4, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 4, 1, 6, 2].length) (baseStart_2316599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2316599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2316599 prefixEnd_2316599 := by exact prefixLift 2316599
  have htrace : WordTrace (prefixWord ++ tailWord_2316599) baseStart_2316599 baseEnd_2316599 := by
    simpa [prefixWord, tailWord_2316599, baseEnd_2316599] using wordTrace_append hprefix tailTrace_2316599
  have hstable : (prefixWord ++ tailWord_2316599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2316599).length < 2 ^ (prefixWord ++ tailWord_2316599).sum := by decide
  have hdescent : baseEnd_2316599 < baseStart_2316599 := by decide
  rcases family_descends (prefixWord ++ tailWord_2316599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2316626 : List Nat := [3, 2, 2, 1, 1, 1, 5, 1, 3, 4]
def baseStart_2316626 : Nat := 118140960795 + 2316626 * 2 ^ 59
def prefixEnd_2316626 : Nat := 4983230072969 + 3 ^ 40 * 2316626 * 2
def baseEnd_2316626 : Nat := 396514211567586141273679

theorem tailTrace_2316626 : CollatzResearch.WordTrace tailWord_2316626 prefixEnd_2316626 396514211567586141273679 := by
  unfold tailWord_2316626
  simp only [CollatzResearch.WordTrace]
  refine ⟨21123572926316781266686433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56329527803511416711163821 21123572926316781266686433)
  ·
    refine ⟨15842679694737585950014825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21123572926316781266686433 15842679694737585950014825)
    ·
      refine ⟨11882009771053189462511119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15842679694737585950014825 11882009771053189462511119)
      ·
        refine ⟨17823014656579784193766679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11882009771053189462511119 17823014656579784193766679)
        ·
          refine ⟨26734521984869676290650019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17823014656579784193766679 26734521984869676290650019)
          ·
            refine ⟨40101782977304514435975029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26734521984869676290650019 40101782977304514435975029)
            ·
              refine ⟨3759542154122298228372659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 40101782977304514435975029 3759542154122298228372659)
              ·
                refine ⟨5639313231183447342558989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3759542154122298228372659 5639313231183447342558989)
                ·
                  refine ⟨2114742461693792753459621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5639313231183447342558989 2114742461693792753459621)
                  ·
                    refine ⟨396514211567586141273679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2114742461693792753459621 396514211567586141273679)
                    ·
                      rfl

theorem cell23_2316626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 5, 1, 3, 4].length) (baseStart_2316626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2316626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2316626 prefixEnd_2316626 := by exact prefixLift 2316626
  have htrace : WordTrace (prefixWord ++ tailWord_2316626) baseStart_2316626 baseEnd_2316626 := by
    simpa [prefixWord, tailWord_2316626, baseEnd_2316626] using wordTrace_append hprefix tailTrace_2316626
  have hstable : (prefixWord ++ tailWord_2316626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2316626).length < 2 ^ (prefixWord ++ tailWord_2316626).sum := by decide
  have hdescent : baseEnd_2316626 < baseStart_2316626 := by decide
  rcases family_descends (prefixWord ++ tailWord_2316626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2316686 : List Nat := [4, 1, 1, 4, 1, 1, 1, 2, 3, 5]
def baseStart_2316686 : Nat := 118140960795 + 2316686 * 2 ^ 59
def prefixEnd_2316686 : Nat := 4983230072969 + 3 ^ 40 * 2316686 * 2
def baseEnd_2316686 : Nat := 396524481180676063023587

theorem tailTrace_2316686 : CollatzResearch.WordTrace tailWord_2316686 prefixEnd_2316686 396524481180676063023587 := by
  unfold tailWord_2316686
  simp only [CollatzResearch.WordTrace]
  refine ⟨10562060010631219414241239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56330986723366503542619941 10562060010631219414241239)
  ·
    refine ⟨15843090015946829121361859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10562060010631219414241239 15843090015946829121361859)
    ·
      refine ⟨23764635023920243682042789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15843090015946829121361859 23764635023920243682042789)
      ·
        refine ⟨4455869066985045690383023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23764635023920243682042789 4455869066985045690383023)
        ·
          refine ⟨6683803600477568535574535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4455869066985045690383023 6683803600477568535574535)
          ·
            refine ⟨10025705400716352803361803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6683803600477568535574535 10025705400716352803361803)
            ·
              refine ⟨15038558101074529205042705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10025705400716352803361803 15038558101074529205042705)
              ·
                refine ⟨11278918575805896903782029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15038558101074529205042705 11278918575805896903782029)
                ·
                  refine ⟨4229594465927211338918261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11278918575805896903782029 4229594465927211338918261)
                  ·
                    refine ⟨396524481180676063023587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4229594465927211338918261 396524481180676063023587)
                    ·
                      rfl

theorem cell23_2316686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 2, 3, 5].length) (baseStart_2316686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2316686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2316686 prefixEnd_2316686 := by exact prefixLift 2316686
  have htrace : WordTrace (prefixWord ++ tailWord_2316686) baseStart_2316686 baseEnd_2316686 := by
    simpa [prefixWord, tailWord_2316686, baseEnd_2316686] using wordTrace_append hprefix tailTrace_2316686
  have hstable : (prefixWord ++ tailWord_2316686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2316686).length < 2 ^ (prefixWord ++ tailWord_2316686).sum := by decide
  have hdescent : baseEnd_2316686 < baseStart_2316686 := by decide
  rcases family_descends (prefixWord ++ tailWord_2316686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2316706 : List Nat := [3, 3, 1, 2, 1, 1, 1, 3, 3, 1, 4]
def baseStart_2316706 : Nat := 118140960795 + 2316706 * 2 ^ 59
def prefixEnd_2316706 : Nat := 4983230072969 + 3 ^ 40 * 2316706 * 2
def baseEnd_2316706 : Nat := 1189583713155118110820669

theorem tailTrace_2316706 : CollatzResearch.WordTrace tailWord_2316706 prefixEnd_2316706 1189583713155118110820669 := by
  unfold tailWord_2316706
  simp only [CollatzResearch.WordTrace]
  refine ⟨21124302386244324682414493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56331473029984865819771981 21124302386244324682414493)
  ·
    refine ⟨7921613394841621755905435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21124302386244324682414493 7921613394841621755905435)
    ·
      refine ⟨11882420092262432633858153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7921613394841621755905435 11882420092262432633858153)
      ·
        refine ⟨8911815069196824475393615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11882420092262432633858153 8911815069196824475393615)
        ·
          refine ⟨13367722603795236713090423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8911815069196824475393615 13367722603795236713090423)
          ·
            refine ⟨20051583905692855069635635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13367722603795236713090423 20051583905692855069635635)
            ·
              refine ⟨30077375858539282604453453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20051583905692855069635635 30077375858539282604453453)
              ·
                refine ⟨11279015946952230976670045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30077375858539282604453453 11279015946952230976670045)
                ·
                  refine ⟨4229630980107086616251267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11279015946952230976670045 4229630980107086616251267)
                  ·
                    refine ⟨6344446470160629924376901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4229630980107086616251267 6344446470160629924376901)
                    ·
                      refine ⟨1189583713155118110820669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6344446470160629924376901 1189583713155118110820669)
                      ·
                        rfl

theorem cell23_2316706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 3, 3, 1, 4].length) (baseStart_2316706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2316706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2316706 prefixEnd_2316706 := by exact prefixLift 2316706
  have htrace : WordTrace (prefixWord ++ tailWord_2316706) baseStart_2316706 baseEnd_2316706 := by
    simpa [prefixWord, tailWord_2316706, baseEnd_2316706] using wordTrace_append hprefix tailTrace_2316706
  have hstable : (prefixWord ++ tailWord_2316706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2316706).length < 2 ^ (prefixWord ++ tailWord_2316706).sum := by decide
  have hdescent : baseEnd_2316706 < baseStart_2316706 := by decide
  rcases family_descends (prefixWord ++ tailWord_2316706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2316729 : List Nat := [1, 2, 1, 4, 3, 2, 10]
def baseStart_2316729 : Nat := 118140960795 + 2316729 * 2 ^ 59
def prefixEnd_2316729 : Nat := 4983230072969 + 3 ^ 40 * 2316729 * 2
def baseEnd_2316729 : Nat := 14686364484076191615223

theorem tailTrace_2316729 : CollatzResearch.WordTrace tailWord_2316729 prefixEnd_2316729 14686364484076191615223 := by
  unfold tailWord_2316729
  simp only [CollatzResearch.WordTrace]
  refine ⟨84498048423893973657745241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56332032282595982438496827 84498048423893973657745241)
  ·
    refine ⟨63373536317920480243308931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84498048423893973657745241 63373536317920480243308931)
    ·
      refine ⟨95060304476880720364963397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63373536317920480243308931 95060304476880720364963397)
      ·
        refine ⟨17823807089415135068430637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 95060304476880720364963397 17823807089415135068430637)
        ·
          refine ⟨6683927658530675650661489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17823807089415135068430637 6683927658530675650661489)
          ·
            refine ⟨5012945743898006737996117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6683927658530675650661489 5012945743898006737996117)
            ·
              refine ⟨14686364484076191615223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 5012945743898006737996117 14686364484076191615223)
              ·
                rfl

theorem cell23_2316729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 10].length) (baseStart_2316729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2316729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2316729 prefixEnd_2316729 := by exact prefixLift 2316729
  have htrace : WordTrace (prefixWord ++ tailWord_2316729) baseStart_2316729 baseEnd_2316729 := by
    simpa [prefixWord, tailWord_2316729, baseEnd_2316729] using wordTrace_append hprefix tailTrace_2316729
  have hstable : (prefixWord ++ tailWord_2316729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2316729).length < 2 ^ (prefixWord ++ tailWord_2316729).sum := by decide
  have hdescent : baseEnd_2316729 < baseStart_2316729 := by decide
  rcases family_descends (prefixWord ++ tailWord_2316729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2316733 : List Nat := [1, 4, 1, 2, 2, 2, 3, 2, 2, 4]
def baseStart_2316733 : Nat := 118140960795 + 2316733 * 2 ^ 59
def prefixEnd_2316733 : Nat := 4983230072969 + 3 ^ 40 * 2316733 * 2
def baseEnd_2316733 : Nat := 396532525710929835061015

theorem tailTrace_2316733 : CollatzResearch.WordTrace tailWord_2316733 prefixEnd_2316733 396532525710929835061015 := by
  unfold tailWord_2316733
  simp only [CollatzResearch.WordTrace]
  refine ⟨84498194315879482340890853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56332129543919654893927235 84498194315879482340890853)
  ·
    refine ⟨15843411434227402938917035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 84498194315879482340890853 15843411434227402938917035)
    ·
      refine ⟨23765117151341104408375553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15843411434227402938917035 23765117151341104408375553)
      ·
        refine ⟨17823837863505828306281665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23765117151341104408375553 17823837863505828306281665)
        ·
          refine ⟨13367878397629371229711249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17823837863505828306281665 13367878397629371229711249)
          ·
            refine ⟨10025908798222028422283437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13367878397629371229711249 10025908798222028422283437)
            ·
              refine ⟨3759715799333260658356289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10025908798222028422283437 3759715799333260658356289)
              ·
                refine ⟨2819786849499945493767217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3759715799333260658356289 2819786849499945493767217)
                ·
                  refine ⟨2114840137124959120325413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2819786849499945493767217 2114840137124959120325413)
                  ·
                    refine ⟨396532525710929835061015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2114840137124959120325413 396532525710929835061015)
                    ·
                      rfl

theorem cell23_2316733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 3, 2, 2, 4].length) (baseStart_2316733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2316733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2316733 prefixEnd_2316733 := by exact prefixLift 2316733
  have htrace : WordTrace (prefixWord ++ tailWord_2316733) baseStart_2316733 baseEnd_2316733 := by
    simpa [prefixWord, tailWord_2316733, baseEnd_2316733] using wordTrace_append hprefix tailTrace_2316733
  have hstable : (prefixWord ++ tailWord_2316733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2316733).length < 2 ^ (prefixWord ++ tailWord_2316733).sum := by decide
  have hdescent : baseEnd_2316733 < baseStart_2316733 := by decide
  rcases family_descends (prefixWord ++ tailWord_2316733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2316769 : List Nat := [1, 2, 3, 1, 2, 2, 1, 1, 1, 4, 5]
def baseStart_2316769 : Nat := 118140960795 + 2316769 * 2 ^ 59
def prefixEnd_2316769 : Nat := 4983230072969 + 3 ^ 40 * 2316769 * 2
def baseEnd_2316769 : Nat := 1189616062436351364332879

theorem tailTrace_2316769 : CollatzResearch.WordTrace tailWord_2316769 prefixEnd_2316769 1189616062436351364332879 := by
  unfold tailWord_2316769
  simp only [CollatzResearch.WordTrace]
  refine ⟨84499507343749060489201361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56333004895832706992800907 84499507343749060489201361)
  ·
    refine ⟨63374630507811795366901021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84499507343749060489201361 63374630507811795366901021)
    ·
      refine ⟨23765486440429423262587883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63374630507811795366901021 23765486440429423262587883)
      ·
        refine ⟨35648229660644134893881825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23765486440429423262587883 35648229660644134893881825)
        ·
          refine ⟨26736172245483101170411369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35648229660644134893881825 26736172245483101170411369)
          ·
            refine ⟨20052129184112325877808527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26736172245483101170411369 20052129184112325877808527)
            ·
              refine ⟨30078193776168488816712791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20052129184112325877808527 30078193776168488816712791)
              ·
                refine ⟨45117290664252733225069187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30078193776168488816712791 45117290664252733225069187)
                ·
                  refine ⟨67675935996379099837603781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45117290664252733225069187 67675935996379099837603781)
                  ·
                    refine ⟨12689237999321081219550709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 67675935996379099837603781 12689237999321081219550709)
                    ·
                      refine ⟨1189616062436351364332879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12689237999321081219550709 1189616062436351364332879)
                      ·
                        rfl

theorem cell23_2316769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 1, 1, 4, 5].length) (baseStart_2316769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2316769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2316769 prefixEnd_2316769 := by exact prefixLift 2316769
  have htrace : WordTrace (prefixWord ++ tailWord_2316769) baseStart_2316769 baseEnd_2316769 := by
    simpa [prefixWord, tailWord_2316769, baseEnd_2316769] using wordTrace_append hprefix tailTrace_2316769
  have hstable : (prefixWord ++ tailWord_2316769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2316769).length < 2 ^ (prefixWord ++ tailWord_2316769).sum := by decide
  have hdescent : baseEnd_2316769 < baseStart_2316769 := by decide
  rcases family_descends (prefixWord ++ tailWord_2316769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2316790 : List Nat := [5, 1, 1, 1, 2, 1, 2, 4, 2, 1, 3]
def baseStart_2316790 : Nat := 118140960795 + 2316790 * 2 ^ 59
def prefixEnd_2316790 : Nat := 4983230072969 + 3 ^ 40 * 2316790 * 2
def baseEnd_2316790 : Nat := 1189626845530095782170283

theorem tailTrace_2316790 : CollatzResearch.WordTrace tailWord_2316790 prefixEnd_2316790 1189626845530095782170283 := by
  unfold tailWord_2316790
  simp only [CollatzResearch.WordTrace]
  refine ⟨5281267079792061317232239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 56333515517781987383810549 5281267079792061317232239)
  ·
    refine ⟨7921900619688091975848359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5281267079792061317232239 7921900619688091975848359)
    ·
      refine ⟨11882850929532137963772539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7921900619688091975848359 11882850929532137963772539)
      ·
        refine ⟨17824276394298206945658809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11882850929532137963772539 17824276394298206945658809)
        ·
          refine ⟨13368207295723655209244107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17824276394298206945658809 13368207295723655209244107)
          ·
            refine ⟨20052310943585482813866161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13368207295723655209244107 20052310943585482813866161)
            ·
              refine ⟨15039233207689112110399621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20052310943585482813866161 15039233207689112110399621)
              ·
                refine ⟨2819856226441708520699929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15039233207689112110399621 2819856226441708520699929)
                ·
                  refine ⟨2114892169831281390524947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2819856226441708520699929 2114892169831281390524947)
                  ·
                    refine ⟨3172338254746922085787421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2114892169831281390524947 3172338254746922085787421)
                    ·
                      refine ⟨1189626845530095782170283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3172338254746922085787421 1189626845530095782170283)
                      ·
                        rfl

theorem cell23_2316790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 4, 2, 1, 3].length) (baseStart_2316790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2316790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2316790 prefixEnd_2316790 := by exact prefixLift 2316790
  have htrace : WordTrace (prefixWord ++ tailWord_2316790) baseStart_2316790 baseEnd_2316790 := by
    simpa [prefixWord, tailWord_2316790, baseEnd_2316790] using wordTrace_append hprefix tailTrace_2316790
  have hstable : (prefixWord ++ tailWord_2316790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2316790).length < 2 ^ (prefixWord ++ tailWord_2316790).sum := by decide
  have hdescent : baseEnd_2316790 < baseStart_2316790 := by decide
  rcases family_descends (prefixWord ++ tailWord_2316790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2316799 : List Nat := [1, 1, 2, 2, 1, 2, 3, 2, 1, 3, 5]
def baseStart_2316799 : Nat := 118140960795 + 2316799 * 2 ^ 59
def prefixEnd_2316799 : Nat := 4983230072969 + 3 ^ 40 * 2316799 * 2
def baseEnd_2316799 : Nat := 1189631466855986246957741

theorem tailTrace_2316799 : CollatzResearch.WordTrace tailWord_2316799 prefixEnd_2316799 1189631466855986246957741 := by
  unfold tailWord_2316799
  simp only [CollatzResearch.WordTrace]
  refine ⟨84500601533640375612793451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56333734355760250408528967 84500601533640375612793451)
  ·
    refine ⟨126750902300460563419190177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84500601533640375612793451 126750902300460563419190177)
    ·
      refine ⟨95063176725345422564392633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126750902300460563419190177 95063176725345422564392633)
      ·
        refine ⟨71297382544009066923294475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95063176725345422564392633 71297382544009066923294475)
        ·
          refine ⟨106946073816013600384941713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71297382544009066923294475 106946073816013600384941713)
          ·
            refine ⟨80209555362010200288706285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 106946073816013600384941713 80209555362010200288706285)
            ·
              refine ⟨30078583260753825108264857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 80209555362010200288706285 30078583260753825108264857)
              ·
                refine ⟨22558937445565368831198643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30078583260753825108264857 22558937445565368831198643)
                ·
                  refine ⟨33838406168348053246797965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22558937445565368831198643 33838406168348053246797965)
                  ·
                    refine ⟨12689402313130519967549237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 33838406168348053246797965 12689402313130519967549237)
                    ·
                      refine ⟨1189631466855986246957741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12689402313130519967549237 1189631466855986246957741)
                      ·
                        rfl

theorem cell23_2316799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 2, 1, 3, 5].length) (baseStart_2316799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2316799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2316799 prefixEnd_2316799 := by exact prefixLift 2316799
  have htrace : WordTrace (prefixWord ++ tailWord_2316799) baseStart_2316799 baseEnd_2316799 := by
    simpa [prefixWord, tailWord_2316799, baseEnd_2316799] using wordTrace_append hprefix tailTrace_2316799
  have hstable : (prefixWord ++ tailWord_2316799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2316799).length < 2 ^ (prefixWord ++ tailWord_2316799).sum := by decide
  have hdescent : baseEnd_2316799 < baseStart_2316799 := by decide
  rcases family_descends (prefixWord ++ tailWord_2316799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2316819 : List Nat := [1, 1, 1, 2, 1, 5, 2, 1, 9]
def baseStart_2316819 : Nat := 118140960795 + 2316819 * 2 ^ 59
def prefixEnd_2316819 : Nat := 4983230072969 + 3 ^ 40 * 2316819 * 2
def baseEnd_2316819 : Nat := 132182415163230685411961

theorem tailTrace_2316819 : CollatzResearch.WordTrace tailWord_2316819 prefixEnd_2316819 132182415163230685411961 := by
  unfold tailWord_2316819
  simp only [CollatzResearch.WordTrace]
  refine ⟨84501330993567919028521511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56334220662378612685681007 84501330993567919028521511)
  ·
    refine ⟨126751996490351878542782267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84501330993567919028521511 126751996490351878542782267)
    ·
      refine ⟨190127994735527817814173401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126751996490351878542782267 190127994735527817814173401)
      ·
        refine ⟨142595996051645863360630051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 190127994735527817814173401 142595996051645863360630051)
        ·
          refine ⟨213893994077468795040945077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142595996051645863360630051 213893994077468795040945077)
          ·
            refine ⟨20052561944762699535088601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 213893994077468795040945077 20052561944762699535088601)
            ·
              refine ⟨15039421458572024651316451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20052561944762699535088601 15039421458572024651316451)
              ·
                refine ⟨22559132187858036976974677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15039421458572024651316451 22559132187858036976974677)
                ·
                  refine ⟨132182415163230685411961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 22559132187858036976974677 132182415163230685411961)
                  ·
                    rfl

theorem cell23_2316819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 1, 9].length) (baseStart_2316819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2316819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2316819 prefixEnd_2316819 := by exact prefixLift 2316819
  have htrace : WordTrace (prefixWord ++ tailWord_2316819) baseStart_2316819 baseEnd_2316819 := by
    simpa [prefixWord, tailWord_2316819, baseEnd_2316819] using wordTrace_append hprefix tailTrace_2316819
  have hstable : (prefixWord ++ tailWord_2316819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2316819).length < 2 ^ (prefixWord ++ tailWord_2316819).sum := by decide
  have hdescent : baseEnd_2316819 < baseStart_2316819 := by decide
  rcases family_descends (prefixWord ++ tailWord_2316819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2316853 : List Nat := [1, 3, 3, 1, 1, 2, 3, 4, 5]
def baseStart_2316853 : Nat := 118140960795 + 2316853 * 2 ^ 59
def prefixEnd_2316853 : Nat := 4983230072969 + 3 ^ 40 * 2316853 * 2
def baseEnd_2316853 : Nat := 132184354979036559520277

theorem tailTrace_2316853 : CollatzResearch.WordTrace tailWord_2316853 prefixEnd_2316853 132184354979036559520277 := by
  unfold tailWord_2316853
  simp only [CollatzResearch.WordTrace]
  refine ⟨84502571075444742835259213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56335047383629828556839475 84502571075444742835259213)
  ·
    refine ⟨31688464153291778563222205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84502571075444742835259213 31688464153291778563222205)
    ·
      refine ⟨11883174057484416961208327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31688464153291778563222205 11883174057484416961208327)
      ·
        refine ⟨17824761086226625441812491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11883174057484416961208327 17824761086226625441812491)
        ·
          refine ⟨26737141629339938162718737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17824761086226625441812491 26737141629339938162718737)
          ·
            refine ⟨20052856222004953622039053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26737141629339938162718737 20052856222004953622039053)
            ·
              refine ⟨7519821083251857608264645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20052856222004953622039053 7519821083251857608264645)
              ·
                refine ⟨1409966453109723301549621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7519821083251857608264645 1409966453109723301549621)
                ·
                  refine ⟨132184354979036559520277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1409966453109723301549621 132184354979036559520277)
                  ·
                    rfl

theorem cell23_2316853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 3, 4, 5].length) (baseStart_2316853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2316853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2316853 prefixEnd_2316853 := by exact prefixLift 2316853
  have htrace : WordTrace (prefixWord ++ tailWord_2316853) baseStart_2316853 baseEnd_2316853 := by
    simpa [prefixWord, tailWord_2316853, baseEnd_2316853] using wordTrace_append hprefix tailTrace_2316853
  have hstable : (prefixWord ++ tailWord_2316853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2316853).length < 2 ^ (prefixWord ++ tailWord_2316853).sum := by decide
  have hdescent : baseEnd_2316853 < baseStart_2316853 := by decide
  rcases family_descends (prefixWord ++ tailWord_2316853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2316859 : List Nat := [1, 1, 1, 1, 1, 2, 1, 2, 5, 1, 7]
def baseStart_2316859 : Nat := 118140960795 + 2316859 * 2 ^ 59
def prefixEnd_2316859 : Nat := 4983230072969 + 3 ^ 40 * 2316859 * 2
def baseEnd_2316859 : Nat := 1189662275695256012207465

theorem tailTrace_2316859 : CollatzResearch.WordTrace tailWord_2316859 prefixEnd_2316859 1189662275695256012207465 := by
  unfold tailWord_2316859
  simp only [CollatzResearch.WordTrace]
  refine ⟨84502789913423005859977631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56335193275615337239985087 84502789913423005859977631)
  ·
    refine ⟨126754184870134508789966447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84502789913423005859977631 126754184870134508789966447)
    ·
      refine ⟨190131277305201763184949671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126754184870134508789966447 190131277305201763184949671)
      ·
        refine ⟨285196915957802644777424507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190131277305201763184949671 285196915957802644777424507)
        ·
          refine ⟨427795373936703967166136761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 285196915957802644777424507 427795373936703967166136761)
          ·
            refine ⟨320846530452527975374602571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 427795373936703967166136761 320846530452527975374602571)
            ·
              refine ⟨481269795678791963061903857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 320846530452527975374602571 481269795678791963061903857)
              ·
                refine ⟨360952346759093972296427893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 481269795678791963061903857 360952346759093972296427893)
                ·
                  refine ⟨33839282508665059902790115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 360952346759093972296427893 33839282508665059902790115)
                  ·
                    refine ⟨50758923762997589854185173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 33839282508665059902790115 50758923762997589854185173)
                    ·
                      refine ⟨1189662275695256012207465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 50758923762997589854185173 1189662275695256012207465)
                      ·
                        rfl

theorem cell23_2316859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 5, 1, 7].length) (baseStart_2316859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2316859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2316859 prefixEnd_2316859 := by exact prefixLift 2316859
  have htrace : WordTrace (prefixWord ++ tailWord_2316859) baseStart_2316859 baseEnd_2316859 := by
    simpa [prefixWord, tailWord_2316859, baseEnd_2316859] using wordTrace_append hprefix tailTrace_2316859
  have hstable : (prefixWord ++ tailWord_2316859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2316859).length < 2 ^ (prefixWord ++ tailWord_2316859).sum := by decide
  have hdescent : baseEnd_2316859 < baseStart_2316859 := by decide
  rcases family_descends (prefixWord ++ tailWord_2316859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2316870 : List Nat := [6, 1, 1, 1, 2, 2, 1, 2, 7]
def baseStart_2316870 : Nat := 118140960795 + 2316870 * 2 ^ 59
def prefixEnd_2316870 : Nat := 4983230072969 + 3 ^ 40 * 2316870 * 2
def baseEnd_2316870 : Nat := 132185324886939496574435

theorem tailTrace_2316870 : CollatzResearch.WordTrace tailWord_2316870 prefixEnd_2316870 132185324886939496574435 := by
  unfold tailWord_2316870
  simp only [CollatzResearch.WordTrace]
  refine ⟨2640724722386973585582127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 56335460744255436492418709 2640724722386973585582127)
  ·
    refine ⟨3961087083580460378373191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2640724722386973585582127 3961087083580460378373191)
    ·
      refine ⟨5941630625370690567559787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3961087083580460378373191 5941630625370690567559787)
      ·
        refine ⟨8912445938056035851339681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5941630625370690567559787 8912445938056035851339681)
        ·
          refine ⟨6684334453542026888504761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8912445938056035851339681 6684334453542026888504761)
          ·
            refine ⟨5013250840156520166378571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6684334453542026888504761 5013250840156520166378571)
            ·
              refine ⟨7519876260234780249567857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5013250840156520166378571 7519876260234780249567857)
              ·
                refine ⟨5639907195176085187175893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7519876260234780249567857 5639907195176085187175893)
                ·
                  refine ⟨132185324886939496574435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5639907195176085187175893 132185324886939496574435)
                  ·
                    rfl

theorem cell23_2316870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 1, 2, 7].length) (baseStart_2316870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2316870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2316870 prefixEnd_2316870 := by exact prefixLift 2316870
  have htrace : WordTrace (prefixWord ++ tailWord_2316870) baseStart_2316870 baseEnd_2316870 := by
    simpa [prefixWord, tailWord_2316870, baseEnd_2316870] using wordTrace_append hprefix tailTrace_2316870
  have hstable : (prefixWord ++ tailWord_2316870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2316870).length < 2 ^ (prefixWord ++ tailWord_2316870).sum := by decide
  have hdescent : baseEnd_2316870 < baseStart_2316870 := by decide
  rcases family_descends (prefixWord ++ tailWord_2316870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
